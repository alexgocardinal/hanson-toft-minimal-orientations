import CycleRotationNormalization
import Init.Data.Fin.Lemmas
import Init.Data.List.Pairwise

namespace HansonToft

def reversePaletteColor {k : Nat}
    (color : Vertex k → Fin k) : Vertex k → Fin k :=
  fun v => Fin.rev (color v)

theorem reversePaletteColor_involution {k : Nat}
    (color : Vertex k → Fin k) :
    reversePaletteColor (reversePaletteColor color) = color := by
  funext v
  exact Fin.rev_rev (color v)

theorem reversePaletteColor_proper {k : Nat}
    (color : Vertex k → Fin k)
    (hProper : Proper k k color) :
    Proper k k (reversePaletteColor color) := by
  intro u v hAdj hEqual
  apply hProper u v hAdj
  exact Fin.rev_inj.mp hEqual

theorem edgesAlong_reverse_palette {k : Nat}
    (p : List (Vertex k)) :
    EdgesAlong p → EdgesAlong p.reverse := by
  induction p with
  | nil =>
      intro h
      trivial
  | cons v rest ih =>
      intro h
      cases rest with
      | nil =>
          trivial
      | cons w tail =>
          have hTail : EdgesAlong (w :: tail).reverse :=
            ih h.2
          have hBack : Adj k w v :=
            (adj_symmetric k v w).mp h.1
          have hAppend :=
            edgesAlong_append_vertex tail.reverse w v
              (by simpa only [List.reverse_cons] using hTail)
              hBack
          simpa only [
            List.reverse_cons, List.append_assoc,
            List.cons_append, List.nil_append
          ] using hAppend

theorem full_path_reverse_palette {k : Nat}
    (color : Vertex k → Fin k)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k color p) :
    FullIncreasingPath k (reversePaletteColor color) p.reverse := by
  have hSimple : p.reverse.Nodup := by
    change p.reverse.Pairwise (fun a b => a ≠ b)
    rw [List.pairwise_reverse]
    exact List.Pairwise.imp (fun h => Ne.symm h) hp.2.1
  refine ⟨?_, hSimple, edgesAlong_reverse_palette p hp.2.2.1, ?_⟩
  · simpa only [List.length_reverse] using hp.1
  · intro i v hv
    have hIndex :
        i.val + (Fin.rev i).val + 1 = p.length := by
      have hi := i.isLt
      have hLength := hp.1
      simp only [Fin.val_rev]
      omega
    have hLookup : p[(Fin.rev i).val]? = some v := by
      rw [← List.getElem?_reverse' hIndex]
      exact hv
    have hColor := hp.2.2.2 (Fin.rev i) v hLookup
    change Fin.rev (color v) = i
    rw [hColor, Fin.rev_rev]

theorem reverse_palette_preserves_unique {k : Nat}
    (color : Vertex k → Fin k)
    (hUnique : HasUniqueFullPath k color) :
    HasUniqueFullPath k (reversePaletteColor color) := by
  obtain ⟨p, hp, hOnly⟩ := hUnique
  refine ⟨p.reverse, full_path_reverse_palette color p hp, ?_⟩
  intro q hq
  have hBack :=
    full_path_reverse_palette (reversePaletteColor color) q hq
  have hOriginal : FullIncreasingPath k color q.reverse := by
    simpa only [reversePaletteColor_involution] using hBack
  have hEqual := hOnly q.reverse hOriginal
  have hReverse := congrArg List.reverse hEqual
  simpa only [List.reverse_reverse] using hReverse

theorem reverse_palette_preserves_two_paths {k : Nat}
    (color : Vertex k → Fin k)
    (hTwo : HasTwoFullPaths k color) :
    HasTwoFullPaths k (reversePaletteColor color) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hTwo
  refine ⟨p.reverse, q.reverse,
    full_path_reverse_palette color p hp,
    full_path_reverse_palette color q hq, ?_⟩
  intro hEqual
  apply hpq
  have hReverse := congrArg List.reverse hEqual
  simpa only [List.reverse_reverse] using hReverse

theorem palette_choice_has_low_cycle {k : Nat}
    (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (hUnique : HasUniqueFullPath k color) :
    ∃ d : Vertex k → Fin k,
      Proper k k d ∧ HasUniqueFullPath k d ∧
      ∃ i : Fin 7, (d (.cycle i)).val < (k + 1) / 2 := by
  classical
  by_cases hLow :
      ∃ i : Fin 7, (color (.cycle i)).val < (k + 1) / 2
  · exact ⟨color, hProper, hUnique, hLow⟩
  · refine ⟨reversePaletteColor color,
      reversePaletteColor_proper color hProper,
      reverse_palette_preserves_unique color hUnique, 0, ?_⟩
    have hHigh :
        ¬ (color (.cycle (0 : Fin 7))).val < (k + 1) / 2 := by
      intro h
      exact hLow ⟨0, h⟩
    have hBound := (color (.cycle (0 : Fin 7))).isLt
    change k - ((color (.cycle (0 : Fin 7))).val + 1) <
      (k + 1) / 2
    omega

theorem normalize_cycle_minimum_and_half
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hProper : Proper (s.val + 4) (s.val + 4) color)
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    ∃ d : Vertex (s.val + 4) → Fin (s.val + 4),
      Proper (s.val + 4) (s.val + 4) d ∧
      HasUniqueFullPath (s.val + 4) d ∧
      (∀ i : Fin 7,
        (d (.cycle 0)).val ≤ (d (.cycle i)).val) ∧
      (d (.cycle 0)).val < (s.val + 4 + 1) / 2 := by
  obtain ⟨d, hd, hUniqueD, i, hLow⟩ :=
    palette_choice_has_low_cycle color hProper hUnique
  obtain ⟨offset, hRotProper, hRotUnique, hMinimum⟩ :=
    rotate_to_cycle_minimum s d hd hUniqueD
  refine ⟨relabelColor (cycleRotationRelabeling s offset) d,
    hRotProper, hRotUnique, hMinimum, ?_⟩
  have hRight :
      cycleRotateVertex offset
        (cycleUnrotateVertex offset
          (.cycle i : Vertex (s.val + 4))) = .cycle i :=
    (cycleRotationRelabeling s offset).rightInverse (.cycle i)
  have hCompare := hMinimum (cycleUnrotateIndex offset i)
  change
    (d (cycleRotateVertex offset (.cycle 0))).val ≤
      (d (cycleRotateVertex offset
        (cycleUnrotateVertex offset (.cycle i)))).val at hCompare
  rw [hRight] at hCompare
  change (d (cycleRotateVertex offset (.cycle 0))).val <
    (s.val + 4 + 1) / 2
  omega

#print axioms full_path_reverse_palette
#print axioms reverse_palette_preserves_unique
#print axioms normalize_cycle_minimum_and_half

end HansonToft
