import CertifiedColoringFamily
import Init.Data.List.TakeDrop
import Init.Data.List.Pairwise

namespace HansonToft

theorem directedEdgesAlong_take {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (p : List (Vertex k)) :
    ∀ n, DirectedEdgesAlong d p →
      DirectedEdgesAlong d (p.take n) := by
  induction p with
  | nil =>
      intro n h
      cases n <;> trivial
  | cons u rest ih =>
      intro n h
      cases n with
      | zero => trivial
      | succ n =>
          cases rest with
          | nil =>
              cases n <;> trivial
          | cons v tail =>
              cases n with
              | zero => trivial
              | succ n =>
                  exact ⟨h.1, ih (n + 1) h.2⟩

theorem directedEdgesAlong_drop {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (p : List (Vertex k)) :
    ∀ n, DirectedEdgesAlong d p →
      DirectedEdgesAlong d (p.drop n) := by
  induction p with
  | nil =>
      intro n h
      cases n <;> trivial
  | cons u rest ih =>
      intro n h
      cases n with
      | zero => exact h
      | succ n =>
          apply ih n
          cases rest with
          | nil => trivial
          | cons v tail => exact h.2

theorem directedEdgesAlong_of_subrelation {k : Nat}
    (d e : Vertex k → Vertex k → Prop)
    (hSub : ∀ u v, e u v → d u v)
    (p : List (Vertex k)) :
    DirectedEdgesAlong e p → DirectedEdgesAlong d p := by
  induction p with
  | nil =>
      intro h
      trivial
  | cons u rest ih =>
      intro h
      cases rest with
      | nil => trivial
      | cons v tail =>
          exact ⟨hSub u v h.1, ih h.2⟩

theorem unique_directed_path_bounds_length {k : Nat}
    (hk : 0 < k)
    (d : Vertex k → Vertex k → Prop)
    (hUnique : ∃ q, FullDirectedPath k d q ∧
      ∀ r, FullDirectedPath k d r → r = q)
    (p : List (Vertex k))
    (hSimple : p.Nodup)
    (hDirected : DirectedEdgesAlong d p) :
    p.length ≤ k := by
  classical
  by_cases hBound : p.length ≤ k
  · exact hBound
  · have hLong : k + 1 ≤ p.length := by omega
    have hFirst : FullDirectedPath k d (p.take k) := by
      refine ⟨?_, List.Pairwise.take hSimple,
        directedEdgesAlong_take d p k hDirected⟩
      simp only [List.length_take]
      omega
    have hSecond :
        FullDirectedPath k d ((p.drop 1).take k) := by
      refine ⟨?_, List.Pairwise.take (List.Pairwise.drop hSimple),
        directedEdgesAlong_take d (p.drop 1) k
          (directedEdgesAlong_drop d p 1 hDirected)⟩
      simp only [List.length_take, List.length_drop]
      omega
    obtain ⟨q, hq, hOnly⟩ := hUnique
    have hEqual : p.take k = (p.drop 1).take k :=
      (hOnly _ hFirst).trans (hOnly _ hSecond).symm
    have hLookup :=
      congrArg (fun xs : List (Vertex k) => xs[0]?) hEqual
    simp only [List.getElem?_take_of_lt hk] at hLookup
    have hDrop : (p.drop 1)[0]? = p[1]? := by
      cases p <;> rfl
    rw [hDrop] at hLookup
    have hIndex :=
      hSimple.eq_of_getElem?_eq (by omega : 0 < p.length) hLookup
    omega

def IncreasingEdgesFollow {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k) : Prop :=
  ∀ u v, Adj k u v →
    (color u).val < (color v).val → d u v

theorem ranked_edges_follow_orientation {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k)
    (hFollow : IncreasingEdgesFollow d color)
    (p : List (Vertex k)) :
    ∀ s, EdgesAlong p →
      RanksFrom (fun v => (color v).val) s p →
      DirectedEdgesAlong d p := by
  induction p with
  | nil =>
      intro s hEdges hRanks
      trivial
  | cons u rest ih =>
      intro s hEdges hRanks
      cases rest with
      | nil => trivial
      | cons v tail =>
          refine ⟨hFollow u v hEdges.1 ?_,
            ih (s + 1) hEdges.2 hRanks.2⟩
          have hu : (color u).val = s := hRanks.1
          have hv : (color v).val = s + 1 := hRanks.2.1
          omega

theorem increasing_path_is_directed {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k)
    (hFollow : IncreasingEdgesFollow d color)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k color p) :
    FullDirectedPath k d p := by
  have hRanks :=
    ((fullIncreasingPath_iff_ranks color p).mp hp).2.2.2
  exact ⟨hp.1, hp.2.1,
    ranked_edges_follow_orientation d color hFollow p 0
      hp.2.2.1 hRanks⟩

theorem compatible_coloring_rules_out_unique_orientation {k : Nat}
    (hk : 4 ≤ k)
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (hFollow : IncreasingEdgesFollow d color) :
    ¬ (∃ r, FullDirectedPath k d r ∧
      ∀ q, FullDirectedPath k d q → q = r) := by
  obtain ⟨p, q, hp, hq, hDifferent⟩ :=
    certified_two_paths_family k hk color hProper
  intro ⟨r, hr, hOnly⟩
  apply hDifferent
  exact
    (hOnly p (increasing_path_is_directed d color hFollow p hp)).trans
    (hOnly q (increasing_path_is_directed d color hFollow q hq)).symm

#print axioms unique_directed_path_bounds_length
#print axioms increasing_path_is_directed
#print axioms compatible_coloring_rules_out_unique_orientation

end HansonToft
