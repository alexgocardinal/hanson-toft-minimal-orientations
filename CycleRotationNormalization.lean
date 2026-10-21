import RelabelingPaths

namespace HansonToft

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem normalization_minimum_witness {α : Type}
    (value : α → Nat) (xs : List α) (hNonempty : xs ≠ []) :
    ∃ x ∈ xs, ∀ y ∈ xs, value x ≤ value y := by
  revert hNonempty
  induction xs with
  | nil =>
      intro hNonempty
      exact False.elim (hNonempty rfl)
  | cons a rest ih =>
      intro hNonempty
      by_cases hRest : rest = []
      · subst rest
        refine ⟨a, by simp, ?_⟩
        intro y hy
        have hEqual := List.mem_singleton.mp hy
        subst y
        exact Nat.le_refl _
      · obtain ⟨b, hb, hMinimum⟩ := ih hRest
        by_cases hOrder : value a ≤ value b
        · refine ⟨a, by simp, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with hEqual | hTail
          · subst y
            exact Nat.le_refl _
          · exact Nat.le_trans hOrder (hMinimum y hTail)
        · refine ⟨b, List.mem_cons.mpr (Or.inr hb), ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with hEqual | hTail
          · subst y
            omega
          · exact hMinimum y hTail

def normalizationCycleIndices : List (Fin 7) :=
  [0, 1, 2, 3, 4, 5, 6]

theorem normalizationCycleIndices_complete :
    ∀ i : Fin 7, i ∈ normalizationCycleIndices := by
  decide

theorem exists_minimum_cycle_color {k : Nat}
    (color : Vertex k → Fin k) :
    ∃ i : Fin 7,
      ∀ j : Fin 7,
        (color (.cycle i)).val ≤ (color (.cycle j)).val := by
  obtain ⟨i, hi, hMinimum⟩ :=
    normalization_minimum_witness
      (fun i : Fin 7 => (color (.cycle i)).val)
      normalizationCycleIndices (by decide)
  exact ⟨i, fun j =>
    hMinimum j (normalizationCycleIndices_complete j)⟩

def cycleRotateIndex (offset i : Fin 7) : Fin 7 :=
  ⟨(i.val + offset.val) % 7, Nat.mod_lt _ (by decide)⟩

def cycleUnrotateIndex (offset i : Fin 7) : Fin 7 :=
  ⟨(i.val + 7 - offset.val) % 7, Nat.mod_lt _ (by decide)⟩

def cycleRotateVertex {k : Nat}
    (offset : Fin 7) : Vertex k → Vertex k
  | .cycle i => .cycle (cycleRotateIndex offset i)
  | .clique i a => .clique (cycleRotateIndex offset i) a

def cycleUnrotateVertex {k : Nat}
    (offset : Fin 7) : Vertex k → Vertex k
  | .cycle i => .cycle (cycleUnrotateIndex offset i)
  | .clique i a => .clique (cycleUnrotateIndex offset i) a

theorem cycleRotateIndex_zero (offset : Fin 7) :
    cycleRotateIndex offset 0 = offset := by
  apply Fin.ext
  change (0 + offset.val) % 7 = offset.val
  simpa only [Nat.zero_add] using Nat.mod_eq_of_lt offset.isLt

theorem finite_cycle_rotation_laws :
    ∀ s : Fin 6, ∀ offset : Fin 7,
      (∀ v : Vertex (s.val + 4),
        cycleUnrotateVertex offset (cycleRotateVertex offset v) = v) ∧
      (∀ v : Vertex (s.val + 4),
        cycleRotateVertex offset (cycleUnrotateVertex offset v) = v) ∧
      (∀ u v : Vertex (s.val + 4),
        Adj (s.val + 4)
          (cycleRotateVertex offset u) (cycleRotateVertex offset v) ↔
        Adj (s.val + 4) u v) := by
  decide +native

def cycleRotationRelabeling
    (s : Fin 6) (offset : Fin 7) :
    GraphRelabeling (s.val + 4) where
  toVertex := cycleRotateVertex offset
  fromVertex := cycleUnrotateVertex offset
  leftInverse := (finite_cycle_rotation_laws s offset).1
  rightInverse := (finite_cycle_rotation_laws s offset).2.1
  adj_iff := (finite_cycle_rotation_laws s offset).2.2

theorem rotate_to_cycle_minimum
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hProper : Proper (s.val + 4) (s.val + 4) color)
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    ∃ offset : Fin 7,
      Proper (s.val + 4) (s.val + 4)
        (relabelColor (cycleRotationRelabeling s offset) color) ∧
      HasUniqueFullPath (s.val + 4)
        (relabelColor (cycleRotationRelabeling s offset) color) ∧
      ∀ i : Fin 7,
        ((relabelColor (cycleRotationRelabeling s offset) color)
          (.cycle 0)).val ≤
        ((relabelColor (cycleRotationRelabeling s offset) color)
          (.cycle i)).val := by
  obtain ⟨offset, hMinimum⟩ := exists_minimum_cycle_color color
  refine ⟨offset,
    relabel_preserves_proper
      (cycleRotationRelabeling s offset) color hProper,
    relabel_preserves_unique
      (cycleRotationRelabeling s offset) color hUnique, ?_⟩
  intro i
  change (color (.cycle (cycleRotateIndex offset 0))).val ≤
    (color (.cycle (cycleRotateIndex offset i))).val
  rw [cycleRotateIndex_zero]
  exact hMinimum (cycleRotateIndex offset i)

#print axioms exists_minimum_cycle_color
#print axioms finite_cycle_rotation_laws
#print axioms rotate_to_cycle_minimum

end HansonToft
