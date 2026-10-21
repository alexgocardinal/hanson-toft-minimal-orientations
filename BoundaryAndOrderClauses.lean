import CompletedAssignmentChecks

namespace HansonToft

theorem bool_eq_of_true_iff (a b : Bool)
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem completed_no_multiplicity_unit {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (rank : Fin k)
    (hNo : ¬ MultipleRankPaths color rank.val v) :
    HoldsClause (counterExtendedAssignment color)
      [(multiplicityVariable v rank.val, false)] := by
  rw [holdsClause_one]
  cases hValue : counterExtendedAssignment color
      (multiplicityVariable v rank.val) with
  | false =>
      rfl
  | true =>
      exact False.elim
        (hNo ((counterExtendedAssignment_correct
          hk4 hk9 color v rank).2.2.mp hValue))

theorem completed_rank_zero_clauses {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k) (v : Vertex k) :
    HoldsClause (counterExtendedAssignment color)
      [(reachVariable v 0, false), (colorVariable v 0, true)] ∧
    HoldsClause (counterExtendedAssignment color)
      [(colorVariable v 0, false), (reachVariable v 0, true)] ∧
    HoldsClause (counterExtendedAssignment color)
      [(multiplicityVariable v 0, false)] := by
  let zero : Fin k := ⟨0, by omega⟩
  have hCorrect :=
    counterExtendedAssignment_correct hk4 hk9 color v zero
  have hZero : (color v).val = 0 ↔ color v = zero := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      have hValues := congrArg Fin.val h
      exact hValues
  have hEqual :
      counterExtendedAssignment color (reachVariable v 0) =
        counterExtendedAssignment color (colorVariable v 0) :=
    bool_eq_of_true_iff _ _
      (hCorrect.2.1.trans
        ((reachesRank_zero color v).trans
          (hZero.trans hCorrect.1.symm)))
  have hCopy := (equivalence_gate_semantics
    (counterExtendedAssignment color)
    (reachVariable v 0) (colorVariable v 0)).mpr hEqual
  exact ⟨hCopy.1, hCopy.2,
    completed_no_multiplicity_unit hk4 hk9 color v zero
      (no_multiple_rank_zero color v)⟩

theorem completed_final_reachability_clause
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    HoldsClause (counterExtendedAssignment color)
      ((List.range (7 * ((s.val + 4) - 2))).map fun j =>
        (encodingR (s.val + 4) j ((s.val + 4) - 1), true)) := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega
  obtain ⟨p, hp, hOnly⟩ := hUnique
  obtain ⟨v, hReach⟩ :=
    full_path_gives_final_reachability (by omega) color p hp
  let rank : Fin (s.val + 4) :=
    ⟨(s.val + 4) - 1, by omega⟩
  have hNumber := (finite_numbering_correct s).1 v
  rw [holdsClause_iff]
  refine ⟨(encodingR (s.val + 4) (vertexNumber v)
    ((s.val + 4) - 1), true), ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨vertexNumber v, List.mem_range.mpr hNumber, rfl⟩
  · rw [encodingR_of_vertexNumber v (vertexNumber v)
      ((s.val + 4) - 1) rfl]
    exact (counterExtendedAssignment_correct
      hk4 hk9 color v rank).2.1.mpr hReach

theorem encodingM_of_vertexNumber {k : Nat}
    (v : Vertex k) (j rank : Nat)
    (hNumber : vertexNumber v = j) :
    encodingM k j rank = multiplicityVariable v rank := by
  change registerWidth k + registerWidth k + (j * k + rank) =
    registerWidth k + registerWidth k +
      (vertexNumber v * k + rank)
  rw [hNumber]

theorem completed_final_multiplicity_clauses
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    ∀ j, j < 7 * ((s.val + 4) - 2) →
      HoldsClause (counterExtendedAssignment color)
        [(encodingM (s.val + 4) j ((s.val + 4) - 1), false)] := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega
  intro j hj
  obtain ⟨v, hv⟩ := finite_numbering_surjective s ⟨j, hj⟩
  let rank : Fin (s.val + 4) :=
    ⟨(s.val + 4) - 1, by omega⟩
  rw [encodingM_of_vertexNumber v j ((s.val + 4) - 1) hv]
  exact completed_no_multiplicity_unit hk4 hk9 color v rank
    (unique_full_path_forbids_multiplicity
      (by omega) color hUnique v)

theorem completed_forbidden_color_pair {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (u v : Vertex k) (a b : Fin k)
    (hForbidden : color u = a → color v = b → False) :
    HoldsClause (counterExtendedAssignment color)
      [(colorVariable u a.val, false),
       (colorVariable v b.val, false)] := by
  rw [holdsClause_two]
  by_cases hu : color u = a
  · right
    apply completed_color_false hk4 hk9 color v b
    exact hForbidden hu
  · left
    exact completed_color_false hk4 hk9 color u a hu

theorem completed_increasing_color_clause {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (u v : Vertex k)
    (hOrder : (color u).val < (color v).val)
    (a b : Fin k) (hBad : b.val ≤ a.val) :
    HoldsClause (counterExtendedAssignment color)
      [(colorVariable u a.val, false),
       (colorVariable v b.val, false)] := by
  apply completed_forbidden_color_pair hk4 hk9 color u v a b
  intro hu hv
  have hU := congrArg Fin.val hu
  have hV := congrArg Fin.val hv
  omega

theorem completed_minimum_color_clause {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (u v : Vertex k)
    (hOrder : (color u).val ≤ (color v).val)
    (a b : Fin k) (hBad : b.val < a.val) :
    HoldsClause (counterExtendedAssignment color)
      [(colorVariable u a.val, false),
       (colorVariable v b.val, false)] := by
  apply completed_forbidden_color_pair hk4 hk9 color u v a b
  intro hu hv
  have hU := congrArg Fin.val hu
  have hV := congrArg Fin.val hv
  omega

theorem completed_small_cycle_color_clause {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (hSmall : (color (.cycle 0)).val < (k + 1) / 2) :
    HoldsClause (counterExtendedAssignment color)
      ((List.range ((k + 1) / 2)).map fun a =>
        (colorVariable (.cycle 0 : Vertex k) a, true)) := by
  rw [holdsClause_iff]
  refine ⟨(colorVariable (.cycle 0 : Vertex k)
    (color (.cycle 0)).val, true), ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨(color (.cycle 0)).val, List.mem_range.mpr hSmall, rfl⟩
  · exact (counterExtendedAssignment_correct hk4 hk9 color
      (.cycle 0) (color (.cycle 0))).1.mpr rfl

#print axioms completed_rank_zero_clauses
#print axioms completed_final_reachability_clause
#print axioms completed_final_multiplicity_clauses
#print axioms completed_increasing_color_clause
#print axioms completed_minimum_color_clause
#print axioms completed_small_cycle_color_clause

end HansonToft
