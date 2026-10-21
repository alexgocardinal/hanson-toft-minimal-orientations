import CounterAssignment

namespace HansonToft

theorem gateProgramClause_variables_bounded
    (program : List CNFGate) :
    ∀ next, gateProgramValid next program →
      ∀ clause ∈ gateProgramClauses next program,
        ∀ lit ∈ clause, lit.1 < next + program.length := by
  induction program with
  | nil =>
      intro next hValid clause hClause
      cases hClause
  | cons gate rest ih =>
      intro next hValid clause hClause lit hLit
      change clause ∈ gateClauses next gate ++
        gateProgramClauses (next + 1) rest at hClause
      rcases List.mem_append.mp hClause with hHere | hRest
      · have hBound := gateClause_variables_bounded
          next gate hValid.1 clause hHere lit hLit
        simp only [List.length_cons]
        omega
      · have hBound := ih (next + 1) hValid.2
          clause hRest lit hLit
        simp only [List.length_cons]
        omega

theorem counterAssignment_preserves_clause {k : Nat}
    (color : Vertex k → Fin k)
    (clause : List (Nat × Bool))
    (hBelow : ∀ lit ∈ clause, lit.1 < encodingCounterStart k) :
    HoldsClause (gateExtendedAssignment color) clause ↔
      HoldsClause (counterExtendedAssignment color) clause := by
  apply holdsClause_congr_on
  intro lit hLit
  exact (counterExtendedAssignment_below
    color lit.1 (hBelow lit hLit)).symm

theorem counterExtendedAssignment_satisfies_gates
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4)) :
    ∀ clause ∈ gateProgramClauses
        (3 * registerWidth (s.val + 4))
        (reconstructEncoding (s.val + 4)).gates.toList,
      HoldsClause (counterExtendedAssignment color) clause := by
  intro clause hClause
  have hBelow :
      ∀ lit ∈ clause,
        lit.1 < encodingCounterStart (s.val + 4) := by
    intro lit hLit
    have hBound := gateProgramClause_variables_bounded
      (reconstructEncoding (s.val + 4)).gates.toList
      (3 * registerWidth (s.val + 4))
      (reconstructed_gate_programs_valid s)
      clause hClause lit hLit
    simpa [encodingCounterStart] using hBound
  exact (counterAssignment_preserves_clause color clause hBelow).mp
    (gateExtendedAssignment_satisfies_gates s color clause hClause)

theorem counterExtendedAssignment_correct {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a : Fin k) :
    (counterExtendedAssignment color (colorVariable v a.val) = true ↔
      color v = a) ∧
    (counterExtendedAssignment color (reachVariable v a.val) = true ↔
      ReachesRank color a.val v) ∧
    (counterExtendedAssignment color
        (multiplicityVariable v a.val) = true ↔
      MultipleRankPaths color a.val v) := by
  have hStart : 3 * registerWidth k ≤ encodingCounterStart k := by
    unfold encodingCounterStart
    omega
  have hBounds := register_variables_below_gate
    hk4 hk9 v a (encodingCounterStart k) hStart
  have hC := counterExtendedAssignment_below
    color (colorVariable v a.val) hBounds.1
  have hR := counterExtendedAssignment_below
    color (reachVariable v a.val) hBounds.2.1
  have hM := counterExtendedAssignment_below
    color (multiplicityVariable v a.val) hBounds.2.2
  rw [hC, hR, hM]
  exact gateExtendedAssignment_correct hk4 hk9 color v a

theorem completed_color_false {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a : Fin k)
    (hne : color v ≠ a) :
    counterExtendedAssignment color (colorVariable v a.val) = false := by
  cases hValue :
      counterExtendedAssignment color (colorVariable v a.val) with
  | false =>
      rfl
  | true =>
      have hColor :=
        (counterExtendedAssignment_correct hk4 hk9 color v a).1.mp
          hValue
      exact False.elim (hne hColor)

theorem completed_color_at_least_one {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k) (v : Vertex k) :
    HoldsClause (counterExtendedAssignment color)
      ((List.range k).map fun rank =>
        (colorVariable v rank, true)) := by
  rw [holdsClause_iff]
  refine ⟨(colorVariable v (color v).val, true), ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨(color v).val, List.mem_range.mpr (color v).isLt, rfl⟩
  · exact
      (counterExtendedAssignment_correct hk4 hk9 color v (color v)).1.mpr
        rfl

theorem completed_color_at_most_one {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a b : Fin k) (hab : a ≠ b) :
    HoldsClause (counterExtendedAssignment color)
      [(colorVariable v a.val, false),
       (colorVariable v b.val, false)] := by
  rw [holdsClause_two]
  by_cases ha : color v = a
  · right
    apply completed_color_false hk4 hk9 color v b
    intro hb
    exact hab (ha.symm.trans hb)
  · left
    exact completed_color_false hk4 hk9 color v a ha

theorem completed_coloring_edge_clause {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (u v : Vertex k) (hAdj : Adj k u v) (a : Fin k) :
    HoldsClause (counterExtendedAssignment color)
      [(colorVariable u a.val, false),
       (colorVariable v a.val, false)] := by
  rw [holdsClause_two]
  by_cases hu : color u = a
  · right
    apply completed_color_false hk4 hk9 color v a
    intro hv
    exact hProper u v hAdj (hu.trans hv.symm)
  · left
    exact completed_color_false hk4 hk9 color u a hu

theorem completed_assignment_gates_and_counter
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    (∀ clause ∈ gateProgramClauses
        (3 * registerWidth (s.val + 4))
        (reconstructEncoding (s.val + 4)).gates.toList,
      HoldsClause (counterExtendedAssignment color) clause) ∧
    encodingCounterClausesHold
      (counterExtendedAssignment color) (s.val + 4) := by
  exact ⟨counterExtendedAssignment_satisfies_gates s color,
    counterExtendedAssignment_satisfies_counter_clauses s color hUnique⟩

#print axioms counterExtendedAssignment_correct
#print axioms completed_color_at_least_one
#print axioms completed_color_at_most_one
#print axioms completed_coloring_edge_clause
#print axioms completed_assignment_gates_and_counter

end HansonToft
