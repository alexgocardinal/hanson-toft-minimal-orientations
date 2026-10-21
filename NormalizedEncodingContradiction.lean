import ClassifiedEncodingClauses

namespace HansonToft

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def EncodingNormalized {k : Nat}
    (color : Vertex k → Fin k) : Prop :=
  (∀ (i : Fin 7) (a b : Fin (k - 3)),
    a.val + 1 = b.val →
      (color (.clique i a)).val < (color (.clique i b)).val) ∧
  (∀ i : Fin 7,
    (color (.cycle 0)).val ≤ (color (.cycle i)).val) ∧
  (color (.cycle 0)).val < (k + 1) / 2

def AllClausesHold (assignment : Nat → Bool)
    (clauses : List (List (Nat × Bool))) : Prop :=
  ∀ clause ∈ clauses, HoldsClause assignment clause

theorem allClausesHold_append
    (assignment : Nat → Bool)
    (xs ys : List (List (Nat × Bool))) :
    AllClausesHold assignment (xs ++ ys) ↔
      AllClausesHold assignment xs ∧ AllClausesHold assignment ys := by
  constructor
  · intro h
    constructor
    · intro clause hc
      exact h clause (List.mem_append.mpr (Or.inl hc))
    · intro clause hc
      exact h clause (List.mem_append.mpr (Or.inr hc))
  · rintro ⟨hx, hy⟩ clause hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hx clause hc
    · exact hy clause hc

theorem completed_classified_clauses_hold
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hProper : Proper (s.val + 4) (s.val + 4) color)
    (hUnique : HasUniqueFullPath (s.val + 4) color)
    (hNormalized : EncodingNormalized color) :
    AllClausesHold (counterExtendedAssignment color)
      (classifiedEncodingClauses (s.val + 4)) := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega

  have hAtLeast :
      AllClausesHold (counterExtendedAssignment color)
        (encodingAtLeastClauses (s.val + 4)) := by
    intro clause hClause
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hClause
    obtain ⟨v, hNumber⟩ :=
      finite_numbering_surjective s ⟨j, List.mem_range.mp hj⟩
    have h := completed_color_at_least_one hk4 hk9 color v
    simpa only [colorVariable, encodingC, hNumber] using h

  have hAtMost :
      AllClausesHold (counterExtendedAssignment color)
        (encodingAtMostClauses (s.val + 4)) := by
    intro clause hClause
    obtain ⟨j, hj, hRest⟩ := List.mem_flatMap.mp hClause
    obtain ⟨a, ha, hRest⟩ := List.mem_flatMap.mp hRest
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hRest
    have hFilter := List.mem_filter.mp hb
    have haBound := List.mem_range.mp ha
    have hbBound := List.mem_range.mp hFilter.1
    have hLess : a < b := of_decide_eq_true hFilter.2
    obtain ⟨v, hNumber⟩ :=
      finite_numbering_surjective s ⟨j, List.mem_range.mp hj⟩
    let aa : Fin (s.val + 4) := ⟨a, haBound⟩
    let bb : Fin (s.val + 4) := ⟨b, hbBound⟩
    have hDifferent : aa ≠ bb := by
      intro hEqual
      have hValues := congrArg Fin.val hEqual
      change a = b at hValues
      omega
    have h :=
      completed_color_at_most_one hk4 hk9 color v aa bb hDifferent
    simpa only [colorVariable, encodingC, hNumber, aa, bb] using h

  have hEdges :
      AllClausesHold (counterExtendedAssignment color)
        (encodingEdgeClauses (s.val + 4)) := by
    intro clause hClause
    obtain ⟨u, hu, hRest⟩ := List.mem_flatMap.mp hClause
    obtain ⟨v, hv, hRest⟩ := List.mem_flatMap.mp hRest
    by_cases hEdge : u < v ∧ numericAdj (s.val + 4) u v
    · rw [ite_eq_left hEdge] at hRest
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hRest
      obtain ⟨uVertex, hU⟩ :=
        finite_numbering_surjective s ⟨u, List.mem_range.mp hu⟩
      obtain ⟨vVertex, hV⟩ :=
        finite_numbering_surjective s ⟨v, List.mem_range.mp hv⟩
      have hAdj : Adj (s.val + 4) uVertex vVertex :=
        ((finite_numbering_correct s).2.2 uVertex vVertex).mp
          (by simpa only [hU, hV] using hEdge.2)
      let rank : Fin (s.val + 4) := ⟨a, List.mem_range.mp ha⟩
      have h := completed_coloring_edge_clause
        hk4 hk9 color hProper uVertex vVertex hAdj rank
      simpa only [colorVariable, encodingC, hU, hV, rank] using h
    · rw [ite_eq_right hEdge] at hRest
      cases hRest

  have hCliqueOrder :
      AllClausesHold (counterExtendedAssignment color)
        (encodingCliqueOrderClauses (s.val + 4)) := by
    intro clause hClause
    obtain ⟨i, hi, hRest⟩ := List.mem_flatMap.mp hClause
    obtain ⟨offset, hOffset, hRest⟩ := List.mem_flatMap.mp hRest
    obtain ⟨a, ha, hRest⟩ := List.mem_flatMap.mp hRest
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hRest
    have hI := List.mem_range.mp hi
    have hOffsetBound := List.mem_range.mp hOffset
    have haBound := List.mem_range.mp ha
    have hbBound := List.mem_range.mp hb
    let group : Fin 7 := ⟨i, hI⟩
    let leftPos : Fin ((s.val + 4) - 3) := ⟨offset, by omega⟩
    let rightPos : Fin ((s.val + 4) - 3) := ⟨offset + 1, by omega⟩
    let aa : Fin (s.val + 4) := ⟨a, haBound⟩
    let bb : Fin (s.val + 4) := ⟨b, by omega⟩
    have hOrder := hNormalized.1 group leftPos rightPos rfl
    have hBad : bb.val ≤ aa.val := by
      change b ≤ a
      omega
    have h := completed_increasing_color_clause hk4 hk9 color
      (.clique group leftPos) (.clique group rightPos)
      hOrder aa bb hBad
    simpa only [colorVariable, vertexNumber, encodingC,
      group, leftPos, rightPos, aa, bb, Nat.add_assoc] using h

  have hCycleMin :
      AllClausesHold (counterExtendedAssignment color)
        (encodingCycleMinimumClauses (s.val + 4)) := by
    intro clause hClause
    obtain ⟨offset, hOffset, hRest⟩ := List.mem_flatMap.mp hClause
    obtain ⟨a, ha, hRest⟩ := List.mem_flatMap.mp hRest
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hRest
    have hOffsetBound := List.mem_range.mp hOffset
    have haBound := List.mem_range.mp ha
    have hbBound := List.mem_range.mp hb
    let index : Fin 7 := ⟨offset + 1, by omega⟩
    let aa : Fin (s.val + 4) := ⟨a, haBound⟩
    let bb : Fin (s.val + 4) := ⟨b, by omega⟩
    have hBad : bb.val < aa.val := by
      change b < a
      exact hbBound
    have h := completed_minimum_color_clause hk4 hk9 color
      (.cycle 0) (.cycle index) (hNormalized.2.1 index) aa bb hBad
    have hZero : (0 : Fin 7).val = 0 := rfl
    simpa only [colorVariable, vertexNumber, encodingC,
      index, aa, bb, hZero] using h

  have hInitial :
      AllClausesHold (counterExtendedAssignment color)
        (encodingInitialPathClauses (s.val + 4)) := by
    intro clause hClause
    obtain ⟨j, hj, hRest⟩ := List.mem_flatMap.mp hClause
    obtain ⟨v, hNumber⟩ :=
      finite_numbering_surjective s ⟨j, List.mem_range.mp hj⟩
    have h := completed_rank_zero_clauses hk4 hk9 color v
    simp only [colorVariable, reachVariable, multiplicityVariable,
      hNumber] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRest
    rcases hRest with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2

  have hGates :
      AllClausesHold (counterExtendedAssignment color)
        (gateProgramClauses (3 * registerWidth (s.val + 4))
          (reconstructEncoding (s.val + 4)).gates.toList) :=
    counterExtendedAssignment_satisfies_gates s color

  have hLinks :
      AllClausesHold (counterExtendedAssignment color)
        (encodingPathLinkClauses (s.val + 4)) := by
    intro clause hClause
    obtain ⟨layout, hLayout, hRest⟩ := List.mem_flatMap.mp hClause
    have hReach := completed_reachability_link_clauses
      s color layout hLayout
    have hMulti := completed_multiplicity_link_clauses
      s color layout hLayout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRest
    rcases hRest with rfl | rfl | rfl | rfl
    · exact hReach.1
    · exact hReach.2
    · exact hMulti.1
    · exact hMulti.2

  have hFinal :
      AllClausesHold (counterExtendedAssignment color)
        (encodingFinalPathClauses (s.val + 4)) := by
    intro clause hClause
    rcases List.mem_append.mp hClause with hReach | hMulti
    · have hEq := List.mem_singleton.mp hReach
      subst clause
      exact completed_final_reachability_clause s color hUnique
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hMulti
      exact completed_final_multiplicity_clauses
        s color hUnique j (List.mem_range.mp hj)

  have hCounter :
      AllClausesHold (counterExtendedAssignment color)
        (encodingCounterClauseList (s.val + 4)
          (encodingCounterStart (s.val + 4))) := by
    have hConditions :=
      counterExtendedAssignment_satisfies_counter_clauses s color hUnique
    intro clause hClause
    unfold encodingCounterClauseList at hClause
    rw [List.append_assoc] at hClause
    rcases List.mem_append.mp hClause with hFirst | hRest
    · have hEq := List.mem_singleton.mp hFirst
      subst clause
      simpa only [Nat.add_zero] using hConditions.1
    · rcases List.mem_append.mp hRest with hMiddle | hLast
      · obtain ⟨j, hj, hRest⟩ := List.mem_flatMap.mp hMiddle
        have hBound := List.mem_range.mp hj
        have hThree := hConditions.2.1 j (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hRest
        rcases hRest with rfl | rfl | rfl
        · exact hThree.1
        · exact hThree.2.1
        · exact hThree.2.2
      · have hEq := List.mem_singleton.mp hLast
        subst clause
        exact hConditions.2.2

  have hHalf :
      AllClausesHold (counterExtendedAssignment color)
        [encodingHalfClause (s.val + 4)] := by
    intro clause hClause
    have hEq := List.mem_singleton.mp hClause
    subst clause
    exact completed_small_cycle_color_clause
      hk4 hk9 color hNormalized.2.2

  simp only [classifiedEncodingClauses,
    allClausesHold_append, and_assoc]
  exact ⟨hAtLeast, hAtMost, hEdges, hCliqueOrder, hCycleMin,
    hInitial, hGates, hLinks, hFinal, hCounter, hHalf⟩

theorem normalized_coloring_has_no_unique_path
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hProper : Proper (s.val + 4) (s.val + 4) color)
    (hNormalized : EncodingNormalized color) :
    ¬ HasUniqueFullPath (s.val + 4) color := by
  intro hUnique
  have hAll := completed_classified_clauses_hold
    s color hProper hUnique hNormalized
  exact reconstructed_encoding_has_no_assignment
    s (counterExtendedAssignment color)
    (fun clause hMem =>
      hAll clause ((classified_encoding_membership s clause).mp hMem))

#print axioms completed_classified_clauses_hold
#print axioms normalized_coloring_has_no_unique_path

end HansonToft
