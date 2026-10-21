import PathGateLayout

namespace HansonToft

theorem numeric_color_register_truth
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (v : Vertex (s.val + 4)) (rank : Fin (s.val + 4)) :
    counterExtendedAssignment color
        (encodingC (s.val + 4) (vertexNumber v) rank.val) = true ↔
      color v = rank := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega
  exact (counterExtendedAssignment_correct hk4 hk9 color v rank).1

theorem numeric_reach_register_truth
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (v : Vertex (s.val + 4)) (rank : Fin (s.val + 4)) :
    counterExtendedAssignment color
        (encodingR (s.val + 4) (vertexNumber v) rank.val) = true ↔
      ReachesRank color rank.val v := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega
  rw [encodingR_of_vertexNumber v (vertexNumber v) rank.val rfl]
  exact (counterExtendedAssignment_correct hk4 hk9 color v rank).2.1

theorem numeric_multiplicity_register_truth
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (v : Vertex (s.val + 4)) (rank : Fin (s.val + 4)) :
    counterExtendedAssignment color
        (encodingM (s.val + 4) (vertexNumber v) rank.val) = true ↔
      MultipleRankPaths color rank.val v := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega
  rw [encodingM_of_vertexNumber v (vertexNumber v) rank.val rfl]
  exact (counterExtendedAssignment_correct hk4 hk9 color v rank).2.2

theorem encodingNeighbors_vertex_iff
    (s : Fin 6) (v u : Vertex (s.val + 4)) :
    vertexNumber u ∈
        encodingNeighbors (s.val + 4) (vertexNumber v) ↔
      Adj (s.val + 4) u v := by
  have hBound := (finite_numbering_correct s).1 u
  have hMem :
      vertexNumber u ∈
          encodingNeighbors (s.val + 4) (vertexNumber v) ↔
        numericAdj (s.val + 4) (vertexNumber v) (vertexNumber u) := by
    simp only [encodingNeighbors, List.mem_filter,
      List.mem_range, decide_eq_true_eq]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hBound, h⟩
  exact hMem.trans
    (((finite_numbering_correct s).2.2 v u).trans
      (adj_symmetric (s.val + 4) u v).symm)

theorem numeric_neighbor_exists_iff
    (s : Fin 6) (v : Vertex (s.val + 4))
    (p : Vertex (s.val + 4) → Prop) (inputs : Nat → Bool)
    (hValue : ∀ u, inputs (vertexNumber u) = true ↔ p u) :
    (∃ j ∈ encodingNeighbors (s.val + 4) (vertexNumber v),
      inputs j = true) ↔
    ∃ u, Adj (s.val + 4) u v ∧ p u := by
  constructor
  · rintro ⟨j, hj, hTrue⟩
    have hBound : j < 7 * ((s.val + 4) - 2) :=
      List.mem_range.mp (List.mem_filter.mp hj).1
    obtain ⟨u, hNumber⟩ :=
      finite_numbering_surjective s ⟨j, hBound⟩
    have hNeighbor :
        vertexNumber u ∈
          encodingNeighbors (s.val + 4) (vertexNumber v) := by
      simpa only [hNumber] using hj
    have hInput : inputs (vertexNumber u) = true := by
      simpa only [hNumber] using hTrue
    exact ⟨u, (encodingNeighbors_vertex_iff s v u).mp hNeighbor,
      (hValue u).mp hInput⟩
  · rintro ⟨u, hAdj, hp⟩
    exact ⟨vertexNumber u,
      (encodingNeighbors_vertex_iff s v u).mpr hAdj,
      (hValue u).mpr hp⟩

theorem numeric_neighbor_reachability
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (v : Vertex (s.val + 4)) (rank : Fin (s.val + 4)) :
    (∃ j ∈ encodingNeighbors (s.val + 4) (vertexNumber v),
      counterExtendedAssignment color
        (encodingR (s.val + 4) j rank.val) = true) ↔
    ∃ u, Adj (s.val + 4) u v ∧ ReachesRank color rank.val u := by
  exact numeric_neighbor_exists_iff s v
    (fun u => ReachesRank color rank.val u)
    (fun j => counterExtendedAssignment color
      (encodingR (s.val + 4) j rank.val))
    (fun u => numeric_reach_register_truth s color u rank)

theorem numeric_neighbor_multiplicity
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (v : Vertex (s.val + 4)) (rank : Fin (s.val + 4)) :
    (∃ j ∈ encodingNeighbors (s.val + 4) (vertexNumber v),
      counterExtendedAssignment color
        (encodingM (s.val + 4) j rank.val) = true) ↔
    ∃ u, Adj (s.val + 4) u v ∧
      MultipleRankPaths color rank.val u := by
  exact numeric_neighbor_exists_iff s v
    (fun u => MultipleRankPaths color rank.val u)
    (fun j => counterExtendedAssignment color
      (encodingM (s.val + 4) j rank.val))
    (fun u => numeric_multiplicity_register_truth s color u rank)

theorem exists_true_in_map
    (assignment : Nat → Bool) (xs : List Nat) (f : Nat → Nat) :
    (∃ x ∈ xs.map f, assignment x = true) ↔
      ∃ j ∈ xs, assignment (f j) = true := by
  constructor
  · rintro ⟨x, hx, hTrue⟩
    obtain ⟨j, hj, hEq⟩ := List.mem_map.mp hx
    refine ⟨j, hj, ?_⟩
    rw [hEq]
    exact hTrue
  · rintro ⟨j, hj, hTrue⟩
    exact ⟨f j, List.mem_map.mpr ⟨j, hj, rfl⟩, hTrue⟩

theorem completed_reachability_link_clauses
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (layout : PathGateLayout)
    (hLayout : layout ∈ pathGateLayouts (s.val + 4)) :
    HoldsClause (counterExtendedAssignment color)
      [(encodingR (s.val + 4) layout.vertex layout.rank, false),
       (layout.reachAnd, true)] ∧
    HoldsClause (counterExtendedAssignment color)
      [(layout.reachAnd, false),
       (encodingR (s.val + 4) layout.vertex layout.rank, true)] := by
  obtain ⟨hVertex, hPositive, hRank, _, hReachOr, hReachAnd, _, _, _⟩ :=
    reconstructed_path_gate_layouts_valid s layout hLayout
  obtain ⟨v, hNumber⟩ :=
    finite_numbering_surjective s ⟨layout.vertex, hVertex⟩
  let current : Fin (s.val + 4) := ⟨layout.rank, hRank⟩
  let previous : Fin (s.val + 4) := ⟨layout.rank - 1, by omega⟩

  have hRegister :
      counterExtendedAssignment color
          (encodingR (s.val + 4) layout.vertex layout.rank) = true ↔
        ReachesRank color layout.rank v := by
    have h := numeric_reach_register_truth s color v current
    simpa only [hNumber] using h

  have hColorFin :
      counterExtendedAssignment color
          (encodingC (s.val + 4) layout.vertex layout.rank) = true ↔
        color v = current := by
    have h := numeric_color_register_truth s color v current
    simpa only [hNumber] using h
  have hColorValue :
      color v = current ↔ (color v).val = layout.rank := by
    constructor
    · intro h
      have hValues := congrArg Fin.val h
      exact hValues
    · intro h
      exact Fin.ext h
  have hColor := hColorFin.trans hColorValue

  have hOrRead := completed_or_gate_readback s color layout.reachOr
    ((encodingNeighbors (s.val + 4) layout.vertex).map fun u =>
      encodingR (s.val + 4) u (layout.rank - 1)) hReachOr
  have hMapped := exists_true_in_map (counterExtendedAssignment color)
    (encodingNeighbors (s.val + 4) layout.vertex)
    (fun u => encodingR (s.val + 4) u (layout.rank - 1))
  have hNeighbors := numeric_neighbor_reachability s color v previous
  rw [hNumber] at hNeighbors
  have hOr := (hOrRead.trans hMapped).trans hNeighbors

  have hAnd := completed_and_gate_readback s color layout.reachAnd
    (encodingC (s.val + 4) layout.vertex layout.rank)
    layout.reachOr hReachAnd
  have hAndTruth :
      counterExtendedAssignment color layout.reachAnd = true ↔
        (color v).val = layout.rank ∧
        ∃ u, Adj (s.val + 4) u v ∧
          ReachesRank color (layout.rank - 1) u := by
    rw [hAnd, Bool.and_eq_true, hColor, hOr]

  have hSuccessor : layout.rank - 1 + 1 = layout.rank := by omega
  have hRecurrence :
      ReachesRank color layout.rank v ↔
        (color v).val = layout.rank ∧
        ∃ u, Adj (s.val + 4) u v ∧
          ReachesRank color (layout.rank - 1) u := by
    simpa only [hSuccessor] using
      (reachesRank_successor color (layout.rank - 1) v)

  have hEqual := bool_eq_of_true_iff _ _
    ((hRegister.trans hRecurrence).trans hAndTruth.symm)
  exact (equivalence_gate_semantics (counterExtendedAssignment color)
    (encodingR (s.val + 4) layout.vertex layout.rank)
    layout.reachAnd).mpr hEqual

#print axioms encodingNeighbors_vertex_iff
#print axioms numeric_neighbor_multiplicity
#print axioms completed_reachability_link_clauses

end HansonToft
