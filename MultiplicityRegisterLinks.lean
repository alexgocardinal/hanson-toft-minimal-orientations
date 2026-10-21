import ReachabilityRegisterLinks

namespace HansonToft

theorem encodingNeighborPairs_mem_iff (k v i j : Nat) :
    (i, j) ∈ encodingNeighborPairs k v ↔
      i ∈ encodingNeighbors k v ∧
      j ∈ encodingNeighbors k v ∧ i < j := by
  unfold encodingNeighborPairs
  constructor
  · intro h
    obtain ⟨a, ha, hRest⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, hEq⟩ := List.mem_map.mp hRest
    have hFirst : a = i :=
      congrArg (fun p : Nat × Nat => p.1) hEq
    have hSecond : b = j :=
      congrArg (fun p : Nat × Nat => p.2) hEq
    subst a
    subst b
    have hFilter := List.mem_filter.mp hb
    exact ⟨ha, hFilter.1, of_decide_eq_true hFilter.2⟩
  · rintro ⟨hi, hj, hLt⟩
    apply List.mem_flatMap.mpr
    refine ⟨i, hi, ?_⟩
    apply List.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨hj, ?_⟩
    simpa only [decide_eq_true_eq] using hLt

theorem numeric_neighbor_pair_exists_iff
    (s : Fin 6) (v : Vertex (s.val + 4))
    (p : Vertex (s.val + 4) → Prop) (inputs : Nat → Bool)
    (hValue : ∀ u, inputs (vertexNumber u) = true ↔ p u) :
    (∃ pair ∈ encodingNeighborPairs (s.val + 4) (vertexNumber v),
      inputs pair.1 = true ∧ inputs pair.2 = true) ↔
    ∃ u w, u ≠ w ∧ Adj (s.val + 4) u v ∧
      Adj (s.val + 4) w v ∧ p u ∧ p w := by
  constructor
  · rintro ⟨⟨i, j⟩, hPair, hiTrue, hjTrue⟩
    obtain ⟨hiMem, hjMem, hLt⟩ :=
      (encodingNeighborPairs_mem_iff
        (s.val + 4) (vertexNumber v) i j).mp hPair
    have hiBound : i < 7 * ((s.val + 4) - 2) :=
      List.mem_range.mp (List.mem_filter.mp hiMem).1
    have hjBound : j < 7 * ((s.val + 4) - 2) :=
      List.mem_range.mp (List.mem_filter.mp hjMem).1
    obtain ⟨u, hU⟩ := finite_numbering_surjective s ⟨i, hiBound⟩
    obtain ⟨w, hW⟩ := finite_numbering_surjective s ⟨j, hjBound⟩
    have huAdj : Adj (s.val + 4) u v :=
      (encodingNeighbors_vertex_iff s v u).mp
        (by simpa only [hU] using hiMem)
    have hwAdj : Adj (s.val + 4) w v :=
      (encodingNeighbors_vertex_iff s v w).mp
        (by simpa only [hW] using hjMem)
    have huP : p u :=
      (hValue u).mp (by simpa only [hU] using hiTrue)
    have hwP : p w :=
      (hValue w).mp (by simpa only [hW] using hjTrue)
    refine ⟨u, w, ?_, huAdj, hwAdj, huP, hwP⟩
    intro hEqual
    have hNumbers : i = j := by
      calc
        i = vertexNumber u := hU.symm
        _ = vertexNumber w := congrArg
          (fun z : Vertex (s.val + 4) => vertexNumber z) hEqual
        _ = j := hW
    omega
  · rintro ⟨u, w, hDifferent, huAdj, hwAdj, huP, hwP⟩
    have hNumbers : vertexNumber u ≠ vertexNumber w := by
      intro h
      exact hDifferent ((finite_numbering_correct s).2.1 u w h)
    have huMem := (encodingNeighbors_vertex_iff s v u).mpr huAdj
    have hwMem := (encodingNeighbors_vertex_iff s v w).mpr hwAdj
    have huTrue := (hValue u).mpr huP
    have hwTrue := (hValue w).mpr hwP
    by_cases hLt : vertexNumber u < vertexNumber w
    · exact ⟨(vertexNumber u, vertexNumber w),
        (encodingNeighborPairs_mem_iff
          (s.val + 4) (vertexNumber v) _ _).mpr
            ⟨huMem, hwMem, hLt⟩,
        huTrue, hwTrue⟩
    · have hGt : vertexNumber w < vertexNumber u := by omega
      exact ⟨(vertexNumber w, vertexNumber u),
        (encodingNeighborPairs_mem_iff
          (s.val + 4) (vertexNumber v) _ _).mpr
            ⟨hwMem, huMem, hGt⟩,
        hwTrue, huTrue⟩

theorem numeric_neighbor_pair_reachability
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (v : Vertex (s.val + 4)) (rank : Fin (s.val + 4)) :
    (∃ pair ∈ encodingNeighborPairs (s.val + 4) (vertexNumber v),
      counterExtendedAssignment color
        (encodingR (s.val + 4) pair.1 rank.val) = true ∧
      counterExtendedAssignment color
        (encodingR (s.val + 4) pair.2 rank.val) = true) ↔
    ∃ u w, u ≠ w ∧ Adj (s.val + 4) u v ∧
      Adj (s.val + 4) w v ∧
      ReachesRank color rank.val u ∧ ReachesRank color rank.val w := by
  exact numeric_neighbor_pair_exists_iff s v
    (fun u => ReachesRank color rank.val u)
    (fun j => counterExtendedAssignment color
      (encodingR (s.val + 4) j rank.val))
    (fun u => numeric_reach_register_truth s color u rank)

theorem exists_true_in_mapped_list {α : Type}
    (assignment : Nat → Bool) (xs : List α) (f : α → Nat) :
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

theorem exists_true_in_append
    (assignment : Nat → Bool) (xs ys : List Nat) :
    (∃ x ∈ xs ++ ys, assignment x = true) ↔
      (∃ x ∈ xs, assignment x = true) ∨
      (∃ x ∈ ys, assignment x = true) := by
  constructor
  · rintro ⟨x, hMem, hTrue⟩
    rcases List.mem_append.mp hMem with hx | hy
    · exact Or.inl ⟨x, hx, hTrue⟩
    · exact Or.inr ⟨x, hy, hTrue⟩
  · rintro (⟨x, hx, hTrue⟩ | ⟨x, hy, hTrue⟩)
    · exact ⟨x, List.mem_append.mpr (Or.inl hx), hTrue⟩
    · exact ⟨x, List.mem_append.mpr (Or.inr hy), hTrue⟩

theorem pair_gate_outputs_iff
    (assignment : Nat → Bool) (k rank : Nat)
    (pairs : List PairGateLayout)
    (hGates : ∀ p ∈ pairs,
      assignment p.output =
        (assignment (encodingR k p.left rank) &&
          assignment (encodingR k p.right rank))) :
    (∃ p ∈ pairs, assignment p.output = true) ↔
      ∃ pair ∈ pairs.map (fun p => (p.left, p.right)),
        assignment (encodingR k pair.1 rank) = true ∧
        assignment (encodingR k pair.2 rank) = true := by
  constructor
  · rintro ⟨p, hp, hTrue⟩
    rw [hGates p hp, Bool.and_eq_true] at hTrue
    exact ⟨(p.left, p.right),
      List.mem_map.mpr ⟨p, hp, rfl⟩, hTrue⟩
  · rintro ⟨pair, hPair, hBoth⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hPair
    refine ⟨p, hp, ?_⟩
    rw [hGates p hp, Bool.and_eq_true]
    exact hBoth

theorem completed_multiplicity_link_clauses
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (layout : PathGateLayout)
    (hLayout : layout ∈ pathGateLayouts (s.val + 4)) :
    HoldsClause (counterExtendedAssignment color)
      [(encodingM (s.val + 4) layout.vertex layout.rank, false),
       (layout.multiAnd, true)] ∧
    HoldsClause (counterExtendedAssignment color)
      [(layout.multiAnd, false),
       (encodingM (s.val + 4) layout.vertex layout.rank, true)] := by
  obtain ⟨hVertex, hPositive, hRank, hPairs, _, _,
      hPairGates, hMultiOr, hMultiAnd⟩ :=
    reconstructed_path_gate_layouts_valid s layout hLayout
  obtain ⟨v, hNumber⟩ :=
    finite_numbering_surjective s ⟨layout.vertex, hVertex⟩
  let current : Fin (s.val + 4) := ⟨layout.rank, hRank⟩
  let previous : Fin (s.val + 4) := ⟨layout.rank - 1, by omega⟩

  have hRegister :
      counterExtendedAssignment color
          (encodingM (s.val + 4) layout.vertex layout.rank) = true ↔
        MultipleRankPaths color layout.rank v := by
    have h := numeric_multiplicity_register_truth s color v current
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

  have hPairEquations :
      ∀ p ∈ layout.pairs,
        counterExtendedAssignment color p.output =
          (counterExtendedAssignment color
              (encodingR (s.val + 4) p.left (layout.rank - 1)) &&
            counterExtendedAssignment color
              (encodingR (s.val + 4) p.right (layout.rank - 1))) := by
    intro p hp
    exact completed_and_gate_readback s color p.output
      (encodingR (s.val + 4) p.left (layout.rank - 1))
      (encodingR (s.val + 4) p.right (layout.rank - 1))
      (hPairGates p hp)

  have hPairValues := pair_gate_outputs_iff
    (counterExtendedAssignment color) (s.val + 4)
    (layout.rank - 1) layout.pairs hPairEquations
  rw [hPairs] at hPairValues
  have hPairNeighbors :=
    numeric_neighbor_pair_reachability s color v previous
  rw [hNumber] at hPairNeighbors
  have hPairMapped := exists_true_in_mapped_list
    (counterExtendedAssignment color) layout.pairs
    (fun p => p.output)
  have hPair := hPairMapped.trans
    (hPairValues.trans hPairNeighbors)

  have hOldMapped := exists_true_in_map
    (counterExtendedAssignment color)
    (encodingNeighbors (s.val + 4) layout.vertex)
    (fun u => encodingM (s.val + 4) u (layout.rank - 1))
  have hOldNeighbors := numeric_neighbor_multiplicity s color v previous
  rw [hNumber] at hOldNeighbors
  have hInherited := hOldMapped.trans hOldNeighbors

  have hMultiRead := completed_or_gate_readback s color layout.multiOr
    (((encodingNeighbors (s.val + 4) layout.vertex).map fun u =>
      encodingM (s.val + 4) u (layout.rank - 1)) ++
      layout.pairs.map (fun p => p.output)) hMultiOr
  have hSplit := exists_true_in_append
    (counterExtendedAssignment color)
    ((encodingNeighbors (s.val + 4) layout.vertex).map fun u =>
      encodingM (s.val + 4) u (layout.rank - 1))
    (layout.pairs.map (fun p => p.output))
  have hMultiTruth := (hMultiRead.trans hSplit).trans
    (or_congr hInherited hPair)

  have hAnd := completed_and_gate_readback s color layout.multiAnd
    (encodingC (s.val + 4) layout.vertex layout.rank)
    layout.multiOr hMultiAnd
  have hAndTruth :
      counterExtendedAssignment color layout.multiAnd = true ↔
        (color v).val = layout.rank ∧
        ((∃ u, Adj (s.val + 4) u v ∧
            MultipleRankPaths color (layout.rank - 1) u) ∨
         (∃ u w, u ≠ w ∧ Adj (s.val + 4) u v ∧
            Adj (s.val + 4) w v ∧
            ReachesRank color (layout.rank - 1) u ∧
            ReachesRank color (layout.rank - 1) w)) := by
    rw [hAnd, Bool.and_eq_true, hColor, hMultiTruth]

  have hSuccessor : layout.rank - 1 + 1 = layout.rank := by omega
  have hRecurrence :
      MultipleRankPaths color layout.rank v ↔
        (color v).val = layout.rank ∧
        ((∃ u, Adj (s.val + 4) u v ∧
            MultipleRankPaths color (layout.rank - 1) u) ∨
         (∃ u w, u ≠ w ∧ Adj (s.val + 4) u v ∧
            Adj (s.val + 4) w v ∧
            ReachesRank color (layout.rank - 1) u ∧
            ReachesRank color (layout.rank - 1) w)) := by
    simpa only [hSuccessor] using
      (multipleRankPaths_successor color (layout.rank - 1) v)

  have hEqual := bool_eq_of_true_iff _ _
    ((hRegister.trans hRecurrence).trans hAndTruth.symm)
  exact (equivalence_gate_semantics (counterExtendedAssignment color)
    (encodingM (s.val + 4) layout.vertex layout.rank)
    layout.multiAnd).mpr hEqual

#print axioms numeric_neighbor_pair_reachability
#print axioms completed_multiplicity_link_clauses

end HansonToft
