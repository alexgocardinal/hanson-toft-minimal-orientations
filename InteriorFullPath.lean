import RankInsertion

namespace HansonToft

theorem full_path_insert_interior {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (color : Vertex k → Fin k)
    (ranks : Vertex k → Nat)
    (c : Fin k)
    (front rest : List (Vertex k))
    (u v : Vertex k)
    (hLength : (front ++ u :: v :: rest).length + 1 = k)
    (hEdges : EdgesAlong (front ++ u :: v :: rest))
    (hSimple : (front ++ u :: v :: rest).Nodup)
    (hKeep : ∀ w ∈ front ++ u :: v :: rest,
      ∀ i, w ≠ .clique i (removed i))
    (hRanks : RanksFrom ranks 0 (front ++ u :: v :: rest))
    (hPosition : c.val = (front ++ [u]).length)
    (hRemoved : ∀ i, color (.clique i (removed i)) = c)
    (hExpand : ∀ w ∈ front ++ u :: v :: rest,
      (color w).val = expandRank c.val (ranks w)) :
    ∃ i, FullIncreasingPath k color
      (front ++ u :: .clique i (removed i) :: v :: rest) := by
  obtain ⟨i, hNewEdges, hNewSimple⟩ :=
    simple_path_insert_middle removed front rest u v
      hEdges hSimple hKeep
  refine ⟨i, ?_⟩
  apply (fullIncreasingPath_iff_ranks color
    (front ++ u :: .clique i (removed i) :: v :: rest)).mpr
  refine ⟨?_, hNewSimple, hNewEdges, ?_⟩
  · simp only [List.length_append, List.length_cons] at hLength ⊢
    omega
  · have hOld :
        RanksFrom ranks 0 ((front ++ [u]) ++ v :: rest) := by
      simpa [List.append_assoc] using hRanks
    have hLift :
        ∀ w ∈ (front ++ [u]) ++ v :: rest,
          (color w).val = expandRank c.val (ranks w) := by
      simpa [List.append_assoc] using hExpand
    have hNew := ranksFrom_insert_missing
      ranks (fun w => (color w).val)
      (front ++ [u]) (v :: rest)
      (.clique i (removed i)) 0 c.val
      (by simpa using hPosition)
      hOld
      (congrArg Fin.val (hRemoved i))
      hLift
    simpa [List.append_assoc] using hNew

#print axioms full_path_insert_interior

end HansonToft
