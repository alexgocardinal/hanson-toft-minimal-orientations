import PathInsertion

namespace HansonToft

theorem edgesAlong_tail {k : Nat} (u : Vertex k)
    (rest : List (Vertex k)) (h : EdgesAlong (u :: rest)) :
    EdgesAlong rest := by
  cases rest with
  | nil => trivial
  | cons v rest => exact h.2

theorem edgesAlong_drop_prefix {k : Nat}
    (front rest : List (Vertex k))
    (h : EdgesAlong (front ++ rest)) :
    EdgesAlong rest := by
  revert h
  induction front with
  | nil =>
      intro h
      exact h
  | cons u front ih =>
      intro h
      exact ih (edgesAlong_tail u (front ++ rest) h)

theorem simple_path_insert_middle {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (front rest : List (Vertex k)) (u v : Vertex k)
    (hEdges : EdgesAlong (front ++ u :: v :: rest))
    (hSimple : (front ++ u :: v :: rest).Nodup)
    (hKeep : ∀ w ∈ front ++ u :: v :: rest,
      ∀ i, w ≠ .clique i (removed i)) :
    ∃ i,
      EdgesAlong (front ++ u :: .clique i (removed i) :: v :: rest) ∧
      (front ++ u :: .clique i (removed i) :: v :: rest).Nodup := by
  have huMem : u ∈ front ++ u :: v :: rest := by simp
  have hvMem : v ∈ front ++ u :: v :: rest := by simp
  have huv : Adj k u v :=
    (edgesAlong_drop_prefix front (u :: v :: rest) hEdges).1
  obtain ⟨i, huz, hzv⟩ := edge_has_insertable_vertex
    removed u v huv (hKeep u huMem) (hKeep v hvMem)
  have hzFresh :
      .clique i (removed i) ∉ front ++ u :: v :: rest := by
    intro hz
    exact hKeep _ hz i rfl
  refine ⟨i, ?_, ?_⟩
  · exact edgesAlong_insert_middle
      front rest u v (.clique i (removed i)) hEdges huz hzv
  · have hInserted := nodup_insert_middle
        (front ++ [u]) (v :: rest) (.clique i (removed i))
        (by simpa [List.append_assoc] using hSimple)
        (by simpa [List.append_assoc] using hzFresh)
    simpa [List.append_assoc] using hInserted

#print axioms edgesAlong_drop_prefix
#print axioms simple_path_insert_middle

end HansonToft
