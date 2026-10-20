import BlockLemmas

namespace HansonToft

theorem endpoint_has_insertable_vertex {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (v : Vertex k)
    (hvKeep : ∀ i, v ≠ .clique i (removed i)) :
    ∃ i, Adj k (.clique i (removed i)) v := by
  obtain ⟨i, hv⟩ := vertex_in_block v
  exact ⟨i, clique_vertex_adjacent_in_block
    i (removed i) v hv (hvKeep i)⟩

theorem edgesAlong_insert_middle {k : Nat}
    (front rest : List (Vertex k)) (u v z : Vertex k)
    (hpath : EdgesAlong (front ++ u :: v :: rest))
    (huz : Adj k u z) (hzv : Adj k z v) :
    EdgesAlong (front ++ u :: z :: v :: rest) := by
  revert hpath
  induction front with
  | nil =>
      intro hpath
      exact ⟨huz, hzv, hpath.2⟩
  | cons w front ih =>
      intro hpath
      cases front with
      | nil =>
          exact ⟨hpath.1, huz, hzv, hpath.2.2⟩
      | cons w' front =>
          exact ⟨hpath.1, ih hpath.2⟩

theorem nodup_insert_middle {α : Type}
    (front rest : List α) (z : α)
    (h : (front ++ rest).Nodup)
    (hz : z ∉ front ++ rest) :
    (front ++ z :: rest).Nodup := by
  revert h hz
  induction front with
  | nil =>
      intro h hz
      exact List.nodup_cons.mpr ⟨hz, h⟩
  | cons a front ih =>
      intro h hz
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp h
      have hzTail : z ∉ front ++ rest := by
        intro hm
        exact hz (List.mem_cons.mpr (Or.inr hm))
      refine List.nodup_cons.mpr ⟨?_, ih htail hzTail⟩
      intro hm
      rcases List.mem_append.mp hm with hf | hr
      · exact hhead (List.mem_append.mpr (Or.inl hf))
      · rcases List.mem_cons.mp hr with haz | hr
        · exact hz (List.mem_cons.mpr (Or.inl haz.symm))
        · exact hhead (List.mem_append.mpr (Or.inr hr))

#print axioms endpoint_has_insertable_vertex
#print axioms edgesAlong_insert_middle
#print axioms nodup_insert_middle

end HansonToft
