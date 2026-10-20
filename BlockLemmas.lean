import GraphLemmas

namespace HansonToft

def InBlock {k : Nat} (i : Fin 7) : Vertex k → Prop
  | .cycle j => inTriple i j
  | .clique j _ => j = i

theorem vertex_in_block {k : Nat} (v : Vertex k) :
    ∃ i, InBlock i v := by
  cases v with
  | cycle j => exact ⟨j, Or.inl rfl⟩
  | clique j a => exact ⟨j, rfl⟩

theorem edge_in_block {k : Nat} (u v : Vertex k)
    (h : Adj k u v) :
    ∃ i, InBlock i u ∧ InBlock i v := by
  cases u with
  | cycle i =>
      cases v with
      | cycle j =>
          rcases h with h | h
          · exact ⟨i, Or.inl rfl, Or.inr (Or.inl h.symm)⟩
          · exact ⟨j, Or.inr (Or.inl h.symm), Or.inl rfl⟩
      | clique j b =>
          exact ⟨j, h, rfl⟩
  | clique i a =>
      cases v with
      | cycle j =>
          exact ⟨i, rfl, h⟩
      | clique j b =>
          exact ⟨i, rfl, h.1.symm⟩

theorem clique_vertex_adjacent_in_block {k : Nat}
    (i : Fin 7) (a : Fin (k - 3)) (v : Vertex k)
    (hv : InBlock i v) (hne : v ≠ .clique i a) :
    Adj k (.clique i a) v := by
  cases v with
  | cycle j =>
      exact hv
  | clique j b =>
      change j = i at hv
      subst j
      change i = i ∧ a ≠ b
      refine ⟨rfl, ?_⟩
      intro hab
      apply hne
      cases hab
      rfl

theorem edge_has_insertable_vertex {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (u v : Vertex k) (h : Adj k u v)
    (huKeep : ∀ i, u ≠ .clique i (removed i))
    (hvKeep : ∀ i, v ≠ .clique i (removed i)) :
    ∃ i, Adj k u (.clique i (removed i)) ∧
      Adj k (.clique i (removed i)) v := by
  obtain ⟨i, hu, hv⟩ := edge_in_block u v h
  refine ⟨i, ?_, ?_⟩
  · exact (adj_symmetric k u (.clique i (removed i))).mpr
      (clique_vertex_adjacent_in_block i (removed i) u hu (huKeep i))
  · exact clique_vertex_adjacent_in_block i (removed i) v hv (hvKeep i)

#print axioms vertex_in_block
#print axioms edge_in_block
#print axioms edge_has_insertable_vertex

end HansonToft
