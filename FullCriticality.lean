import EdgeCriticality

namespace HansonToft

theorem no_isolated_vertices (k : Nat) (v : Vertex k) :
    ∃ w, Adj k v w := by
  cases v with
  | cycle i =>
      exact ⟨.cycle (cycleStep i 1), Or.inl rfl⟩
  | clique i a =>
      exact ⟨.cycle i, Or.inl rfl⟩

theorem vertex_deletion_colorable {k : Nat}
    (hk : 4 ≤ k) (v : Vertex k) :
    ∃ color : Vertex k → Fin (k - 1),
      ∀ a b, Adj k a b → a ≠ v → b ≠ v →
        color a ≠ color b := by
  obtain ⟨w, hEdge⟩ := no_isolated_vertices k v
  obtain ⟨color, hColor⟩ :=
    all_edge_deletions_colorable hk v w hEdge
  refine ⟨color, ?_⟩
  intro a b hAdj ha hb
  apply hColor a b hAdj
  intro hDeleted
  rcases hDeleted with ⟨hav, hbw⟩ | ⟨haw, hbv⟩
  · exact ha hav
  · exact hb hbv

theorem proper_subgraph_colorable {k : Nat}
    (hk : 4 ≤ k)
    (keep : Vertex k → Prop)
    (edges : Vertex k → Vertex k → Prop)
    (hEdges : ∀ a b, edges a b →
      Adj k a b ∧ keep a ∧ keep b)
    (hStrict :
      (∃ v, ¬ keep v) ∨
      (∃ u v, Adj k u v ∧ ¬ edges u v ∧ ¬ edges v u)) :
    ∃ color : Vertex k → Fin (k - 1),
      ∀ a b, edges a b → color a ≠ color b := by
  rcases hStrict with hVertex | hEdge
  · obtain ⟨v, hv⟩ := hVertex
    obtain ⟨color, hColor⟩ := vertex_deletion_colorable hk v
    refine ⟨color, ?_⟩
    intro a b hab
    obtain ⟨hAdj, haKeep, hbKeep⟩ := hEdges a b hab
    have ha : a ≠ v := by
      intro heq
      subst a
      exact hv haKeep
    have hb : b ≠ v := by
      intro heq
      subst b
      exact hv hbKeep
    exact hColor a b hAdj ha hb
  · obtain ⟨u, v, huv, hMissing, hMissingReverse⟩ := hEdge
    obtain ⟨color, hColor⟩ :=
      all_edge_deletions_colorable hk u v huv
    refine ⟨color, ?_⟩
    intro a b hab
    apply hColor a b (hEdges a b hab).1
    intro hDeleted
    rcases hDeleted with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hMissing hab
    · exact hMissingReverse hab

#print axioms vertex_deletion_colorable
#print axioms proper_subgraph_colorable

end HansonToft
