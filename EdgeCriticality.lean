import InternalEdgeDeletion

namespace HansonToft

theorem properWithoutEdge_swap {k m : Nat}
    (u v : Vertex k) (color : Vertex k → Fin m)
    (h : ProperWithoutEdge k m u v color) :
    ProperWithoutEdge k m v u color := by
  intro a b hAdj hKeep
  apply h a b hAdj
  intro hDeleted
  apply hKeep
  rcases hDeleted with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact Or.inl ⟨ha, hb⟩

theorem all_edge_deletions_colorable {k : Nat}
    (hk : 4 ≤ k) (u v : Vertex k) (hAdj : Adj k u v) :
    ∃ color : Vertex k → Fin (k - 1),
      ProperWithoutEdge k (k - 1) u v color := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 :=
    ⟨k - 4, by omega⟩
  cases u with
  | cycle i =>
      cases v with
      | cycle j =>
          rcases hAdj with hForward | hBackward
          · have hij : cycleStep i 1 = j := Fin.ext hForward
            obtain ⟨color, hColor⟩ :=
              cycle_edge_deletion_colorable (by omega : 4 ≤ m + 4) i
            refine ⟨color, ?_⟩
            simpa only [hij] using hColor
          · have hji : cycleStep j 1 = i := Fin.ext hBackward
            obtain ⟨color, hColor⟩ :=
              cycle_edge_deletion_colorable (by omega : 4 ≤ m + 4) j
            have hReverse :
                ProperWithoutEdge (m + 4) (m + 4 - 1)
                  (.cycle j) (.cycle i) color := by
              simpa only [hji] using hColor
            exact ⟨color,
              properWithoutEdge_swap _ _ color hReverse⟩
      | clique j b =>
          obtain ⟨color, hColor⟩ :=
            attachment_edge_deletion_colorable j i b hAdj
          exact ⟨color, properWithoutEdge_swap _ _ color hColor⟩
  | clique i a =>
      cases v with
      | cycle j =>
          exact attachment_edge_deletion_colorable i j a hAdj
      | clique j b =>
          obtain ⟨hij, hDifferent⟩ := hAdj
          subst j
          have hm : 1 ≤ m := by
            have ha := a.isLt
            have hb := b.isLt
            have hValues : a.val ≠ b.val := by
              intro heq
              exact hDifferent (Fin.ext heq)
            omega
          obtain ⟨n, hn⟩ : ∃ n, m = n + 1 :=
            ⟨m - 1, by omega⟩
          subst m
          exact internal_edge_deletion_colorable i a b hDifferent

theorem edgeCriticalStatement_proved {k : Nat}
    (hk : 4 ≤ k) : EdgeCriticalStatement k := by
  refine ⟨exists_proper_k_coloring hk,
    no_k_minus_one_coloring hk, ?_⟩
  intro u v hAdj
  exact all_edge_deletions_colorable hk u v hAdj

#print axioms edgeCriticalStatement_proved

end HansonToft
