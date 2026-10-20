import ChromaticUpperBound

set_option maxHeartbeats 2000000

namespace HansonToft

def brokenCycleColor (e i : Fin 7) : Fin 2 :=
  ⟨((i.val + 7 - ((e.val + 1) % 7)) % 7) % 2,
    Nat.mod_lt _ (by decide)⟩

theorem brokenCycleColor_proper :
    ∀ e i j : Fin 7,
      ((i.val + 1) % 7 = j.val ∨
        (j.val + 1) % 7 = i.val) →
      ¬ ((i = e ∧ j = cycleStep e 1) ∨
        (i = cycleStep e 1 ∧ j = e)) →
      brokenCycleColor e i ≠ brokenCycleColor e j := by
  decide

def cycleEdgeColor (k : Nat) (hk : 4 ≤ k) (e : Fin 7) :
    Vertex k → Fin (k - 1)
  | .cycle i =>
      ⟨(brokenCycleColor e i).val, by
        have h := (brokenCycleColor e i).isLt
        omega⟩
  | .clique _ a =>
      ⟨a.val + 2, by
        have h := a.isLt
        omega⟩

theorem cycleEdgeColor_proper (k : Nat) (hk : 4 ≤ k)
    (e : Fin 7) :
    ProperWithoutEdge k (k - 1)
      (.cycle e) (.cycle (cycleStep e 1))
      (cycleEdgeColor k hk e) := by
  intro u v hAdj hKeep hEqual
  have hValues := congrArg Fin.val hEqual
  cases u with
  | cycle i =>
      cases v with
      | cycle j =>
          have hNot :
              ¬ ((i = e ∧ j = cycleStep e 1) ∨
                (i = cycleStep e 1 ∧ j = e)) := by
            intro h
            apply hKeep
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
          apply brokenCycleColor_proper e i j hAdj hNot
          apply Fin.ext
          exact hValues
      | clique j b =>
          change (brokenCycleColor e i).val = b.val + 2 at hValues
          have hSmall := (brokenCycleColor e i).isLt
          omega
  | clique i a =>
      cases v with
      | cycle j =>
          change a.val + 2 = (brokenCycleColor e j).val at hValues
          have hSmall := (brokenCycleColor e j).isLt
          omega
      | clique j b =>
          change a.val + 2 = b.val + 2 at hValues
          apply hAdj.2
          apply Fin.ext
          omega

theorem cycle_edge_deletion_colorable {k : Nat}
    (hk : 4 ≤ k) (e : Fin 7) :
    ∃ color : Vertex k → Fin (k - 1),
      ProperWithoutEdge k (k - 1)
        (.cycle e) (.cycle (cycleStep e 1)) color := by
  exact ⟨cycleEdgeColor k hk e, cycleEdgeColor_proper k hk e⟩

#print axioms brokenCycleColor_proper
#print axioms cycle_edge_deletion_colorable

end HansonToft
