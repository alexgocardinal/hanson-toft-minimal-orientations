import HansonToft

namespace HansonToft

theorem adj_symmetric (k : Nat) (u v : Vertex k) :
    Adj k u v ↔ Adj k v u := by
  cases u <;> cases v <;>
    simp [Adj, eq_comm, and_comm, or_comm]

theorem cycle_no_loop :
    ∀ i : Fin 7, (i.val + 1) % 7 ≠ i.val := by
  decide

theorem adj_irreflexive (k : Nat) (v : Vertex k) :
    ¬ Adj k v v := by
  cases v with
  | cycle i =>
      simpa only [Adj, or_self] using cycle_no_loop i
  | clique i a =>
      simp [Adj]

#print axioms adj_symmetric
#print axioms adj_irreflexive

end HansonToft
