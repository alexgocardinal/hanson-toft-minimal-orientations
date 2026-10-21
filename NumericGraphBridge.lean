import FamilyInduction

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace HansonToft

instance vertexForallDecidable (k : Nat)
    (p : Vertex k → Prop) [DecidablePred p] :
    Decidable (∀ v, p v) :=
  match (inferInstance :
      Decidable ((∀ i, p (.cycle i)) ∧
        (∀ i a, p (.clique i a)))) with
  | .isTrue h =>
      .isTrue (by
        intro v
        cases v with
        | cycle i => exact h.1 i
        | clique i a => exact h.2 i a)
  | .isFalse h =>
      .isFalse (by
        intro hall
        apply h
        exact ⟨fun i => hall (.cycle i),
          fun i a => hall (.clique i a)⟩)

instance graphAdjDecidable (k : Nat) (u v : Vertex k) :
    Decidable (Adj k u v) := by
  cases u <;> cases v <;>
    simp only [Adj, inTriple] <;> infer_instance

def vertexNumber {k : Nat} : Vertex k → Nat
  | .cycle i => i.val
  | .clique i a => 7 + i.val * (k - 3) + a.val

def numericAdj (k u v : Nat) : Prop :=
  if u < 7 then
    if v < 7 then
      (u + 1) % 7 = v ∨ (v + 1) % 7 = u
    else
      let j := (v - 7) / (k - 3)
      u = j ∨ u = (j + 1) % 7 ∨ u = (j + 3) % 7
  else if v < 7 then
    let i := (u - 7) / (k - 3)
    v = i ∨ v = (i + 1) % 7 ∨ v = (i + 3) % 7
  else
    (u - 7) / (k - 3) = (v - 7) / (k - 3) ∧ u ≠ v

instance numericAdjDecidable (k u v : Nat) :
    Decidable (numericAdj k u v) := by
  unfold numericAdj
  infer_instance

theorem finite_numbering_correct :
    ∀ s : Fin 6,
      let k := s.val + 4
      (∀ u : Vertex k, vertexNumber u < 7 * (k - 2)) ∧
      (∀ u v : Vertex k, vertexNumber u = vertexNumber v → u = v) ∧
      (∀ u v : Vertex k,
        numericAdj k (vertexNumber u) (vertexNumber v) ↔ Adj k u v) := by
  decide

#print axioms finite_numbering_correct

end HansonToft
