import PathRegisterAssignment

namespace HansonToft

def assignFresh (assignment : Nat → Bool)
    (output : Nat) (value : Bool) : Nat → Bool :=
  fun varId => if varId = output then value else assignment varId

theorem assignFresh_at_output
    (assignment : Nat → Bool) (output : Nat) (value : Bool) :
    assignFresh assignment output value output = value := by
  simp [assignFresh]

theorem assignFresh_below
    (assignment : Nat → Bool) (output : Nat) (value : Bool)
    (varId : Nat) (hBelow : varId < output) :
    assignFresh assignment output value varId = assignment varId := by
  simp [assignFresh, Nat.ne_of_lt hBelow]

theorem holdsClause_congr_on
    (assignment other : Nat → Bool)
    (clause : List (Nat × Bool))
    (hAgree : ∀ lit ∈ clause, assignment lit.1 = other lit.1) :
    HoldsClause assignment clause ↔ HoldsClause other clause := by
  rw [holdsClause_iff, holdsClause_iff]
  constructor
  · rintro ⟨lit, hMem, hValue⟩
    refine ⟨lit, hMem, ?_⟩
    rw [← hAgree lit hMem]
    exact hValue
  · rintro ⟨lit, hMem, hValue⟩
    refine ⟨lit, hMem, ?_⟩
    rw [hAgree lit hMem]
    exact hValue

theorem assignFresh_preserves_clause
    (assignment : Nat → Bool) (output : Nat) (value : Bool)
    (clause : List (Nat × Bool))
    (hBelow : ∀ lit ∈ clause, lit.1 < output) :
    HoldsClause assignment clause ↔
      HoldsClause (assignFresh assignment output value) clause := by
  apply holdsClause_congr_on
  intro lit hMem
  exact (assignFresh_below assignment output value
    lit.1 (hBelow lit hMem)).symm

noncomputable def assignOr
    (assignment : Nat → Bool) (output : Nat)
    (inputs : List Nat) : Nat → Bool := by
  classical
  exact assignFresh assignment output
    (decide (∃ x ∈ inputs, assignment x = true))

theorem fresh_or_gate_satisfied
    (assignment : Nat → Bool) (output : Nat)
    (inputs : List Nat)
    (hBelow : ∀ x ∈ inputs, x < output) :
    ∀ clause ∈ orGateClauses output inputs,
      HoldsClause (assignOr assignment output inputs) clause := by
  classical
  have hOutput :
      assignOr assignment output inputs output = true ↔
        ∃ x ∈ inputs, assignment x = true := by
    simp [assignOr, assignFresh]
  have hInput : ∀ x ∈ inputs,
      assignOr assignment output inputs x = assignment x := by
    intro x hx
    simp only [assignOr]
    apply assignFresh_below
    exact hBelow x hx
  apply (orGateClauses_semantics
    (assignOr assignment output inputs) output inputs).mpr
  constructor
  · intro h
    obtain ⟨x, hx, hTrue⟩ := hOutput.mp h
    exact ⟨x, hx, (hInput x hx).trans hTrue⟩
  · rintro ⟨x, hx, hTrue⟩
    apply hOutput.mpr
    exact ⟨x, hx, (hInput x hx).symm.trans hTrue⟩

theorem fresh_and_gate_satisfied
    (assignment : Nat → Bool) (output x y : Nat)
    (hx : x < output) (hy : y < output) :
    let extended :=
      assignFresh assignment output (assignment x && assignment y)
    HoldsClause extended [(output, false), (x, true)] ∧
    HoldsClause extended [(output, false), (y, true)] ∧
    HoldsClause extended [(output, true), (x, false), (y, false)] := by
  let extended :=
    assignFresh assignment output (assignment x && assignment y)
  have hGate : extended output = (extended x && extended y) := by
    dsimp [extended]
    simp [assignFresh, Nat.ne_of_lt hx, Nat.ne_of_lt hy]
  exact (and_gate_semantics extended x y output).mpr hGate

theorem register_variables_below_gate {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (v : Vertex k) (rank : Fin k)
    (output : Nat) (hStart : 3 * registerWidth k ≤ output) :
    colorVariable v rank.val < output ∧
    reachVariable v rank.val < output ∧
    multiplicityVariable v rank.val < output := by
  have hBound := colorVariable_bound hk4 hk9 v rank
  unfold reachVariable multiplicityVariable
  omega

#print axioms assignFresh_preserves_clause
#print axioms fresh_or_gate_satisfied
#print axioms fresh_and_gate_satisfied
#print axioms register_variables_below_gate

end HansonToft
