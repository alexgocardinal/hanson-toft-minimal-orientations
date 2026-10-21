import GateAssignmentExtension

namespace HansonToft

inductive CNFGate where
  | orGate (inputs : List Nat)
  | andGate (x y : Nat)
  deriving Repr

def gateInputsBelow (output : Nat) : CNFGate → Prop
  | .orGate inputs => ∀ x ∈ inputs, x < output
  | .andGate x y => x < output ∧ y < output

def gateClauses (output : Nat) :
    CNFGate → List (List (Nat × Bool))
  | .orGate inputs => orGateClauses output inputs
  | .andGate x y =>
      [[(output, false), (x, true)],
       [(output, false), (y, true)],
       [(output, true), (x, false), (y, false)]]

noncomputable def extendGate
    (assignment : Nat → Bool) (output : Nat) :
    CNFGate → Nat → Bool
  | .orGate inputs => assignOr assignment output inputs
  | .andGate x y =>
      assignFresh assignment output (assignment x && assignment y)

theorem extendGate_below
    (assignment : Nat → Bool) (output : Nat)
    (gate : CNFGate) (x : Nat) (hx : x < output) :
    extendGate assignment output gate x = assignment x := by
  cases gate with
  | orGate inputs =>
      unfold extendGate assignOr
      exact assignFresh_below assignment output _ x hx
  | andGate a b =>
      exact assignFresh_below assignment output _ x hx

theorem extendGate_satisfies
    (assignment : Nat → Bool) (output : Nat)
    (gate : CNFGate) (hBelow : gateInputsBelow output gate) :
    ∀ clause ∈ gateClauses output gate,
      HoldsClause (extendGate assignment output gate) clause := by
  cases gate with
  | orGate inputs =>
      exact fresh_or_gate_satisfied assignment output inputs hBelow
  | andGate x y =>
      have h := fresh_and_gate_satisfied
        assignment output x y hBelow.1 hBelow.2
      intro clause hClause
      simp only [gateClauses, List.mem_cons,
        List.not_mem_nil, or_false] at hClause
      rcases hClause with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

theorem gateClause_variables_bounded
    (output : Nat) (gate : CNFGate)
    (hBelow : gateInputsBelow output gate)
    (clause : List (Nat × Bool))
    (hClause : clause ∈ gateClauses output gate)
    (lit : Nat × Bool) (hLit : lit ∈ clause) :
    lit.1 < output + 1 := by
  cases gate with
  | orGate inputs =>
      change clause ∈ orGateClauses output inputs at hClause
      unfold orGateClauses at hClause
      rcases List.mem_append.mp hClause with hMapped | hLast
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hMapped
        rcases List.mem_cons.mp hLit with hFirst | hSecond
        · subst lit
          exact Nat.lt_succ_of_lt (hBelow x hx)
        · have hEq := List.mem_singleton.mp hSecond
          subst lit
          simp
      · have hEq := List.mem_singleton.mp hLast
        subst clause
        rcases List.mem_cons.mp hLit with hFirst | hRest
        · subst lit
          simp
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hRest
          exact Nat.lt_succ_of_lt (hBelow x hx)
  | andGate x y =>
      have hx := hBelow.1
      have hy := hBelow.2
      simp only [gateClauses, List.mem_cons,
        List.not_mem_nil, or_false] at hClause
      rcases hClause with rfl | rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
        rcases hLit with rfl | rfl <;> dsimp <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
        rcases hLit with rfl | rfl <;> dsimp <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hLit
        rcases hLit with rfl | rfl | rfl <;> dsimp <;> omega

def gateProgramValid : Nat → List CNFGate → Prop
  | _, [] => True
  | next, gate :: rest =>
      gateInputsBelow next gate ∧ gateProgramValid (next + 1) rest

def gateProgramClauses : Nat → List CNFGate →
    List (List (Nat × Bool))
  | _, [] => []
  | next, gate :: rest =>
      gateClauses next gate ++ gateProgramClauses (next + 1) rest

noncomputable def runGateProgram
    (assignment : Nat → Bool) (next : Nat) :
    List CNFGate → Nat → Bool
  | [] => assignment
  | gate :: rest =>
      runGateProgram (extendGate assignment next gate) (next + 1) rest

theorem runGateProgram_below (program : List CNFGate) :
    ∀ (next : Nat) (assignment : Nat → Bool) (x : Nat),
      x < next →
      runGateProgram assignment next program x = assignment x := by
  induction program with
  | nil =>
      intro next assignment x hx
      rfl
  | cons gate rest ih =>
      intro next assignment x hx
      change runGateProgram
        (extendGate assignment next gate) (next + 1) rest x =
          assignment x
      rw [ih (next + 1) (extendGate assignment next gate) x (by omega)]
      exact extendGate_below assignment next gate x hx

theorem runGateProgram_satisfies (program : List CNFGate) :
    ∀ (next : Nat) (assignment : Nat → Bool),
      gateProgramValid next program →
      ∀ clause ∈ gateProgramClauses next program,
        HoldsClause (runGateProgram assignment next program) clause := by
  induction program with
  | nil =>
      intro next assignment hValid clause hClause
      cases hClause
  | cons gate rest ih =>
      intro next assignment hValid clause hClause
      change clause ∈ gateClauses next gate ++
        gateProgramClauses (next + 1) rest at hClause
      rcases List.mem_append.mp hClause with hHere | hRest
      · have hLocal :=
          extendGate_satisfies assignment next gate hValid.1 clause hHere
        apply (holdsClause_congr_on
          (extendGate assignment next gate)
          (runGateProgram assignment next (gate :: rest))
          clause ?_).mp hLocal
        intro lit hLit
        exact (runGateProgram_below rest (next + 1)
          (extendGate assignment next gate) lit.1
          (gateClause_variables_bounded
            next gate hValid.1 clause hHere lit hLit)).symm
      · exact ih (next + 1) (extendGate assignment next gate)
          hValid.2 clause hRest

theorem runGateProgram_preserves_clause
    (program : List CNFGate)
    (next : Nat) (assignment : Nat → Bool)
    (clause : List (Nat × Bool))
    (hBelow : ∀ lit ∈ clause, lit.1 < next) :
    HoldsClause assignment clause ↔
      HoldsClause (runGateProgram assignment next program) clause := by
  apply holdsClause_congr_on
  intro lit hLit
  exact (runGateProgram_below program next assignment
    lit.1 (hBelow lit hLit)).symm

#print axioms runGateProgram_below
#print axioms runGateProgram_satisfies
#print axioms runGateProgram_preserves_clause

end HansonToft
