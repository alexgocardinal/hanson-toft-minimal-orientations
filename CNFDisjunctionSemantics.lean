import CNFClauseSemantics

namespace HansonToft

theorem holdsClause_nil (assignment : Nat → Bool) :
    ¬ HoldsClause assignment [] := by
  simp [holdsClause_iff]


theorem holdsClause_cons (assignment : Nat → Bool)
    (x : Nat) (polarity : Bool) (rest : List (Nat × Bool)) :
    HoldsClause assignment ((x, polarity) :: rest) ↔
      assignment x = polarity ∨ HoldsClause assignment rest := by
  simp [holdsClause_iff]

theorem holdsClause_positive (assignment : Nat → Bool)
    (inputs : List Nat) :
    HoldsClause assignment (inputs.map (fun x => (x, true))) ↔
      ∃ x ∈ inputs, assignment x = true := by
  rw [holdsClause_iff]
  constructor
  · rintro ⟨literal, hMem, hValue⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hMem
    exact ⟨x, hx, hValue⟩
  · rintro ⟨x, hx, hValue⟩
    exact ⟨(x, true), List.mem_map.mpr ⟨x, hx, rfl⟩, hValue⟩

theorem disjunction_gate_semantics (assignment : Nat → Bool)
    (output : Nat) (inputs : List Nat) :
    ((∀ x ∈ inputs,
        HoldsClause assignment [(x, false), (output, true)]) ∧
      HoldsClause assignment
        ((output, false) :: inputs.map (fun x => (x, true)))) ↔
    (assignment output = true ↔
      ∃ x ∈ inputs, assignment x = true) := by
  simp only [holdsClause_cons, holdsClause_positive, holdsClause_nil, or_false]
  constructor
  · rintro ⟨hRules, hLong⟩
    constructor
    · intro hTrue
      rcases hLong with hFalse | hExists
      · rw [hTrue] at hFalse
        cases hFalse
      · exact hExists
    · rintro ⟨x, hx, hTrue⟩
      rcases hRules x hx with hFalse | hOutput
      · rw [hTrue] at hFalse
        cases hFalse
      · exact hOutput
  · intro hEquivalent
    constructor
    · intro x hx
      by_cases hTrue : assignment x = true
      · exact Or.inr (hEquivalent.mpr ⟨x, hx, hTrue⟩)
      · left
        cases hValue : assignment x <;> simp_all
    · by_cases hTrue : assignment output = true
      · exact Or.inr (hEquivalent.mp hTrue)
      · left
        cases hValue : assignment output <;> simp_all

def orGateClauses (output : Nat) (inputs : List Nat) :
    List (List (Nat × Bool)) :=
  inputs.map (fun x => [(x, false), (output, true)]) ++
    [((output, false) :: inputs.map (fun x => (x, true)))]

theorem orGateClauses_semantics (assignment : Nat → Bool)
    (output : Nat) (inputs : List Nat) :
    (∀ clause ∈ orGateClauses output inputs,
      HoldsClause assignment clause) ↔
    (assignment output = true ↔
      ∃ x ∈ inputs, assignment x = true) := by
  have hForm :
      (∀ clause ∈ orGateClauses output inputs,
        HoldsClause assignment clause) ↔
      ((∀ x ∈ inputs,
          HoldsClause assignment [(x, false), (output, true)]) ∧
        HoldsClause assignment
          ((output, false) :: inputs.map (fun x => (x, true)))) := by
    constructor
    · intro hAll
      constructor
      · intro x hx
        apply hAll
        exact List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨x, hx, rfl⟩))
      · apply hAll
        exact List.mem_append.mpr (Or.inr (by simp))
    · rintro ⟨hRules, hLong⟩ clause hMem
      rcases List.mem_append.mp hMem with hMap | hLast
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hMap
        exact hRules x hx
      · have hEqual := List.mem_singleton.mp hLast
        subst clause
        exact hLong
  exact hForm.trans (disjunction_gate_semantics assignment output inputs)

#print axioms orGateClauses_semantics

end HansonToft
