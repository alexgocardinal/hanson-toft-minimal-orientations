import NumericEndpointSemantics

namespace HansonToft

def encodingCounterStart (k : Nat) : Nat :=
  3 * registerWidth k + (reconstructEncoding k).gates.size

noncomputable def counterExtendedAssignment {k : Nat}
    (color : Vertex k → Fin k) (varId : Nat) : Bool :=
  if encodingCounterStart k ≤ varId ∧
      varId < encodingCounterStart k + (7 * (k - 2) - 1) then
    counterSeen (finalEndpointInputs color)
      (varId - encodingCounterStart k)
  else gateExtendedAssignment color varId

theorem counterExtendedAssignment_below {k : Nat}
    (color : Vertex k → Fin k) (varId : Nat)
    (hBelow : varId < encodingCounterStart k) :
    counterExtendedAssignment color varId =
      gateExtendedAssignment color varId := by
  have hNot : ¬ encodingCounterStart k ≤ varId := by omega
  simp [counterExtendedAssignment, hNot]

theorem counterExtendedAssignment_aux {k : Nat}
    (color : Vertex k → Fin k) (j : Nat)
    (hj : j < 7 * (k - 2) - 1) :
    counterExtendedAssignment color (encodingCounterStart k + j) =
      counterSeen (finalEndpointInputs color) j := by
  have hLower :
      encodingCounterStart k ≤ encodingCounterStart k + j := by
    omega
  have hUpper :
      encodingCounterStart k + j <
        encodingCounterStart k + (7 * (k - 2) - 1) := by
    omega
  simp [counterExtendedAssignment, hLower, hUpper]

theorem numeric_endpoint_below_counter
    (s : Fin 6) (j : Nat)
    (hj : j < 7 * ((s.val + 4) - 2)) :
    encodingR (s.val + 4) j ((s.val + 4) - 1) <
      encodingCounterStart (s.val + 4) := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega
  obtain ⟨v, hv⟩ := finite_numbering_surjective s ⟨j, hj⟩
  let rank : Fin (s.val + 4) :=
    ⟨(s.val + 4) - 1, by omega⟩
  have hStart :
      3 * registerWidth (s.val + 4) ≤
        encodingCounterStart (s.val + 4) := by
    unfold encodingCounterStart
    omega
  have hBounds := register_variables_below_gate
    hk4 hk9 v rank (encodingCounterStart (s.val + 4)) hStart
  rw [encodingR_of_vertexNumber v j ((s.val + 4) - 1) hv]
  exact hBounds.2.1

theorem counterExtendedAssignment_input
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (j : Nat) (hj : j < 7 * ((s.val + 4) - 2)) :
    counterExtendedAssignment color
        (encodingR (s.val + 4) j ((s.val + 4) - 1)) =
      finalEndpointInputs color j := by
  exact counterExtendedAssignment_below color _
    (numeric_endpoint_below_counter s j hj)

theorem counterExtendedAssignment_satisfies_counter
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    SequentialCounter (7 * ((s.val + 4) - 2))
      (fun j => counterExtendedAssignment color
        (encodingR (s.val + 4) j ((s.val + 4) - 1)))
      (fun j => counterExtendedAssignment color
        (encodingCounterStart (s.val + 4) + j)) := by
  have hn : 2 ≤ 7 * ((s.val + 4) - 2) := by omega
  have hCanonical := sequential_counter_complete hn
    (finalEndpointInputs color)
    (unique_path_numeric_endpoints_at_most_one s color hUnique)
  refine ⟨?_, ?_, ?_⟩
  · have hInput := counterExtendedAssignment_input
      s color 0 (by omega)
    have hAux := counterExtendedAssignment_aux color 0 (by omega)
    simpa only [hInput, hAux] using hCanonical.1
  · intro j hj
    have hInput := counterExtendedAssignment_input
      s color (j + 1) (by omega)
    have hAux := counterExtendedAssignment_aux color j (by omega)
    have hNext := counterExtendedAssignment_aux
      color (j + 1) (by omega)
    simpa only [hInput, hAux, hNext] using hCanonical.2.1 j hj
  · have hInput := counterExtendedAssignment_input
      s color (7 * ((s.val + 4) - 2) - 1) (by omega)
    have hAux := counterExtendedAssignment_aux
      color (7 * ((s.val + 4) - 2) - 2) (by omega)
    simpa only [hInput, hAux] using hCanonical.2.2

def encodingCounterClausesHold
    (assignment : Nat → Bool) (k : Nat) : Prop :=
  let n := 7 * (k - 2)
  let start := encodingCounterStart k
  HoldsClause assignment
      [(encodingR k 0 (k - 1), false), (start + 0, true)] ∧
  (∀ j, j + 2 < n →
    HoldsClause assignment
      [(start + j, false), (start + (j + 1), true)] ∧
    HoldsClause assignment
      [(encodingR k (j + 1) (k - 1), false), (start + j, false)] ∧
    HoldsClause assignment
      [(encodingR k (j + 1) (k - 1), false),
        (start + (j + 1), true)]) ∧
  HoldsClause assignment
    [(encodingR k (n - 1) (k - 1), false),
      (start + (n - 2), false)]

theorem counterExtendedAssignment_satisfies_counter_clauses
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    encodingCounterClausesHold
      (counterExtendedAssignment color) (s.val + 4) := by
  exact (sequential_counter_clause_semantics
    (counterExtendedAssignment color)
    (fun j => encodingR (s.val + 4) j ((s.val + 4) - 1))
    (fun j => encodingCounterStart (s.val + 4) + j)
    (7 * ((s.val + 4) - 2))).mpr
      (counterExtendedAssignment_satisfies_counter s color hUnique)

#print axioms counterExtendedAssignment_satisfies_counter
#print axioms counterExtendedAssignment_satisfies_counter_clauses

end HansonToft
