import ReconstructedUnsatisfiability

namespace HansonToft

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

instance gateInputsBelowDecidable
    (output : Nat) (gate : CNFGate) :
    Decidable (gateInputsBelow output gate) := by
  cases gate with
  | orGate inputs =>
      unfold gateInputsBelow
      infer_instance
  | andGate x y =>
      unfold gateInputsBelow
      infer_instance

instance gateProgramValidDecidable (next : Nat) :
    (program : List CNFGate) →
      Decidable (gateProgramValid next program)
  | [] => isTrue trivial
  | gate :: rest => by
      letI : Decidable (gateProgramValid (next + 1) rest) :=
        gateProgramValidDecidable (next + 1) rest
      exact inferInstanceAs
        (Decidable (gateInputsBelow next gate ∧
          gateProgramValid (next + 1) rest))

theorem reconstructed_gate_programs_valid :
    ∀ s : Fin 6,
      gateProgramValid (3 * registerWidth (s.val + 4))
        (reconstructEncoding (s.val + 4)).gates.toList := by
  decide +native

theorem reconstructed_variable_layout :
    ∀ s : Fin 6,
      let k := s.val + 4
      let result := reconstructEncoding k
      result.next =
        3 * registerWidth k + result.gates.size +
          (7 * (k - 2) - 1) := by
  decide +native

noncomputable def gateExtendedAssignment {k : Nat}
    (color : Vertex k → Fin k) : Nat → Bool :=
  runGateProgram (registerAssignment color)
    (3 * registerWidth k)
    (reconstructEncoding k).gates.toList

theorem gateExtendedAssignment_correct {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a : Fin k) :
    (gateExtendedAssignment color (colorVariable v a.val) = true ↔
      color v = a) ∧
    (gateExtendedAssignment color (reachVariable v a.val) = true ↔
      ReachesRank color a.val v) ∧
    (gateExtendedAssignment color
        (multiplicityVariable v a.val) = true ↔
      MultipleRankPaths color a.val v) := by
  have hBounds := register_variables_below_gate
    hk4 hk9 v a (3 * registerWidth k) (Nat.le_refl _)
  have hC := runGateProgram_below
    (reconstructEncoding k).gates.toList
    (3 * registerWidth k) (registerAssignment color)
    (colorVariable v a.val) hBounds.1
  have hR := runGateProgram_below
    (reconstructEncoding k).gates.toList
    (3 * registerWidth k) (registerAssignment color)
    (reachVariable v a.val) hBounds.2.1
  have hM := runGateProgram_below
    (reconstructEncoding k).gates.toList
    (3 * registerWidth k) (registerAssignment color)
    (multiplicityVariable v a.val) hBounds.2.2
  unfold gateExtendedAssignment
  rw [hC, hR, hM]
  exact registerAssignment_correct hk4 hk9 color v a

theorem gateExtendedAssignment_satisfies_gates
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4)) :
    ∀ clause ∈ gateProgramClauses
        (3 * registerWidth (s.val + 4))
        (reconstructEncoding (s.val + 4)).gates.toList,
      HoldsClause (gateExtendedAssignment color) clause := by
  exact runGateProgram_satisfies
    (reconstructEncoding (s.val + 4)).gates.toList
    (3 * registerWidth (s.val + 4))
    (registerAssignment color)
    (reconstructed_gate_programs_valid s)

#print axioms reconstructed_gate_programs_valid
#print axioms reconstructed_variable_layout
#print axioms gateExtendedAssignment_correct
#print axioms gateExtendedAssignment_satisfies_gates

end HansonToft
