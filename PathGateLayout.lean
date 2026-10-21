import BoundaryAndOrderClauses

namespace HansonToft

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

deriving instance DecidableEq for CNFGate

theorem gateProgram_clause_at (program : List CNFGate) :
    ∀ (next index : Nat) (gate : CNFGate),
      program[index]? = some gate →
      ∀ clause ∈ gateClauses (next + index) gate,
        clause ∈ gateProgramClauses next program := by
  induction program with
  | nil =>
      intro next index gate hLookup
      simp at hLookup
  | cons head rest ih =>
      intro next index gate hLookup clause hClause
      cases index with
      | zero =>
          have hGate : head = gate := Option.some.inj hLookup
          cases hGate
          exact List.mem_append.mpr (Or.inl hClause)
      | succ index =>
          have hLookup' : rest[index]? = some gate := by
            simpa using hLookup
          apply List.mem_append.mpr
          right
          apply ih (next + 1) index gate hLookup' clause
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hClause

theorem gateProgram_or_readback
    (program : List CNFGate) (next index : Nat)
    (inputs : List Nat) (assignment : Nat → Bool)
    (hAll : ∀ clause ∈ gateProgramClauses next program,
      HoldsClause assignment clause)
    (hLookup : program[index]? = some (.orGate inputs)) :
    assignment (next + index) = true ↔
      ∃ x ∈ inputs, assignment x = true := by
  apply (orGateClauses_semantics
    assignment (next + index) inputs).mp
  intro clause hClause
  exact hAll clause
    (gateProgram_clause_at program next index (.orGate inputs)
      hLookup clause hClause)

theorem gateProgram_and_readback
    (program : List CNFGate) (next index x y : Nat)
    (assignment : Nat → Bool)
    (hAll : ∀ clause ∈ gateProgramClauses next program,
      HoldsClause assignment clause)
    (hLookup : program[index]? = some (.andGate x y)) :
    assignment (next + index) = (assignment x && assignment y) := by
  have hGate :
      ∀ clause ∈ gateClauses (next + index) (.andGate x y),
        HoldsClause assignment clause := by
    intro clause hClause
    exact hAll clause
      (gateProgram_clause_at program next index (.andGate x y)
        hLookup clause hClause)
  apply (and_gate_semantics assignment x y (next + index)).mp
  refine ⟨hGate _ ?_, hGate _ ?_, hGate _ ?_⟩ <;>
    simp [gateClauses]

def encodingGateAtFrom
    (gates : Array CNFGate) (start output : Nat)
    (gate : CNFGate) : Prop :=
  start ≤ output ∧ gates[output - start]? = some gate

instance encodingGateAtFromDecidable
    (gates : Array CNFGate) (start output : Nat)
    (gate : CNFGate) :
    Decidable (encodingGateAtFrom gates start output gate) := by
  unfold encodingGateAtFrom
  infer_instance

def encodingGateAt (k output : Nat) (gate : CNFGate) : Prop :=
  encodingGateAtFrom (reconstructEncoding k).gates
    (3 * registerWidth k) output gate

instance encodingGateAtDecidable
    (k output : Nat) (gate : CNFGate) :
    Decidable (encodingGateAt k output gate) := by
  unfold encodingGateAt
  infer_instance

theorem completed_or_gate_readback
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (output : Nat) (inputs : List Nat)
    (hAt : encodingGateAt (s.val + 4) output (.orGate inputs)) :
    counterExtendedAssignment color output = true ↔
      ∃ x ∈ inputs, counterExtendedAssignment color x = true := by
  have hLookup :
      (reconstructEncoding (s.val + 4)).gates.toList[output - 3 * registerWidth (s.val + 4)]? =
          some (.orGate inputs) := by
    simpa using hAt.2
  have hRead := gateProgram_or_readback
    (reconstructEncoding (s.val + 4)).gates.toList
    (3 * registerWidth (s.val + 4))
    (output - 3 * registerWidth (s.val + 4))
    inputs (counterExtendedAssignment color)
    (counterExtendedAssignment_satisfies_gates s color) hLookup
  have hAddress :
      3 * registerWidth (s.val + 4) +
        (output - 3 * registerWidth (s.val + 4)) = output := by
    have hLower := hAt.1
    omega
  simpa only [hAddress] using hRead

theorem completed_and_gate_readback
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (output x y : Nat)
    (hAt : encodingGateAt (s.val + 4) output (.andGate x y)) :
    counterExtendedAssignment color output =
      (counterExtendedAssignment color x &&
        counterExtendedAssignment color y) := by
  have hLookup :
      (reconstructEncoding (s.val + 4)).gates.toList[output - 3 * registerWidth (s.val + 4)]? =
          some (.andGate x y) := by
    simpa using hAt.2
  have hRead := gateProgram_and_readback
    (reconstructEncoding (s.val + 4)).gates.toList
    (3 * registerWidth (s.val + 4))
    (output - 3 * registerWidth (s.val + 4)) x y
    (counterExtendedAssignment color)
    (counterExtendedAssignment_satisfies_gates s color) hLookup
  have hAddress :
      3 * registerWidth (s.val + 4) +
        (output - 3 * registerWidth (s.val + 4)) = output := by
    have hLower := hAt.1
    omega
  simpa only [hAddress] using hRead

structure PairGateLayout where
  left : Nat
  right : Nat
  output : Nat
  deriving Repr

structure PathGateLayout where
  vertex : Nat
  rank : Nat
  reachOr : Nat
  reachAnd : Nat
  pairs : List PairGateLayout
  multiOr : Nat
  multiAnd : Nat
  deriving Repr

def encodingNeighbors (k v : Nat) : List Nat :=
  (List.range (7 * (k - 2))).filter fun u =>
    decide (numericAdj k v u)

def encodingNeighborPairs (k v : Nat) : List (Nat × Nat) :=
  let neighbors := encodingNeighbors k v
  neighbors.flatMap fun u =>
    (neighbors.filter fun w => decide (u < w)).map fun w => (u, w)

def pathGateLayouts (k : Nat) : List PathGateLayout := Id.run do
  let mut cursor := 3 * registerWidth k
  let mut layouts : Array PathGateLayout := #[]
  for v in List.range (7 * (k - 2)) do
    let endpoints := encodingNeighborPairs k v
    for offset in List.range (k - 1) do
      let pairs : List PairGateLayout :=
        endpoints.zipIdx.map fun entry =>
          { left := entry.1.1
            right := entry.1.2
            output := cursor + 2 + entry.2 }
      layouts := layouts.push
        { vertex := v
          rank := offset + 1
          reachOr := cursor
          reachAnd := cursor + 1
          pairs := pairs
          multiOr := cursor + 2 + endpoints.length
          multiAnd := cursor + 3 + endpoints.length }
      cursor := cursor + 4 + endpoints.length
  return layouts.toList

def pathGateLayoutValidFrom
    (k : Nat) (gates : Array CNFGate)
    (layout : PathGateLayout) : Prop :=
  layout.vertex < 7 * (k - 2) ∧
  0 < layout.rank ∧ layout.rank < k ∧
  layout.pairs.map (fun p => (p.left, p.right)) =
    encodingNeighborPairs k layout.vertex ∧
  encodingGateAtFrom gates (3 * registerWidth k) layout.reachOr
    (.orGate ((encodingNeighbors k layout.vertex).map fun u =>
      encodingR k u (layout.rank - 1))) ∧
  encodingGateAtFrom gates (3 * registerWidth k) layout.reachAnd
    (.andGate (encodingC k layout.vertex layout.rank) layout.reachOr) ∧
  (∀ p ∈ layout.pairs,
    encodingGateAtFrom gates (3 * registerWidth k) p.output
      (.andGate (encodingR k p.left (layout.rank - 1))
        (encodingR k p.right (layout.rank - 1)))) ∧
  encodingGateAtFrom gates (3 * registerWidth k) layout.multiOr
    (.orGate
      (((encodingNeighbors k layout.vertex).map fun u =>
        encodingM k u (layout.rank - 1)) ++
        layout.pairs.map (fun p => p.output))) ∧
  encodingGateAtFrom gates (3 * registerWidth k) layout.multiAnd
    (.andGate (encodingC k layout.vertex layout.rank) layout.multiOr)

def pathGateLayoutValid (k : Nat) (layout : PathGateLayout) : Prop :=
  pathGateLayoutValidFrom k (reconstructEncoding k).gates layout

instance pathGateLayoutValidFromDecidable
    (k : Nat) (gates : Array CNFGate) (layout : PathGateLayout) :
    Decidable (pathGateLayoutValidFrom k gates layout) := by
  unfold pathGateLayoutValidFrom
  infer_instance

instance pathGateLayoutValidDecidable
    (k : Nat) (layout : PathGateLayout) :
    Decidable (pathGateLayoutValid k layout) :=
  pathGateLayoutValidFromDecidable
    k (reconstructEncoding k).gates layout

def checkPathGateLayouts (k : Nat) : Bool :=
  let gates := (reconstructEncoding k).gates
  (pathGateLayouts k).all fun layout =>
    decide (pathGateLayoutValidFrom k gates layout)

theorem reconstructed_path_gate_layouts_valid :
    ∀ s : Fin 6,
      ∀ layout ∈ pathGateLayouts (s.val + 4),
        pathGateLayoutValid (s.val + 4) layout := by
  have hChecked :
      ∀ s : Fin 6, checkPathGateLayouts (s.val + 4) = true := by
    decide +native
  intro s
  have h := hChecked s
  simpa only [checkPathGateLayouts, List.all_eq_true,
    decide_eq_true_eq, pathGateLayoutValid] using h

#eval (List.range 6).map fun s =>
  (s + 4, (pathGateLayouts (s + 4)).length)

#print axioms completed_or_gate_readback
#print axioms completed_and_gate_readback
#print axioms reconstructed_path_gate_layouts_valid

end HansonToft
