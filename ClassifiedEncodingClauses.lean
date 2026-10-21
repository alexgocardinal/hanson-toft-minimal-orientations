import MultiplicityRegisterLinks
import Init.Data.List.Sort

namespace HansonToft

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def encodingAtLeastClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  (List.range (7 * (k - 2))).map fun v =>
    (List.range k).map fun a => (encodingC k v a, true)

def encodingAtMostClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  (List.range (7 * (k - 2))).flatMap fun v =>
    (List.range k).flatMap fun a =>
      ((List.range k).filter fun b => decide (a < b)).map fun b =>
        [(encodingC k v a, false), (encodingC k v b, false)]

def encodingEdgeClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  (List.range (7 * (k - 2))).flatMap fun u =>
    (List.range (7 * (k - 2))).flatMap fun v =>
      if u < v ∧ numericAdj k u v then
        (List.range k).map fun a =>
          [(encodingC k u a, false), (encodingC k v a, false)]
      else []

def encodingCliqueOrderClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  (List.range 7).flatMap fun i =>
    (List.range (k - 4)).flatMap fun offset =>
      let u := 7 + i * (k - 3) + offset
      (List.range k).flatMap fun a =>
        (List.range (a + 1)).map fun b =>
          [(encodingC k u a, false),
           (encodingC k (u + 1) b, false)]

def encodingCycleMinimumClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  (List.range 6).flatMap fun offset =>
    (List.range k).flatMap fun a =>
      (List.range a).map fun b =>
        [(encodingC k 0 a, false),
         (encodingC k (offset + 1) b, false)]

def encodingInitialPathClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  (List.range (7 * (k - 2))).flatMap fun v =>
    [[(encodingR k v 0, false), (encodingC k v 0, true)],
     [(encodingC k v 0, false), (encodingR k v 0, true)],
     [(encodingM k v 0, false)]]

def encodingPathLinkClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  (pathGateLayouts k).flatMap fun layout =>
    [[(encodingR k layout.vertex layout.rank, false),
       (layout.reachAnd, true)],
     [(layout.reachAnd, false),
       (encodingR k layout.vertex layout.rank, true)],
     [(encodingM k layout.vertex layout.rank, false),
       (layout.multiAnd, true)],
     [(layout.multiAnd, false),
       (encodingM k layout.vertex layout.rank, true)]]

def encodingFinalPathClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  [((List.range (7 * (k - 2))).map fun v =>
      (encodingR k v (k - 1), true))] ++
  (List.range (7 * (k - 2))).map fun v =>
    [(encodingM k v (k - 1), false)]

def encodingCounterClauseList (k start : Nat) :
    List (List (Nat × Bool)) :=
  let n := 7 * (k - 2)
  [[(encodingR k 0 (k - 1), false), (start, true)]] ++
  (List.range (n - 2)).flatMap (fun j =>
    [[(start + j, false), (start + (j + 1), true)],
     [(encodingR k (j + 1) (k - 1), false), (start + j, false)],
     [(encodingR k (j + 1) (k - 1), false),
       (start + (j + 1), true)]]) ++
  [[(encodingR k (n - 1) (k - 1), false),
     (start + (n - 2), false)]]

def encodingHalfClause (k : Nat) : List (Nat × Bool) :=
  (List.range ((k + 1) / 2)).map fun a => (encodingC k 0 a, true)

def classifiedEncodingClauses (k : Nat) :
    List (List (Nat × Bool)) :=
  let result := reconstructEncoding k
  let counterStart := 3 * registerWidth k + result.gates.size
  encodingAtLeastClauses k ++
  encodingAtMostClauses k ++
  encodingEdgeClauses k ++
  encodingCliqueOrderClauses k ++
  encodingCycleMinimumClauses k ++
  encodingInitialPathClauses k ++
  gateProgramClauses (3 * registerWidth k) result.gates.toList ++
  encodingPathLinkClauses k ++
  encodingFinalPathClauses k ++
  encodingCounterClauseList k counterStart ++
  [encodingHalfClause k]

def clauseLexLE :
    List (Nat × Bool) → List (Nat × Bool) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: leftRest, b :: rightRest =>
      if a.1 < b.1 then true
      else if b.1 < a.1 then false
      else if a.2 = b.2 then clauseLexLE leftRest rightRest
      else !a.2

def checkClassifiedEncoding (k : Nat) : Bool :=
  let original := (reconstructEncoding k).clauses.toList
  let classified := classifiedEncodingClauses k
  decide (original.mergeSort clauseLexLE =
    classified.mergeSort clauseLexLE)

theorem classified_encoding_membership
    (s : Fin 6) (clause : List (Nat × Bool)) :
    clause ∈ (reconstructEncoding (s.val + 4)).clauses.toList ↔
      clause ∈ classifiedEncodingClauses (s.val + 4) := by
  have hChecked :
      ∀ s : Fin 6, checkClassifiedEncoding (s.val + 4) = true := by
    decide +native
  have hSorted :
      (reconstructEncoding (s.val + 4)).clauses.toList.mergeSort
          clauseLexLE =
        (classifiedEncodingClauses (s.val + 4)).mergeSort
          clauseLexLE := by
    have h := hChecked s
    simpa only [checkClassifiedEncoding, decide_eq_true_eq] using h
  have hMem :
      clause ∈
          (reconstructEncoding (s.val + 4)).clauses.toList.mergeSort
            clauseLexLE ↔
        clause ∈
          (classifiedEncodingClauses (s.val + 4)).mergeSort
            clauseLexLE := by
    rw [hSorted]
  simpa only [List.mem_mergeSort] using hMem

#eval (List.range 6).map fun s =>
  (s + 4, (classifiedEncodingClauses (s + 4)).length)

#print axioms classified_encoding_membership

end HansonToft
