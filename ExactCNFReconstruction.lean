import GateProgramSemantics
import CertificateK4
import CertificateK5
import CertificateK6
import CertificateK7
import CertificateK8
import CertificateK9

namespace HansonToft

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure EncodingState where
  next : Nat
  clauses : Array (List (Nat × Bool))
  gates : Array CNFGate

abbrev EncodingBuild := StateM EncodingState

def encodingFresh : EncodingBuild Nat := do
  let state ← get
  set { state with next := state.next + 1 }
  pure state.next

def encodingClause (clause : List (Nat × Bool)) :
    EncodingBuild Unit :=
  modify fun state =>
    { state with clauses := state.clauses.push clause }

def encodingGate (gate : CNFGate) : EncodingBuild Nat := do
  let output ← encodingFresh
  for clause in gateClauses output gate do
    encodingClause clause
  modify fun state =>
    { state with gates := state.gates.push gate }
  pure output

def encodingC (k v rank : Nat) : Nat :=
  v * k + rank

def encodingR (k v rank : Nat) : Nat :=
  registerWidth k + encodingC k v rank

def encodingM (k v rank : Nat) : Nat :=
  registerWidth k + registerWidth k + encodingC k v rank

def buildExactEncoding (k : Nat) : EncodingBuild Unit := do
  let n := 7 * (k - 2)
  let vertices := List.range n

  for v in vertices do
    encodingClause ((List.range k).map fun a => (encodingC k v a, true))
    for a in List.range k do
      for b in List.range k do
        if a < b then
          encodingClause [(encodingC k v a, false),
            (encodingC k v b, false)]

  for u in vertices do
    for v in vertices do
      if u < v ∧ numericAdj k u v then
        for a in List.range k do
          encodingClause [(encodingC k u a, false),
            (encodingC k v a, false)]

  for i in List.range 7 do
    for offset in List.range (k - 4) do
      let u := 7 + i * (k - 3) + offset
      let v := u + 1
      for a in List.range k do
        for b in List.range (a + 1) do
          encodingClause [(encodingC k u a, false),
            (encodingC k v b, false)]

  for offset in List.range 6 do
    let v := offset + 1
    for a in List.range k do
      for b in List.range a do
        encodingClause [(encodingC k 0 a, false),
          (encodingC k v b, false)]

  for v in vertices do
    let neighbors := vertices.filter fun u => decide (numericAdj k v u)
    encodingClause [(encodingR k v 0, false), (encodingC k v 0, true)]
    encodingClause [(encodingC k v 0, false), (encodingR k v 0, true)]
    encodingClause [(encodingM k v 0, false)]

    for offset in List.range (k - 1) do
      let a := offset + 1
      let reach ← encodingGate
        (.orGate (neighbors.map fun u => encodingR k u (a - 1)))
      let r ← encodingGate (.andGate (encodingC k v a) reach)
      encodingClause [(encodingR k v a, false), (r, true)]
      encodingClause [(r, false), (encodingR k v a, true)]

      let mut alternatives :=
        neighbors.map fun u => encodingM k u (a - 1)
      for u in neighbors do
        for w in neighbors do
          if u < w then
            let pair ← encodingGate
              (.andGate (encodingR k u (a - 1))
                (encodingR k w (a - 1)))
            alternatives := alternatives ++ [pair]
      let multi ← encodingGate (.orGate alternatives)
      let m ← encodingGate (.andGate (encodingC k v a) multi)
      encodingClause [(encodingM k v a, false), (m, true)]
      encodingClause [(m, false), (encodingM k v a, true)]

  encodingClause (vertices.map fun v => (encodingR k v (k - 1), true))
  for v in vertices do
    encodingClause [(encodingM k v (k - 1), false)]

  let aux ← (List.range (n - 1)).mapM fun _ => encodingFresh
  encodingClause [(encodingR k 0 (k - 1), false), (aux[0]!, true)]
  for offset in List.range (n - 2) do
    let j := offset + 1
    encodingClause [(aux[j - 1]!, false), (aux[j]!, true)]
    encodingClause [(encodingR k j (k - 1), false),
      (aux[j - 1]!, false)]
    encodingClause [(encodingR k j (k - 1), false), (aux[j]!, true)]
  encodingClause [(encodingR k (n - 1) (k - 1), false),
    (aux[n - 2]!, false)]

  encodingClause
    ((List.range ((k + 1) / 2)).map fun a => (encodingC k 0 a, true))

def reconstructEncoding (k : Nat) : EncodingState :=
  ((buildExactEncoding k).run
    { next := 3 * registerWidth k, clauses := #[], gates := #[] }).2

def archivedEncodingClauses (s : Fin 6) :
    List (List (Nat × Bool)) :=
  let formula :=
    match s.val with
    | 0 => CertificateK4.formula
    | 1 => CertificateK5.formula
    | 2 => CertificateK6.formula
    | 3 => CertificateK7.formula
    | 4 => CertificateK8.formula
    | _ => CertificateK9.formula
  formula.clauses.toList.map fun clause => clause.literals

#eval (List.range 6).map fun s =>
  let k := s + 4
  let result := reconstructEncoding k
  (k, result.next, result.clauses.size)

theorem reconstruction_matches_archives :
    ∀ s : Fin 6,
      (reconstructEncoding (s.val + 4)).clauses.toList =
        archivedEncodingClauses s := by
  decide +native

#print axioms reconstruction_matches_archives

end HansonToft
