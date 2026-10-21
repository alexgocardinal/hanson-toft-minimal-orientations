import NumericGraphBridge
import Std.Sat.CNF.Sat

namespace HansonToft

def HoldsClause (assignment : Nat → Bool)
    (literals : List (Nat × Bool)) : Prop :=
  Std.Sat.CNF.Clause.Sat assignment
    (Std.Sat.CNF.Clause.ofLiterals literals)

theorem holdsClause_iff (assignment : Nat → Bool)
    (literals : List (Nat × Bool)) :
    HoldsClause assignment literals ↔
      ∃ literal ∈ literals, assignment literal.1 = literal.2 := by
  simp only [HoldsClause,
    Std.Sat.CNF.Clause.sat_iff_exists_mem_eq,
    ← Std.Sat.CNF.Clause.mem_literals_iff,
    Std.Sat.CNF.Clause.literals_ofLiterals]

theorem holdsClause_one (assignment : Nat → Bool)
    (x : Nat) (p : Bool) :
    HoldsClause assignment [(x, p)] ↔ assignment x = p := by
  simp [holdsClause_iff]

theorem holdsClause_two (assignment : Nat → Bool)
    (x y : Nat) (p q : Bool) :
    HoldsClause assignment [(x, p), (y, q)] ↔
      assignment x = p ∨ assignment y = q := by
  simp [holdsClause_iff]

theorem holdsClause_three (assignment : Nat → Bool)
    (x y z : Nat) (p q r : Bool) :
    HoldsClause assignment [(x, p), (y, q), (z, r)] ↔
      assignment x = p ∨ assignment y = q ∨ assignment z = r := by
  simp [holdsClause_iff]

theorem and_gate_semantics (assignment : Nat → Bool)
    (x y z : Nat) :
    (HoldsClause assignment [(z, false), (x, true)] ∧
      HoldsClause assignment [(z, false), (y, true)] ∧
      HoldsClause assignment [(z, true), (x, false), (y, false)]) ↔
    assignment z = (assignment x && assignment y) := by
  simp only [holdsClause_two, holdsClause_three]
  cases hx : assignment x <;>
    cases hy : assignment y <;>
    cases hz : assignment z <;>
    simp_all

theorem equivalence_gate_semantics (assignment : Nat → Bool)
    (x z : Nat) :
    (HoldsClause assignment [(x, false), (z, true)] ∧
      HoldsClause assignment [(z, false), (x, true)]) ↔
    assignment x = assignment z := by
  simp only [holdsClause_two]
  cases hx : assignment x <;>
    cases hz : assignment z <;>
    simp_all

#print axioms and_gate_semantics
#print axioms equivalence_gate_semantics

end HansonToft
