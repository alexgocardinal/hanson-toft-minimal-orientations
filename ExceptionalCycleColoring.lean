import CycleEdgeDeletion

set_option maxHeartbeats 2000000

namespace HansonToft

def exceptionalBaseColor (i : Fin 7) : Fin 3 :=
  if i.val = 3 then 2
  else if i.val = 1 ∨ i.val = 4 ∨ i.val = 6 then 1
  else 0

def exceptionalCycleColor (e x : Fin 7) : Fin 3 :=
  exceptionalBaseColor
    ⟨(x.val + 7 - e.val) % 7, Nat.mod_lt _ (by decide)⟩

def missingTripleColor (e j : Fin 7) : Fin 3 :=
  if exceptionalCycleColor e j ≠ 0 ∧
      exceptionalCycleColor e (cycleStep j 1) ≠ 0 ∧
      exceptionalCycleColor e (cycleStep j 3) ≠ 0 then 0
  else if exceptionalCycleColor e j ≠ 1 ∧
      exceptionalCycleColor e (cycleStep j 1) ≠ 1 ∧
      exceptionalCycleColor e (cycleStep j 3) ≠ 1 then 1
  else 2

theorem exceptionalCycleColor_proper :
    ∀ e i j : Fin 7,
      ((i.val + 1) % 7 = j.val ∨
        (j.val + 1) % 7 = i.val) →
      exceptionalCycleColor e i ≠ exceptionalCycleColor e j := by
  decide

theorem exceptional_triple_colors_injective :
    ∀ e x y : Fin 7,
      inTriple e x → inTriple e y →
      exceptionalCycleColor e x = exceptionalCycleColor e y →
      x = y := by
  unfold inTriple
  decide

theorem missingTripleColor_available :
    ∀ e j x : Fin 7,
      j ≠ e → inTriple j x →
      missingTripleColor e j ≠ exceptionalCycleColor e x := by
  unfold inTriple
  decide

#print axioms exceptionalCycleColor_proper
#print axioms exceptional_triple_colors_injective
#print axioms missingTripleColor_available

end HansonToft
