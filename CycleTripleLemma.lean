import TwoPathReduction

namespace HansonToft

theorem seven_cycle_triples_contradiction {α : Type}
    (x0 x1 x2 x3 x4 x5 x6 : α)
    (hEdge0 : x0 ≠ x1)
    (hEdge1 : x1 ≠ x2)
    (hEdge2 : x2 ≠ x3)
    (hEdge3 : x3 ≠ x4)
    (hEdge4 : x4 ≠ x5)
    (hEdge5 : x5 ≠ x6)
    (hEdge6 : x6 ≠ x0)
    (hTriple0 : x3 = x0 ∨ x3 = x1)
    (hTriple1 : x4 = x1 ∨ x4 = x2)
    (hTriple2 : x5 = x2 ∨ x5 = x3)
    (hTriple3 : x6 = x3 ∨ x6 = x4)
    (hTriple4 : x0 = x4 ∨ x0 = x5)
    (hTriple5 : x1 = x5 ∨ x1 = x6)
    (hTriple6 : x2 = x6 ∨ x2 = x0)
    : False := by
  rcases hTriple0 with hTriple0 | hTriple0
  · rcases hTriple1 with hTriple1 | hTriple1
    · rcases hTriple2 with hTriple2 | hTriple2
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple2)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge2 ((hTriple6).trans (hTriple0.symm))
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge1 ((hTriple5).trans (hTriple6.symm))
              · exact hEdge2 ((hTriple6).trans (hTriple0.symm))
    · rcases hTriple2 with hTriple2 | hTriple2
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple1)).trans (hTriple2.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple6.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple1)).trans (hTriple2.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple6.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple2)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge0 ((((hTriple6.symm).trans (hTriple1.symm)).trans (hTriple3.symm)).trans (hTriple5.symm))
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple3.symm)).trans (hTriple5.symm))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple0.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple0.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge1 ((hTriple5).trans (hTriple6.symm))
              · exact hEdge0 ((((hTriple6.symm).trans (hTriple1.symm)).trans (hTriple3.symm)).trans (hTriple5.symm))
  · rcases hTriple1 with hTriple1 | hTriple1
    · rcases hTriple2 with hTriple2 | hTriple2
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple2)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge3 ((hTriple0).trans (hTriple1.symm))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple2)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge3 ((hTriple0).trans (hTriple1.symm))
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple1))
              · exact hEdge0 ((hTriple4).trans (hTriple1))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
    · rcases hTriple2 with hTriple2 | hTriple2
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple1)).trans (hTriple2.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple6.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple1)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge4 ((hTriple1).trans (hTriple2.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple2)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge4 ((hTriple1).trans (hTriple2.symm))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple1)).trans (hTriple2.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple6.symm).trans (hTriple2.symm)).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple2)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge0 ((((hTriple6.symm).trans (hTriple1.symm)).trans (hTriple3.symm)).trans (hTriple5.symm))
      · rcases hTriple3 with hTriple3 | hTriple3
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((((hTriple4).trans (hTriple1)).trans (hTriple6)).trans (hTriple3)).trans (hTriple0))
              · exact hEdge5 ((hTriple2).trans (hTriple3.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((((hTriple4).trans (hTriple1)).trans (hTriple6)).trans (hTriple5.symm))
              · exact hEdge5 ((hTriple2).trans (hTriple3.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
        · rcases hTriple4 with hTriple4 | hTriple4
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge6 ((hTriple3).trans (hTriple4.symm))
              · exact hEdge6 ((hTriple3).trans (hTriple4.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
              · exact hEdge0 (((hTriple4).trans (hTriple3.symm)).trans (hTriple5.symm))
          · rcases hTriple5 with hTriple5 | hTriple5
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
              · exact hEdge0 ((hTriple4).trans (hTriple5.symm))
            · rcases hTriple6 with hTriple6 | hTriple6
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
              · exact hEdge0 (((hTriple4).trans (hTriple2)).trans (hTriple0))
  
def cycleStep (i : Fin 7) (s : Nat) : Fin 7 :=
  ⟨(i.val + s) % 7, Nat.mod_lt _ (by decide)⟩

theorem exists_three_color_triple {α : Type}
    (color : Fin 7 → α)
    (hCycle : ∀ i, color i ≠ color (cycleStep i 1)) :
    ∃ i, color i ≠ color (cycleStep i 1) ∧
      color i ≠ color (cycleStep i 3) ∧
      color (cycleStep i 1) ≠ color (cycleStep i 3) := by
  classical
  apply Classical.byContradiction
  intro hNone
  have hBichromatic : ∀ i,
      color (cycleStep i 3) = color i ∨
      color (cycleStep i 3) = color (cycleStep i 1) := by
    intro i
    by_cases h0 : color (cycleStep i 3) = color i
    · exact Or.inl h0
    · right
      apply Classical.byContradiction
      intro h1
      exact hNone ⟨i, hCycle i,
        (fun h => h0 h.symm), (fun h => h1 h.symm)⟩
  apply seven_cycle_triples_contradiction
    (color 0) (color 1) (color 2) (color 3)
    (color 4) (color 5) (color 6)
  · exact hCycle (0 : Fin 7)
  · exact hCycle (1 : Fin 7)
  · exact hCycle (2 : Fin 7)
  · exact hCycle (3 : Fin 7)
  · exact hCycle (4 : Fin 7)
  · exact hCycle (5 : Fin 7)
  · exact hCycle (6 : Fin 7)
  · exact hBichromatic (0 : Fin 7)
  · exact hBichromatic (1 : Fin 7)
  · exact hBichromatic (2 : Fin 7)
  · exact hBichromatic (3 : Fin 7)
  · exact hBichromatic (4 : Fin 7)
  · exact hBichromatic (5 : Fin 7)
  · exact hBichromatic (6 : Fin 7)

#print axioms seven_cycle_triples_contradiction
#print axioms exists_three_color_triple

end HansonToft
