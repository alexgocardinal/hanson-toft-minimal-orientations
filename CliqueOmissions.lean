import CliqueMissingColors

namespace HansonToft

theorem outside_cycle_missing_colors_unique {k : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (i : Fin 7) (c d : Fin k)
    (hc : ∀ j, c ≠ color (.cycle j))
    (hd : ∀ j, d ≠ color (.cycle j))
    (hMissingC : ∀ a, color (.clique i a) ≠ c)
    (hMissingD : ∀ a, color (.clique i a) ≠ d) :
    c = d := by
  apply Classical.byContradiction
  intro hcd
  have h01 :
      color (.cycle i) ≠ color (.cycle (cycleStep i 1)) := by
    apply hProper (.cycle i) (.cycle (cycleStep i 1))
    exact Or.inl rfl
  apply four_colors_not_all_missing hk color hProper i
    (color (.cycle i)) (color (.cycle (cycleStep i 1))) c d
    h01 (Ne.symm (hc i)) (Ne.symm (hd i))
    (Ne.symm (hc (cycleStep i 1)))
    (Ne.symm (hd (cycleStep i 1))) hcd
  · intro a
    apply hProper (.clique i a) (.cycle i)
    exact Or.inl rfl
  · intro a
    apply hProper (.clique i a) (.cycle (cycleStep i 1))
    exact Or.inr (Or.inl rfl)
  · exact hMissingC
  · exact hMissingD

theorem omission_requires_two_colors {k : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (i : Fin 7) (c : Fin k)
    (hc : ∀ j, c ≠ color (.cycle j))
    (hMissing : ∀ a, color (.clique i a) ≠ c) :
    color (.cycle (cycleStep i 3)) = color (.cycle i) ∨
    color (.cycle (cycleStep i 3)) =
      color (.cycle (cycleStep i 1)) := by
  by_cases h0 :
      color (.cycle (cycleStep i 3)) = color (.cycle i)
  · exact Or.inl h0
  · right
    apply Classical.byContradiction
    intro h1
    have h01 :
        color (.cycle i) ≠ color (.cycle (cycleStep i 1)) := by
      apply hProper (.cycle i) (.cycle (cycleStep i 1))
      exact Or.inl rfl
    obtain ⟨a, ha⟩ := three_color_triple_forces_clique
      hk color hProper i h01 (Ne.symm h0) (Ne.symm h1)
      c (hc i) (hc (cycleStep i 1)) (hc (cycleStep i 3))
    exact hMissing a ha

theorem clique_color_vertex_unique {k : Nat}
    (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (i : Fin 7) (c : Fin k)
    (a b : Fin (k - 3))
    (ha : color (.clique i a) = c)
    (hb : color (.clique i b) = c) :
    a = b := by
  apply Classical.byContradiction
  intro hab
  exact hProper (.clique i a) (.clique i b)
    ⟨rfl, hab⟩ (ha.trans hb.symm)

#print axioms outside_cycle_missing_colors_unique
#print axioms omission_requires_two_colors

end HansonToft
