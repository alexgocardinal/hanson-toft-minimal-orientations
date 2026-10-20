import FiniteInjectionBound

namespace HansonToft

theorem disjoint_injections_bound {n r m : Nat}
    (f : Fin n → Fin m) (g : Fin r → Fin m)
    (hf : ∀ a b, f a = f b → a = b)
    (hg : ∀ a b, g a = g b → a = b)
    (hDisjoint : ∀ a b, f a ≠ g b) :
    n + r ≤ m := by
  let joined : Fin (n + r) → Fin m := fun x =>
    if h : x.val < n then
      f ⟨x.val, h⟩
    else
      g ⟨x.val - n, by
        have hx := x.isLt
        omega⟩
  apply finite_injection_bound joined
  intro x y hxy
  have hxBound := x.isLt
  have hyBound := y.isLt
  by_cases hx : x.val < n
  · by_cases hy : y.val < n
    · have heq : f ⟨x.val, hx⟩ = f ⟨y.val, hy⟩ := by
        simpa [joined, hx, hy] using hxy
      have hIndices := hf _ _ heq
      have hValues := congrArg Fin.val hIndices
      apply Fin.ext
      exact hValues
    · have heq :
          f ⟨x.val, hx⟩ =
            g ⟨y.val - n, by omega⟩ := by
        simpa [joined, hx, hy] using hxy
      exact False.elim (hDisjoint _ _ heq)
  · by_cases hy : y.val < n
    · have heq :
          g ⟨x.val - n, by omega⟩ =
            f ⟨y.val, hy⟩ := by
        simpa [joined, hx, hy] using hxy
      exact False.elim (hDisjoint _ _ heq.symm)
    · have heq :
          g ⟨x.val - n, by omega⟩ =
            g ⟨y.val - n, by omega⟩ := by
        simpa [joined, hx, hy] using hxy
      have hIndices := hg _ _ heq
      have hValues := congrArg Fin.val hIndices
      apply Fin.ext
      change x.val - n = y.val - n at hValues
      omega

theorem proper_coloring_requires_k_colors {k m : Nat}
    (hk : 4 ≤ k)
    (color : Vertex k → Fin m)
    (hProper : Proper k m color) :
    k ≤ m := by
  have hCycle : ∀ i : Fin 7,
      color (.cycle i) ≠ color (.cycle (cycleStep i 1)) := by
    intro i
    apply hProper (.cycle i) (.cycle (cycleStep i 1))
    exact Or.inl rfl
  obtain ⟨i, h01, h03, h13⟩ :=
    exists_three_color_triple (fun j => color (.cycle j)) hCycle
  let f : Fin (k - 3) → Fin m :=
    fun a => color (.clique i a)
  let t : Fin 3 → Fin m := fun j =>
    if j.val = 0 then color (.cycle i)
    else if j.val = 1 then color (.cycle (cycleStep i 1))
    else color (.cycle (cycleStep i 3))
  have hf : ∀ a b, f a = f b → a = b := by
    intro a b heq
    apply Classical.byContradiction
    intro hab
    exact hProper (.clique i a) (.clique i b)
      ⟨rfl, hab⟩ heq
  have ht : ∀ a b, t a = t b → a = b := by
    have hCases : ∀ j : Fin 3,
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by
      intro j
      have hj := j.isLt
      omega
    intro a b heq
    rcases hCases a with ha | ha | ha <;>
      rcases hCases b with hb | hb | hb
    · have haEq : a = (0 : Fin 3) := Fin.ext ha
      have hbEq : b = (0 : Fin 3) := Fin.ext hb
      subst a
      subst b
      rfl
    · have haEq : a = (0 : Fin 3) := Fin.ext ha
      have hbEq : b = (1 : Fin 3) := Fin.ext hb
      subst a
      subst b
      exact False.elim (h01 heq)
    · have haEq : a = (0 : Fin 3) := Fin.ext ha
      have hbEq : b = (2 : Fin 3) := Fin.ext hb
      subst a
      subst b
      exact False.elim (h03 heq)
    · have haEq : a = (1 : Fin 3) := Fin.ext ha
      have hbEq : b = (0 : Fin 3) := Fin.ext hb
      subst a
      subst b
      exact False.elim (h01 heq.symm)
    · have haEq : a = (1 : Fin 3) := Fin.ext ha
      have hbEq : b = (1 : Fin 3) := Fin.ext hb
      subst a
      subst b
      rfl
    · have haEq : a = (1 : Fin 3) := Fin.ext ha
      have hbEq : b = (2 : Fin 3) := Fin.ext hb
      subst a
      subst b
      exact False.elim (h13 heq)
    · have haEq : a = (2 : Fin 3) := Fin.ext ha
      have hbEq : b = (0 : Fin 3) := Fin.ext hb
      subst a
      subst b
      exact False.elim (h03 heq.symm)
    · have haEq : a = (2 : Fin 3) := Fin.ext ha
      have hbEq : b = (1 : Fin 3) := Fin.ext hb
      subst a
      subst b
      exact False.elim (h13 heq.symm)
    · have haEq : a = (2 : Fin 3) := Fin.ext ha
      have hbEq : b = (2 : Fin 3) := Fin.ext hb
      subst a
      subst b
      rfl
  have hAttach0 : ∀ a : Fin (k - 3),
      f a ≠ color (.cycle i) := by
    intro a
    apply hProper (.clique i a) (.cycle i)
    exact Or.inl rfl
  have hAttach1 : ∀ a : Fin (k - 3),
      f a ≠ color (.cycle (cycleStep i 1)) := by
    intro a
    apply hProper (.clique i a) (.cycle (cycleStep i 1))
    exact Or.inr (Or.inl rfl)
  have hAttach3 : ∀ a : Fin (k - 3),
      f a ≠ color (.cycle (cycleStep i 3)) := by
    intro a
    apply hProper (.clique i a) (.cycle (cycleStep i 3))
    exact Or.inr (Or.inr rfl)
  have hDisjoint : ∀ a b, f a ≠ t b := by
    intro a b
    dsimp only [t]
    split
    · exact hAttach0 a
    · split
      · exact hAttach1 a
      · exact hAttach3 a
  have hBound := disjoint_injections_bound f t hf ht hDisjoint
  omega

theorem no_k_minus_one_coloring {k : Nat} (hk : 4 ≤ k) :
    ∀ color : Vertex k → Fin (k - 1),
      ¬ Proper k (k - 1) color := by
  intro color hProper
  have hBound := proper_coloring_requires_k_colors hk color hProper
  omega

#print axioms proper_coloring_requires_k_colors
#print axioms no_k_minus_one_coloring

end HansonToft
