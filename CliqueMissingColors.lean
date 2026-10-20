import CycleCountingBounds

namespace HansonToft

theorem clique_missing_colors_bound {k r : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) (i : Fin 7)
    (extras : Fin r → Fin k)
    (hExtras : ∀ a b, extras a = extras b → a = b)
    (hAvoid : ∀ a b, color (.clique i a) ≠ extras b) :
    r ≤ 3 := by
  have hClique :
      ∀ a b : Fin (k - 3),
        color (.clique i a) = color (.clique i b) → a = b := by
    intro a b heq
    apply Classical.byContradiction
    intro hab
    exact hProper (.clique i a) (.clique i b) ⟨rfl, hab⟩ heq
  have hBound := disjoint_injections_bound
    (fun a => color (.clique i a)) extras hClique hExtras hAvoid
  omega

def fourColorMap {α : Type} (a b c d : α) (j : Fin 4) : α :=
  if j.val = 0 then a
  else if j.val = 1 then b
  else if j.val = 2 then c
  else d

theorem fourColorMap_injective {α : Type}
    (a b c d : α)
    (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d)
    (h12 : b ≠ c) (h13 : b ≠ d) (h23 : c ≠ d) :
    ∀ x y, fourColorMap a b c d x =
      fourColorMap a b c d y → x = y := by
  have hCases : ∀ j : Fin 4,
      j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
    intro j
    have hj := j.isLt
    omega
  intro x y heq
  rcases hCases x with hx | hx | hx | hx <;>
    rcases hCases y with hy | hy | hy | hy
  · have hxEq : x = (0 : Fin 4) := Fin.ext hx
    have hyEq : y = (0 : Fin 4) := Fin.ext hy
    subst x
    subst y
    rfl
  · have hxEq : x = (0 : Fin 4) := Fin.ext hx
    have hyEq : y = (1 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h01 heq)
  · have hxEq : x = (0 : Fin 4) := Fin.ext hx
    have hyEq : y = (2 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h02 heq)
  · have hxEq : x = (0 : Fin 4) := Fin.ext hx
    have hyEq : y = (3 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h03 heq)
  · have hxEq : x = (1 : Fin 4) := Fin.ext hx
    have hyEq : y = (0 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h01 heq.symm)
  · have hxEq : x = (1 : Fin 4) := Fin.ext hx
    have hyEq : y = (1 : Fin 4) := Fin.ext hy
    subst x
    subst y
    rfl
  · have hxEq : x = (1 : Fin 4) := Fin.ext hx
    have hyEq : y = (2 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h12 heq)
  · have hxEq : x = (1 : Fin 4) := Fin.ext hx
    have hyEq : y = (3 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h13 heq)
  · have hxEq : x = (2 : Fin 4) := Fin.ext hx
    have hyEq : y = (0 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h02 heq.symm)
  · have hxEq : x = (2 : Fin 4) := Fin.ext hx
    have hyEq : y = (1 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h12 heq.symm)
  · have hxEq : x = (2 : Fin 4) := Fin.ext hx
    have hyEq : y = (2 : Fin 4) := Fin.ext hy
    subst x
    subst y
    rfl
  · have hxEq : x = (2 : Fin 4) := Fin.ext hx
    have hyEq : y = (3 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h23 heq)
  · have hxEq : x = (3 : Fin 4) := Fin.ext hx
    have hyEq : y = (0 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h03 heq.symm)
  · have hxEq : x = (3 : Fin 4) := Fin.ext hx
    have hyEq : y = (1 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h13 heq.symm)
  · have hxEq : x = (3 : Fin 4) := Fin.ext hx
    have hyEq : y = (2 : Fin 4) := Fin.ext hy
    subst x
    subst y
    exact False.elim (h23 heq.symm)
  · have hxEq : x = (3 : Fin 4) := Fin.ext hx
    have hyEq : y = (3 : Fin 4) := Fin.ext hy
    subst x
    subst y
    rfl

theorem four_colors_not_all_missing {k : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) (i : Fin 7)
    (a b c d : Fin k)
    (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d)
    (h12 : b ≠ c) (h13 : b ≠ d) (h23 : c ≠ d)
    (ha : ∀ x, color (.clique i x) ≠ a)
    (hb : ∀ x, color (.clique i x) ≠ b)
    (hc : ∀ x, color (.clique i x) ≠ c)
    (hd : ∀ x, color (.clique i x) ≠ d) :
    False := by
  have hAvoid :
      ∀ x j, color (.clique i x) ≠ fourColorMap a b c d j := by
    intro x j
    have hj := j.isLt
    have hCases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
      omega
    rcases hCases with h | h | h | h
    · have heq : j = (0 : Fin 4) := Fin.ext h
      subst j
      exact ha x
    · have heq : j = (1 : Fin 4) := Fin.ext h
      subst j
      exact hb x
    · have heq : j = (2 : Fin 4) := Fin.ext h
      subst j
      exact hc x
    · have heq : j = (3 : Fin 4) := Fin.ext h
      subst j
      exact hd x

  have hBound := clique_missing_colors_bound hk color hProper i
    (fourColorMap a b c d)
    (fourColorMap_injective a b c d h01 h02 h03 h12 h13 h23)
    hAvoid
  omega

theorem three_color_triple_forces_clique {k : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) (i : Fin 7)
    (h01 : color (.cycle i) ≠ color (.cycle (cycleStep i 1)))
    (h03 : color (.cycle i) ≠ color (.cycle (cycleStep i 3)))
    (h13 : color (.cycle (cycleStep i 1)) ≠
      color (.cycle (cycleStep i 3)))
    (c : Fin k)
    (hc0 : c ≠ color (.cycle i))
    (hc1 : c ≠ color (.cycle (cycleStep i 1)))
    (hc3 : c ≠ color (.cycle (cycleStep i 3))) :
    ∃ a, color (.clique i a) = c := by
  apply Classical.byContradiction
  intro hMissing
  apply four_colors_not_all_missing hk color hProper i
    (color (.cycle i))
    (color (.cycle (cycleStep i 1)))
    (color (.cycle (cycleStep i 3))) c
    h01 h03 (Ne.symm hc0) h13 (Ne.symm hc1) (Ne.symm hc3)
  · intro a
    apply hProper (.clique i a) (.cycle i)
    exact Or.inl rfl
  · intro a
    apply hProper (.clique i a) (.cycle (cycleStep i 1))
    exact Or.inr (Or.inl rfl)
  · intro a
    apply hProper (.clique i a) (.cycle (cycleStep i 3))
    exact Or.inr (Or.inr rfl)
  · intro a heq
    exact hMissing ⟨a, heq⟩

#print axioms three_color_triple_forces_clique

end HansonToft
