import CliquePaletteExtension

namespace HansonToft

def attachmentChosen {m : Nat}
    (e : Fin 7) (y : Fin (m + 1)) (j : Fin 7) : Fin (m + 1) :=
  if j = e then y else ⟨0, by omega⟩

def attachmentLowColor (e target j : Fin 7) : Fin 3 :=
  if j = e then exceptionalCycleColor e target
  else missingTripleColor e j

def attachmentColor {m : Nat}
    (e target : Fin 7) (y : Fin (m + 1)) :
    Vertex (m + 4) → Fin (m + 3)
  | .cycle x =>
      ⟨(exceptionalCycleColor e x).val, by
        have h := (exceptionalCycleColor e x).isLt
        omega⟩
  | .clique j a =>
      cliquePaletteColor
        (attachmentChosen e y j) (attachmentLowColor e target j) a

theorem attachment_color_conflict {m : Nat}
    (e target : Fin 7) (y : Fin (m + 1))
    (hTarget : inTriple e target)
    (j x : Fin 7) (a : Fin (m + 1))
    (hAttach : inTriple j x)
    (hEqual : attachmentColor e target y (.clique j a) =
      attachmentColor e target y (.cycle x)) :
    j = e ∧ a = y ∧ x = target := by
  have hValues := congrArg Fin.val hEqual
  change
    (cliquePaletteColor (attachmentChosen e y j)
      (attachmentLowColor e target j) a).val =
    (exceptionalCycleColor e x).val at hValues
  have ha : a = attachmentChosen e y j := by
    apply Classical.byContradiction
    intro hNot
    have hHigh := cliquePaletteColor_high
      (attachmentChosen e y j) (attachmentLowColor e target j) a hNot
    have hLow := (exceptionalCycleColor e x).isLt
    omega
  subst a
  rw [cliquePaletteColor_selected] at hValues
  have hLowEqual :
      attachmentLowColor e target j = exceptionalCycleColor e x := by
    apply Fin.ext
    exact hValues
  by_cases hj : j = e
  · subst j
    have hx : x = target :=
      exceptional_triple_colors_injective e x target hAttach hTarget
        (by simpa [attachmentLowColor] using hLowEqual.symm)
    refine ⟨rfl, ?_, hx⟩
    simp [attachmentChosen]
  · exact False.elim
      ((missingTripleColor_available e j x hj hAttach)
        (by simpa [attachmentLowColor, hj] using hLowEqual))

theorem attachmentColor_proper {m : Nat}
    (e target : Fin 7) (y : Fin (m + 1))
    (hTarget : inTriple e target) :
    ProperWithoutEdge (m + 4) (m + 3)
      (.clique e y) (.cycle target) (attachmentColor e target y) := by
  intro u v hAdj hKeep hEqual
  cases u with
  | cycle i =>
      cases v with
      | cycle j =>
          apply exceptionalCycleColor_proper e i j hAdj
          have hValues := congrArg Fin.val hEqual
          apply Fin.ext
          exact hValues
      | clique j b =>
          obtain ⟨hj, hb, hi⟩ :=
            attachment_color_conflict e target y hTarget
              j i b hAdj hEqual.symm
          subst j
          subst b
          subst i
          exact hKeep (Or.inr ⟨rfl, rfl⟩)
  | clique i a =>
      cases v with
      | cycle j =>
          obtain ⟨hi, ha, hj⟩ :=
            attachment_color_conflict e target y hTarget
              i j a hAdj hEqual
          subst i
          subst a
          subst j
          exact hKeep (Or.inl ⟨rfl, rfl⟩)
      | clique j b =>
          obtain ⟨hij, hab⟩ := hAdj
          subst j
          exact hab
            (cliquePaletteColor_injective
              (attachmentChosen e y i)
              (attachmentLowColor e target i) a b hEqual)

theorem attachment_edge_deletion_colorable {m : Nat}
    (e target : Fin 7) (y : Fin (m + 1))
    (hTarget : inTriple e target) :
    ∃ color : Vertex (m + 4) → Fin (m + 3),
      ProperWithoutEdge (m + 4) (m + 3)
        (.clique e y) (.cycle target) color := by
  exact ⟨attachmentColor e target y,
    attachmentColor_proper e target y hTarget⟩

#print axioms attachment_edge_deletion_colorable

end HansonToft
