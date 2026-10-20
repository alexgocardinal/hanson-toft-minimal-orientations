import AttachmentEdgeDeletion

namespace HansonToft

def collapseIndex {m : Nat}
    (a b : Fin (m + 2)) (hab : a ≠ b)
    (x : Fin (m + 2)) : Fin (m + 1) :=
  if hx : x = b then compressColor b a hab
  else compressColor b x hx

theorem collapseIndex_expand {m : Nat}
    (a b : Fin (m + 2)) (hab : a ≠ b)
    (x : Fin (m + 2)) :
    expandColor b (collapseIndex a b hab x) =
      if x = b then a else x := by
  by_cases hx : x = b
  · simpa [collapseIndex, hx] using expand_compress_color b a hab
  · simpa [collapseIndex, hx] using expand_compress_color b x hx

theorem collapseIndex_conflict {m : Nat}
    (a b : Fin (m + 2)) (hab : a ≠ b)
    (x y : Fin (m + 2))
    (hEqual : collapseIndex a b hab x = collapseIndex a b hab y) :
    x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hRep :
      (if x = b then a else x) = (if y = b then a else y) := by
    calc
      (if x = b then a else x) =
          expandColor b (collapseIndex a b hab x) :=
        (collapseIndex_expand a b hab x).symm
      _ = expandColor b (collapseIndex a b hab y) :=
        congrArg (expandColor b) hEqual
      _ = (if y = b then a else y) :=
        collapseIndex_expand a b hab y
  by_cases hx : x = b
  · by_cases hy : y = b
    · exact Or.inl (hx.trans hy.symm)
    · have hay : a = y := by simpa [hx, hy] using hRep
      exact Or.inr (Or.inr ⟨hx, hay.symm⟩)
  · by_cases hy : y = b
    · have hxa : x = a := by simpa [hx, hy] using hRep
      exact Or.inr (Or.inl ⟨hxa, hy⟩)
    · exact Or.inl (by simpa [hx, hy] using hRep)

def internalEdgeColor {m : Nat}
    (e : Fin 7) (a b : Fin (m + 2)) (hab : a ≠ b) :
    Vertex (m + 5) → Fin (m + 4)
  | .cycle x =>
      ⟨(exceptionalCycleColor e x).val, by
        have h := (exceptionalCycleColor e x).isLt
        omega⟩
  | .clique j x =>
      if j = e then
        ⟨(collapseIndex a b hab x).val + 3, by
          have h := (collapseIndex a b hab x).isLt
          omega⟩
      else
        cliquePaletteColor (0 : Fin (m + 2))
          (missingTripleColor e j) x

theorem internalEdgeColor_attachment_ne {m : Nat}
    (e : Fin 7) (a b : Fin (m + 2)) (hab : a ≠ b)
    (j z : Fin 7) (x : Fin (m + 2))
    (hAttach : inTriple j z) :
    internalEdgeColor e a b hab (.clique j x) ≠
      internalEdgeColor e a b hab (.cycle z) := by
  intro hEqual
  have hValues := congrArg Fin.val hEqual
  have hLow := (exceptionalCycleColor e z).isLt
  by_cases hj : j = e
  · have hv :
        (collapseIndex a b hab x).val + 3 =
          (exceptionalCycleColor e z).val := by
      simpa [internalEdgeColor, hj] using hValues
    omega
  · by_cases hx : x = (0 : Fin (m + 2))
    · have hv :
          (missingTripleColor e j).val =
            (exceptionalCycleColor e z).val := by
        simpa [internalEdgeColor, hj, cliquePaletteColor, hx] using hValues
      apply missingTripleColor_available e j z hj hAttach
      apply Fin.ext
      exact hv
    · have hHigh := cliquePaletteColor_high
        (0 : Fin (m + 2)) (missingTripleColor e j) x hx
      have hv :
          (cliquePaletteColor (0 : Fin (m + 2))
            (missingTripleColor e j) x).val =
          (exceptionalCycleColor e z).val := by
        simpa [internalEdgeColor, hj] using hValues
      omega

theorem internalEdgeColor_proper {m : Nat}
    (e : Fin 7) (a b : Fin (m + 2)) (hab : a ≠ b) :
    ProperWithoutEdge (m + 5) (m + 4)
      (.clique e a) (.clique e b) (internalEdgeColor e a b hab) := by
  intro u v hAdj hKeep hEqual
  cases u with
  | cycle i =>
      cases v with
      | cycle j =>
          apply exceptionalCycleColor_proper e i j hAdj
          have hValues := congrArg Fin.val hEqual
          apply Fin.ext
          exact hValues
      | clique j y =>
          exact internalEdgeColor_attachment_ne e a b hab j i y
            hAdj hEqual.symm
  | clique i x =>
      cases v with
      | cycle j =>
          exact internalEdgeColor_attachment_ne e a b hab i j x
            hAdj hEqual
      | clique j y =>
          obtain ⟨hij, hDifferent⟩ := hAdj
          subst j
          by_cases hi : i = e
          · subst i
            have hValues :
                (collapseIndex a b hab x).val + 3 =
                  (collapseIndex a b hab y).val + 3 := by
              simpa [internalEdgeColor] using congrArg Fin.val hEqual
            have hCompressed :
                collapseIndex a b hab x = collapseIndex a b hab y := by
              apply Fin.ext
              omega
            rcases collapseIndex_conflict a b hab x y hCompressed with
              hxy | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hDifferent hxy
            · exact hKeep (Or.inl ⟨rfl, rfl⟩)
            · exact hKeep (Or.inr ⟨rfl, rfl⟩)
          · have hPalette :
                cliquePaletteColor (0 : Fin (m + 2))
                  (missingTripleColor e i) x =
                cliquePaletteColor (0 : Fin (m + 2))
                  (missingTripleColor e i) y := by
              simpa [internalEdgeColor, hi] using hEqual
            exact hDifferent
              (cliquePaletteColor_injective
                (0 : Fin (m + 2)) (missingTripleColor e i) x y hPalette)

theorem internal_edge_deletion_colorable {m : Nat}
    (e : Fin 7) (a b : Fin (m + 2)) (hab : a ≠ b) :
    ∃ color : Vertex (m + 5) → Fin (m + 4),
      ProperWithoutEdge (m + 5) (m + 4)
        (.clique e a) (.clique e b) color := by
  exact ⟨internalEdgeColor e a b hab,
    internalEdgeColor_proper e a b hab⟩

#print axioms internal_edge_deletion_colorable

end HansonToft
