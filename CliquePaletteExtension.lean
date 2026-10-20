import ExceptionalCycleColoring

namespace HansonToft

def cliquePaletteColor {n : Nat}
    (chosen : Fin (n + 1)) (low : Fin 3)
    (a : Fin (n + 1)) : Fin (n + 3) :=
  if h : a = chosen then
    ⟨low.val, by
      have hl := low.isLt
      omega⟩
  else
    ⟨(compressColor chosen a h).val + 3, by
      have ha := (compressColor chosen a h).isLt
      omega⟩

theorem cliquePaletteColor_selected {n : Nat}
    (chosen : Fin (n + 1)) (low : Fin 3) :
    (cliquePaletteColor chosen low chosen).val = low.val := by
  simp [cliquePaletteColor]

theorem cliquePaletteColor_high {n : Nat}
    (chosen : Fin (n + 1)) (low : Fin 3)
    (a : Fin (n + 1)) (ha : a ≠ chosen) :
    3 ≤ (cliquePaletteColor chosen low a).val := by
  have hv :
      (cliquePaletteColor chosen low a).val =
        (compressColor chosen a ha).val + 3 := by
    simp [cliquePaletteColor, ha]
  omega

theorem cliquePaletteColor_injective {n : Nat}
    (chosen : Fin (n + 1)) (low : Fin 3) :
    ∀ a b, cliquePaletteColor chosen low a =
      cliquePaletteColor chosen low b → a = b := by
  intro a b hEqual
  by_cases ha : a = chosen
  · subst a
    by_cases hb : b = chosen
    · exact hb.symm
    · have hHigh := cliquePaletteColor_high chosen low b hb
      have hValues := congrArg Fin.val hEqual
      rw [cliquePaletteColor_selected] at hValues
      have hLow := low.isLt
      omega
  · by_cases hb : b = chosen
    · subst b
      have hHigh := cliquePaletteColor_high chosen low a ha
      have hValues := congrArg Fin.val hEqual
      rw [cliquePaletteColor_selected] at hValues
      have hLow := low.isLt
      omega
    · have hValues :
          (compressColor chosen a ha).val + 3 =
            (compressColor chosen b hb).val + 3 := by
        simpa [cliquePaletteColor, ha, hb] using
          congrArg Fin.val hEqual
      have hCompressed :
          compressColor chosen a ha =
            compressColor chosen b hb := by
        apply Fin.ext
        omega
      calc
        a = expandColor chosen (compressColor chosen a ha) :=
          (expand_compress_color chosen a ha).symm
        _ = expandColor chosen (compressColor chosen b hb) :=
          congrArg (expandColor chosen) hCompressed
        _ = b := expand_compress_color chosen b hb

#print axioms cliquePaletteColor_injective

end HansonToft
