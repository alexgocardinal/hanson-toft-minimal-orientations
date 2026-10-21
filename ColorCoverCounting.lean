import CliqueOmissions

namespace HansonToft

def uniqueColors {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest =>
      if a ∈ rest then uniqueColors rest
      else a :: uniqueColors rest

theorem mem_uniqueColors {α : Type} [DecidableEq α]
    (x : α) (colors : List α) :
    x ∈ uniqueColors colors ↔ x ∈ colors := by
  induction colors with
  | nil =>
      simp [uniqueColors]
  | cons a rest ih =>
      by_cases ha : a ∈ rest
      · simp only [uniqueColors, if_pos ha]
        constructor
        · intro hx
          exact List.mem_cons.mpr (Or.inr (ih.mp hx))
        · intro hx
          rcases List.mem_cons.mp hx with hxa | hx
          · subst x
            exact ih.mpr ha
          · exact ih.mpr hx
      · simp only [uniqueColors, if_neg ha, List.mem_cons, ih]

theorem uniqueColors_length {α : Type} [DecidableEq α]
    (colors : List α) :
    (uniqueColors colors).length = colorClassCount colors := by
  induction colors with
  | nil =>
      rfl
  | cons a rest ih =>
      by_cases ha : a ∈ rest <;>
        simp [uniqueColors, colorClassCount, ha, ih, Nat.add_comm]

theorem color_member_has_index {α : Type}
    (x : α) (colors : List α) :
    x ∈ colors →
      ∃ j : Fin colors.length, colors[j.val]? = some x := by
  induction colors with
  | nil =>
      intro hx
      simp at hx
  | cons a rest ih =>
      intro hx
      rcases List.mem_cons.mp hx with hxa | hx
      · subst x
        exact ⟨⟨0, by simp⟩, rfl⟩
      · obtain ⟨j, hj⟩ := ih hx
        refine ⟨⟨j.val + 1, ?_⟩, ?_⟩
        · have h := j.isLt
          simp only [List.length_cons]
          omega
        · simpa using hj

theorem finite_palette_covered_by_list {k : Nat}
    (colors : List (Fin k))
    (hCover : ∀ c : Fin k, c ∈ colors) :
    k ≤ colors.length := by
  let index : Fin k → Fin colors.length :=
    fun c => Classical.choose (color_member_has_index c colors (hCover c))
  have hIndex : ∀ c, colors[(index c).val]? = some c := by
    intro c
    exact Classical.choose_spec
      (color_member_has_index c colors (hCover c))
  apply finite_injection_bound index
  intro c d heq
  have hSome : some c = some d := by
    calc
      some c = colors[(index c).val]? := (hIndex c).symm
      _ = colors[(index d).val]? :=
        congrArg (fun j : Fin colors.length => colors[j.val]?) heq
      _ = some d := hIndex d
  exact Option.some.inj hSome

#print axioms uniqueColors_length
#print axioms finite_palette_covered_by_list

end HansonToft
