import ColorCoverCounting

namespace HansonToft

noncomputable def omittedColorList {k : Nat}
    (color : Vertex k → Fin k) (i : Fin 7) : List (Fin k) := by
  classical
  exact if h : ∃ c : Fin k,
      (∀ j, c ≠ color (.cycle j)) ∧
      (∀ a, color (.clique i a) ≠ c)
    then [Classical.choose h] else []

theorem missing_color_mem_omitted_list {k : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) (i : Fin 7) (c : Fin k)
    (hc : ∀ j, c ≠ color (.cycle j))
    (hMissing : ∀ a, color (.clique i a) ≠ c) :
    c ∈ omittedColorList color i := by
  classical
  unfold omittedColorList
  split
  · rename_i hExists
    have hChosen := Classical.choose_spec hExists
    have hEqual := outside_cycle_missing_colors_unique
      hk color hProper i c (Classical.choose hExists)
      hc hChosen.1 hMissing hChosen.2
    simpa only [List.mem_singleton] using hEqual
  · rename_i hNone
    exact False.elim (hNone ⟨c, hc, hMissing⟩)

theorem omittedColorList_length_bound {k : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) (i : Fin 7) :
    (omittedColorList color i).length ≤
      twoColorIndicator (color (.cycle i))
        (color (.cycle (cycleStep i 1)))
        (color (.cycle (cycleStep i 3))) := by
  classical
  unfold omittedColorList
  split
  · rename_i hExists
    have hChosen := Classical.choose_spec hExists
    have hTwo := omission_requires_two_colors
      hk color hProper i (Classical.choose hExists)
      hChosen.1 hChosen.2
    simp [twoColorIndicator, hTwo]
  · simp

def sevenLists {α : Type} (lists : Fin 7 → List α) : List α :=
  lists 0 ++ lists 1 ++ lists 2 ++ lists 3 ++
    lists 4 ++ lists 5 ++ lists 6

theorem mem_sevenLists {α : Type}
    (lists : Fin 7 → List α) (i : Fin 7) (x : α)
    (hx : x ∈ lists i) :
    x ∈ sevenLists lists := by
  have hi := i.isLt
  have hCases :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by
    omega
  rcases hCases with h | h | h | h | h | h | h
  · have heq : i = (0 : Fin 7) := Fin.ext h
    subst i
    simp [sevenLists, hx]
  · have heq : i = (1 : Fin 7) := Fin.ext h
    subst i
    simp [sevenLists, hx]
  · have heq : i = (2 : Fin 7) := Fin.ext h
    subst i
    simp [sevenLists, hx]
  · have heq : i = (3 : Fin 7) := Fin.ext h
    subst i
    simp [sevenLists, hx]
  · have heq : i = (4 : Fin 7) := Fin.ext h
    subst i
    simp [sevenLists, hx]
  · have heq : i = (5 : Fin 7) := Fin.ext h
    subst i
    simp [sevenLists, hx]
  · have heq : i = (6 : Fin 7) := Fin.ext h
    subst i
    simp [sevenLists, hx]

theorem omission_cover_length_bound {k : Nat}
    (hk : 4 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) :
    (sevenLists (omittedColorList color)).length ≤
      cycleTwoColorCount (fun i => color (.cycle i)) := by
  have h0 : (omittedColorList color (0 : Fin 7)).length ≤
      twoColorIndicator (color (.cycle 0))
        (color (.cycle 1)) (color (.cycle 3)) :=
    omittedColorList_length_bound hk color hProper 0
  have h1 : (omittedColorList color (1 : Fin 7)).length ≤
      twoColorIndicator (color (.cycle 1))
        (color (.cycle 2)) (color (.cycle 4)) :=
    omittedColorList_length_bound hk color hProper 1
  have h2 : (omittedColorList color (2 : Fin 7)).length ≤
      twoColorIndicator (color (.cycle 2))
        (color (.cycle 3)) (color (.cycle 5)) :=
    omittedColorList_length_bound hk color hProper 2
  have h3 : (omittedColorList color (3 : Fin 7)).length ≤
      twoColorIndicator (color (.cycle 3))
        (color (.cycle 4)) (color (.cycle 6)) :=
    omittedColorList_length_bound hk color hProper 3
  have h4 : (omittedColorList color (4 : Fin 7)).length ≤
      twoColorIndicator (color (.cycle 4))
        (color (.cycle 5)) (color (.cycle 0)) :=
    omittedColorList_length_bound hk color hProper 4
  have h5 : (omittedColorList color (5 : Fin 7)).length ≤
      twoColorIndicator (color (.cycle 5))
        (color (.cycle 6)) (color (.cycle 1)) :=
    omittedColorList_length_bound hk color hProper 5
  have h6 : (omittedColorList color (6 : Fin 7)).length ≤
      twoColorIndicator (color (.cycle 6))
        (color (.cycle 0)) (color (.cycle 2)) :=
    omittedColorList_length_bound hk color hProper 6
  unfold sevenLists cycleTwoColorCount
  simp only [List.length_append]
  omega

#print axioms omission_cover_length_bound

end HansonToft
