import OmissionCover

namespace HansonToft

theorem common_color_exists {k : Nat}
    (hk : 10 ≤ k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) :
    ∃ c : Fin k,
      (∀ i, c ≠ color (.cycle i)) ∧
      (∀ i, ∃ a, color (.clique i a) = c) := by
  classical
  have hk4 : 4 ≤ k := by omega
  let cycleColors : List (Fin k) :=
    [color (.cycle 0), color (.cycle 1), color (.cycle 2),
      color (.cycle 3), color (.cycle 4), color (.cycle 5),
      color (.cycle 6)]
  let bad : List (Fin k) :=
    uniqueColors cycleColors ++ sevenLists (omittedColorList color)
  have hCycle : ∀ i : Fin 7,
      color (.cycle i) ≠ color (.cycle (cycleStep i 1)) := by
    intro i
    apply hProper (.cycle i) (.cycle (cycleStep i 1))
    exact Or.inl rfl
  have hCycleLength :
      (uniqueColors cycleColors).length =
        cycleClassCount (fun i => color (.cycle i)) := by
    simpa only [cycleClassCount, cycleColors] using
      uniqueColors_length cycleColors
  have hLength : bad.length ≤ 9 := by
    have hOmit := omission_cover_length_bound hk4 color hProper
    have hCount :=
      (cycle_counting_bounds (fun i => color (.cycle i)) hCycle).2
    have hLengthEq :
        bad.length = (uniqueColors cycleColors).length +
          (sevenLists (omittedColorList color)).length := by
      exact List.length_append
    rw [hCycleLength] at hLengthEq
    omega
  have hNotCovered : ∃ c : Fin k, c ∉ bad := by
    apply Classical.byContradiction
    intro hNone
    have hCover : ∀ c : Fin k, c ∈ bad := by
      intro c
      apply Classical.byContradiction
      intro hc
      exact hNone ⟨c, hc⟩
    have hBound := finite_palette_covered_by_list bad hCover
    omega
  obtain ⟨c, hc⟩ := hNotCovered
  have hCycleMem : ∀ i : Fin 7, color (.cycle i) ∈ cycleColors := by
    intro i
    have hm := mem_sevenLists
      (fun j => [color (.cycle j)]) i (color (.cycle i)) (by simp)
    simpa [sevenLists, cycleColors] using hm
  have hOutside : ∀ i, c ≠ color (.cycle i) := by
    intro i heq
    apply hc
    apply List.mem_append.mpr
    left
    apply (mem_uniqueColors c cycleColors).mpr
    rw [heq]
    exact hCycleMem i
  refine ⟨c, hOutside, ?_⟩
  intro i
  apply Classical.byContradiction
  intro hMissing
  have hMiss : ∀ a, color (.clique i a) ≠ c := by
    intro a heq
    exact hMissing ⟨a, heq⟩
  have hMem := missing_color_mem_omitted_list
    hk4 color hProper i c hOutside hMiss
  apply hc
  exact List.mem_append.mpr
    (Or.inr (mem_sevenLists (omittedColorList color) i c hMem))

theorem common_color_with_selected_vertices {m : Nat}
    (hk : 10 ≤ m + 4)
    (color : Vertex (m + 4) → Fin (m + 4))
    (hProper : Proper (m + 4) (m + 4) color) :
    ∃ (c : Fin (m + 4)) (removed : Fin 7 → Fin (m + 1)),
      (∀ i, color (.cycle i) ≠ c) ∧
      (∀ i, color (deletedVertex removed i) = c) := by
  classical
  obtain ⟨c, hOutside, hEach⟩ := common_color_exists hk color hProper
  let removed : Fin 7 → Fin (m + 1) :=
    fun i => Classical.choose (hEach i)
  refine ⟨c, removed, ?_, ?_⟩
  · intro i
    exact Ne.symm (hOutside i)
  · intro i
    change color (.clique i (removed i)) = c
    exact Classical.choose_spec (hEach i)

theorem uniform_two_path_step {m : Nat}
    (hk : 10 ≤ m + 4)
    (hSmall : ∀ d : Vertex (m + 3) → Fin (m + 3),
      Proper (m + 3) (m + 3) d →
        HasTwoFullPaths (m + 3) d) :
    ∀ color : Vertex (m + 4) → Fin (m + 4),
      Proper (m + 4) (m + 4) color →
        HasTwoFullPaths (m + 4) color := by
  intro color hProper
  obtain ⟨c, removed, hCycle, hRemoved⟩ :=
    common_color_with_selected_vertices hk color hProper
  exact two_paths_after_common_color_deletion
    removed color hProper c hCycle hRemoved hSmall

#print axioms common_color_exists
#print axioms uniform_two_path_step

end HansonToft
