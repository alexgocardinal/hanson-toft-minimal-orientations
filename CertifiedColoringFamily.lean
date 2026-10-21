import FullPathExistence
import FamilyInduction
import ChromaticLowerBound

namespace HansonToft

theorem full_path_exists_for_family {k : Nat}
    (hk : 4 ≤ k)
    (color : Vertex k → Fin k)
    (hProper : Proper k k color) :
    ∃ p, FullIncreasingPath k color p := by
  exact full_path_exists_of_no_smaller_coloring
    (by omega) color hProper
    (fun d => no_k_minus_one_coloring hk d)

theorem two_full_paths_of_exists_and_not_unique {k : Nat}
    (color : Vertex k → Fin k)
    (hExists : ∃ p, FullIncreasingPath k color p)
    (hNotUnique : ¬ HasUniqueFullPath k color) :
    HasTwoFullPaths k color := by
  classical
  obtain ⟨p, hp⟩ := hExists
  have hOther :
      ∃ q, FullIncreasingPath k color q ∧ q ≠ p := by
    apply Classical.byContradiction
    intro hNone
    apply hNotUnique
    refine ⟨p, hp, ?_⟩
    intro q hq
    apply Classical.byContradiction
    intro hDifferent
    exact hNone ⟨q, hq, hDifferent⟩
  obtain ⟨q, hq, hDifferent⟩ := hOther
  refine ⟨p, q, hp, hq, ?_⟩
  intro hEqual
  exact hDifferent hEqual.symm

theorem certified_two_path_bases : TwoPathBases := by
  intro k hk hUpper color hProper
  have hExists := full_path_exists_for_family hk color hProper
  apply two_full_paths_of_exists_and_not_unique color hExists
  obtain ⟨m, rfl⟩ : ∃ m : Nat, k = m + 4 :=
    ⟨k - 4, by omega⟩
  let s : Fin 6 := ⟨m, by omega⟩
  exact small_coloring_has_no_unique_path s color hProper

theorem certified_two_paths_family
    (k : Nat) (hk : 4 ≤ k)
    (color : Vertex k → Fin k)
    (hProper : Proper k k color) :
    HasTwoFullPaths k color := by
  exact two_paths_family_of_bases
    certified_two_path_bases k hk color hProper

theorem certified_coloring_family_statement : familyStatement := by
  exact familyStatement_of_two_path_bases certified_two_path_bases

#print axioms certified_two_path_bases
#print axioms certified_two_paths_family
#print axioms certified_coloring_family_statement

end HansonToft
