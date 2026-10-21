import CommonColor

namespace HansonToft

/-- These are graph-theoretic base cases, not merely CNF unsatisfiability. -/
def TwoPathBases : Prop :=
  ∀ k : Nat, 4 ≤ k → k ≤ 9 →
    ∀ color : Vertex k → Fin k,
      Proper k k color → HasTwoFullPaths k color

theorem two_paths_family_of_bases (hBases : TwoPathBases) :
    ∀ k : Nat, 4 ≤ k →
      ∀ color : Vertex k → Fin k,
        Proper k k color → HasTwoFullPaths k color := by
  intro k
  refine Nat.strongRecOn (motive := fun n =>
    4 ≤ n → ∀ color : Vertex n → Fin n,
      Proper n n color → HasTwoFullPaths n color) k ?_
  intro n ih hn color hProper
  by_cases hSmall : n ≤ 9
  · exact hBases n hn hSmall color hProper
  · have hLarge : 10 ≤ n := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 :=
      ⟨n - 4, by omega⟩
    apply uniform_two_path_step hLarge ?_ color hProper
    intro d hd
    exact ih (m + 3) (by omega) (by omega) d hd

theorem two_paths_exclude_unique {k : Nat}
    (color : Vertex k → Fin k)
    (hTwo : HasTwoFullPaths k color) :
    ¬ HasUniqueFullPath k color := by
  obtain ⟨p, q, hp, hq, hDifferent⟩ := hTwo
  intro hUnique
  obtain ⟨r, hr, hOnly⟩ := hUnique
  exact hDifferent ((hOnly p hp).trans (hOnly q hq).symm)

theorem familyStatement_of_two_path_bases
    (hBases : TwoPathBases) : familyStatement := by
  intro k hk color hProper
  exact two_paths_exclude_unique color
    (two_paths_family_of_bases hBases k hk color hProper)

#print axioms two_paths_family_of_bases
#print axioms familyStatement_of_two_path_bases

end HansonToft
