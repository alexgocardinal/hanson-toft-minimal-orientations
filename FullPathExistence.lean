import CliqueSortingNormalization
import FullPathReachability

namespace HansonToft

noncomputable def reachShiftRank {k : Nat}
    (color : Vertex k → Fin k) (v : Vertex k) : Nat := by
  classical
  exact if ReachesRank color (color v).val v then
    (color v).val
  else
    (color v).val - 1

theorem not_reaches_own_rank_positive {k : Nat}
    (color : Vertex k → Fin k) (v : Vertex k)
    (hNot : ¬ ReachesRank color (color v).val v) :
    0 < (color v).val := by
  have hNonzero : (color v).val ≠ 0 := by
    intro hZero
    have hReach : ReachesRank color 0 v :=
      ⟨[v], PrefixPathTo.zero v hZero⟩
    apply hNot
    simpa only [hZero] using hReach
  omega

theorem reaches_own_rank_propagates {k : Nat}
    (color : Vertex k → Fin k) (u v : Vertex k)
    (hEdge : Adj k u v)
    (hNext : (color v).val = (color u).val + 1)
    (hReach : ReachesRank color (color u).val u) :
    ReachesRank color (color v).val v := by
  obtain ⟨p, hp⟩ := hReach
  rw [hNext]
  exact ⟨p ++ [v], PrefixPathTo.step hp v hEdge hNext⟩

theorem reach_shift_coloring {k : Nat}
    (hk : 0 < k)
    (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (hNoPath : ¬ ∃ p, FullIncreasingPath k color p) :
    ∃ d : Vertex k → Fin (k - 1),
      Proper k (k - 1) d := by
  classical
  have hNoFinal :
      ∀ v, ¬ ReachesRank color (k - 1) v := by
    intro v hv
    apply hNoPath
    exact (full_path_exists_iff_final_reachability hk color).mpr ⟨v, hv⟩
  have hBound : ∀ v, reachShiftRank color v < k - 1 := by
    intro v
    have hOriginal := (color v).isLt
    by_cases hReach : ReachesRank color (color v).val v
    · have hNotLast : (color v).val ≠ k - 1 := by
        intro hLast
        apply hNoFinal v
        simpa only [hLast] using hReach
      simp only [reachShiftRank, ite_eq_left hReach]
      omega
    · have hPositive :=
        not_reaches_own_rank_positive color v hReach
      simp only [reachShiftRank, ite_eq_right hReach]
      omega
  let d : Vertex k → Fin (k - 1) :=
    fun v => ⟨reachShiftRank color v, hBound v⟩
  refine ⟨d, ?_⟩
  intro u v hEdge hEqual
  have hValues := congrArg Fin.val hEqual
  change reachShiftRank color u = reachShiftRank color v at hValues
  by_cases hu : ReachesRank color (color u).val u
  · by_cases hv : ReachesRank color (color v).val v
    · simp only [reachShiftRank, ite_eq_left hu,
        ite_eq_left hv] at hValues
      exact hProper u v hEdge (Fin.ext hValues)
    · have hPositive :=
        not_reaches_own_rank_positive color v hv
      simp only [reachShiftRank, ite_eq_left hu,
        ite_eq_right hv] at hValues
      have hNext : (color v).val = (color u).val + 1 := by
        omega
      exact hv (reaches_own_rank_propagates color u v hEdge hNext hu)
  · by_cases hv : ReachesRank color (color v).val v
    · have hPositive :=
        not_reaches_own_rank_positive color u hu
      simp only [reachShiftRank, ite_eq_right hu,
        ite_eq_left hv] at hValues
      have hNext : (color u).val = (color v).val + 1 := by
        omega
      have hBack : Adj k v u :=
        (adj_symmetric k u v).mp hEdge
      exact hu (reaches_own_rank_propagates color v u hBack hNext hv)
    · have huPositive :=
        not_reaches_own_rank_positive color u hu
      have hvPositive :=
        not_reaches_own_rank_positive color v hv
      simp only [reachShiftRank, ite_eq_right hu,
        ite_eq_right hv] at hValues
      apply hProper u v hEdge
      apply Fin.ext
      omega

theorem full_path_exists_of_no_smaller_coloring {k : Nat}
    (hk : 0 < k)
    (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (hLower : ∀ d : Vertex k → Fin (k - 1),
      ¬ Proper k (k - 1) d) :
    ∃ p, FullIncreasingPath k color p := by
  classical
  apply Classical.byContradiction
  intro hNoPath
  obtain ⟨d, hd⟩ := reach_shift_coloring hk color hProper hNoPath
  exact hLower d hd

#print axioms reach_shift_coloring
#print axioms full_path_exists_of_no_smaller_coloring

end HansonToft
