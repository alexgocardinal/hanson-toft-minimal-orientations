import FullPathReachability

namespace HansonToft

theorem full_path_has_prefix_witness {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k color p) :
    ∃ v, PrefixPathTo color (k - 1) v p := by
  have hNonempty : p ≠ [] := by
    intro hEmpty
    have hLength := hp.1
    rw [hEmpty] at hLength
    simp only [List.length_nil] at hLength
    omega
  obtain ⟨front, v, hList⟩ :=
    nonempty_list_has_last p hNonempty
  have hProperties := (fullIncreasingPath_iff_ranks color p).mp hp
  rw [hList] at hProperties
  have hLength : front.length = k - 1 := by
    have h := hProperties.1
    simp only [List.length_append, List.length_cons,
      List.length_nil] at h
    omega
  have hPrefix := ranked_append_gives_prefix color front v
    hProperties.2.2.1 hProperties.2.2.2
  refine ⟨v, ?_⟩
  rw [hList]
  simpa only [hLength] using hPrefix

theorem unique_full_path_iff_final_conditions {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k) :
    HasUniqueFullPath k color ↔
      ∃ v,
        ReachesRank color (k - 1) v ∧
        (∀ w, ReachesRank color (k - 1) w → w = v) ∧
        (∀ w, ¬ MultipleRankPaths color (k - 1) w) := by
  constructor
  · intro hUnique
    obtain ⟨p, hp, hOnly⟩ := hUnique
    obtain ⟨v, hv⟩ :=
      full_path_gives_final_reachability hk color p hp
    refine ⟨v, hv, ?_, ?_⟩
    · intro w hw
      exact unique_full_path_has_one_final_endpoint
        hk color ⟨p, hp, hOnly⟩ w v hw hv
    · intro w
      exact unique_full_path_forbids_multiplicity
        hk color ⟨p, hp, hOnly⟩ w
  · rintro ⟨v, hv, hEndpoint, hNoMultiple⟩
    obtain ⟨p, hP⟩ := hv
    refine ⟨p, prefixPathTo_full hk color v p hP, ?_⟩
    intro q hq
    obtain ⟨w, hQ⟩ :=
      full_path_has_prefix_witness hk color q hq
    have hEndpointEq : w = v := hEndpoint w ⟨q, hQ⟩
    subst w
    apply Classical.byContradiction
    intro hDifferent
    exact hNoMultiple v ⟨q, p, hQ, hP, hDifferent⟩

#print axioms full_path_has_prefix_witness
#print axioms unique_full_path_iff_final_conditions

end HansonToft
