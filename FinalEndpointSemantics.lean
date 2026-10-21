import MultiplicitySemantics

namespace HansonToft

theorem distinct_final_endpoints_give_two_paths {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k)
    (u v : Vertex k) (hne : u ≠ v)
    (hu : ReachesRank color (k - 1) u)
    (hv : ReachesRank color (k - 1) v) :
    HasTwoFullPaths k color := by
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  refine ⟨p, q,
    prefixPathTo_full hk color u p hp,
    prefixPathTo_full hk color v q hq, ?_⟩
  intro heq
  subst q
  exact hne (prefixPathTo_endpoint_unique hp hq)

theorem unique_full_path_has_one_final_endpoint {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k)
    (hUnique : HasUniqueFullPath k color) :
    ∀ u v,
      ReachesRank color (k - 1) u →
      ReachesRank color (k - 1) v →
      u = v := by
  obtain ⟨path, hPath, hOnly⟩ := hUnique
  intro u v hu hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  have hpEq := hOnly p (prefixPathTo_full hk color u p hp)
  have hqEq := hOnly q (prefixPathTo_full hk color v q hq)
  rw [hpEq] at hp
  rw [hqEq] at hq
  exact prefixPathTo_endpoint_unique hp hq

#print axioms distinct_final_endpoints_give_two_paths
#print axioms unique_full_path_has_one_final_endpoint

end HansonToft
