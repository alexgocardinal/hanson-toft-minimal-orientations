import ChromaticLowerBound

namespace HansonToft

def baseCycleColor (i : Fin 7) : Fin 3 :=
  ⟨if i.val = 6 then 2 else i.val % 2, by
    split
    · decide
    · have h := Nat.mod_lt i.val (by decide : 0 < 2)
      omega⟩

theorem baseCycleColor_proper :
    ∀ i j : Fin 7,
      ((i.val + 1) % 7 = j.val ∨
        (j.val + 1) % 7 = i.val) →
      baseCycleColor i ≠ baseCycleColor j := by
  decide

def uniformColor (k : Nat) (hk : 4 ≤ k) :
    Vertex k → Fin k
  | .cycle i =>
      ⟨(baseCycleColor i).val, by
        have h := (baseCycleColor i).isLt
        omega⟩
  | .clique _ a =>
      ⟨a.val + 3, by
        have h := a.isLt
        omega⟩

theorem uniformColor_proper (k : Nat) (hk : 4 ≤ k) :
    Proper k k (uniformColor k hk) := by
  intro u v hAdj hEqual
  have hValues := congrArg Fin.val hEqual
  cases u with
  | cycle i =>
      cases v with
      | cycle j =>
          apply baseCycleColor_proper i j hAdj
          apply Fin.ext
          exact hValues
      | clique j b =>
          change (baseCycleColor i).val = b.val + 3 at hValues
          have hSmall := (baseCycleColor i).isLt
          omega
  | clique i a =>
      cases v with
      | cycle j =>
          change a.val + 3 = (baseCycleColor j).val at hValues
          have hSmall := (baseCycleColor j).isLt
          omega
      | clique j b =>
          change a.val + 3 = b.val + 3 at hValues
          apply hAdj.2
          apply Fin.ext
          omega

theorem exists_proper_k_coloring {k : Nat} (hk : 4 ≤ k) :
    ∃ color : Vertex k → Fin k, Proper k k color := by
  exact ⟨uniformColor k hk, uniformColor_proper k hk⟩

#print axioms baseCycleColor_proper
#print axioms exists_proper_k_coloring

end HansonToft
