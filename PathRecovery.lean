import SimplePathExtension

namespace HansonToft

theorem filter_kept_list {α : Type} (keep : α → Bool)
    (xs : List α) (h : ∀ x ∈ xs, keep x = true) :
    xs.filter keep = xs := by
  revert h
  induction xs with
  | nil =>
      intro h
      rfl
  | cons x xs ih =>
      intro h
      have hx := h x (List.mem_cons.mpr (Or.inl rfl))
      have hxs : ∀ y ∈ xs, keep y = true := by
        intro y hy
        exact h y (List.mem_cons.mpr (Or.inr hy))
      simp [hx, ih hxs]

theorem filter_insert_middle {α : Type} (keep : α → Bool)
    (front rest : List α) (z : α)
    (hz : keep z = false)
    (hKeep : ∀ x ∈ front ++ rest, keep x = true) :
    (front ++ z :: rest).filter keep = front ++ rest := by
  have hf : front.filter keep = front := by
    apply filter_kept_list
    intro x hx
    exact hKeep x (List.mem_append.mpr (Or.inl hx))
  have hr : rest.filter keep = rest := by
    apply filter_kept_list
    intro x hx
    exact hKeep x (List.mem_append.mpr (Or.inr hx))
  simp [List.filter_append, hz, hf, hr]

theorem recovered_lists_distinct {α : Type} (keep : α → Bool)
    (p q outP outQ : List α)
    (hp : outP.filter keep = p)
    (hq : outQ.filter keep = q)
    (hne : p ≠ q) :
    outP ≠ outQ := by
  intro heq
  apply hne
  calc
    p = outP.filter keep := hp.symm
    _ = outQ.filter keep := congrArg (fun xs => xs.filter keep) heq
    _ = q := hq

def Survives {k : Nat}
    (removed : Fin 7 → Fin (k - 3)) : Vertex k → Bool
  | .cycle _ => true
  | .clique i a => decide (a ≠ removed i)

theorem selected_does_not_survive {k : Nat}
    (removed : Fin 7 → Fin (k - 3)) (i : Fin 7) :
    Survives removed (.clique i (removed i)) = false := by
  simp [Survives]

theorem survives_of_keep {k : Nat}
    (removed : Fin 7 → Fin (k - 3)) (v : Vertex k)
    (hv : ∀ i, v ≠ .clique i (removed i)) :
    Survives removed v = true := by
  cases v with
  | cycle j =>
      rfl
  | clique j b =>
      have hne : b ≠ removed j := by
        intro heq
        apply hv j
        cases heq
        rfl
      simp [Survives, hne]

theorem recover_middle_insertion {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (front rest : List (Vertex k)) (i : Fin 7)
    (hKeep : ∀ w ∈ front ++ rest,
      ∀ j, w ≠ .clique j (removed j)) :
    (front ++ .clique i (removed i) :: rest).filter
      (Survives removed) = front ++ rest := by
  apply filter_insert_middle
  · exact selected_does_not_survive removed i
  · intro w hw
    exact survives_of_keep removed w (hKeep w hw)

#print axioms filter_insert_middle
#print axioms recovered_lists_distinct
#print axioms recover_middle_insertion

end HansonToft
