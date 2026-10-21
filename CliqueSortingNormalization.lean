import PaletteReversalNormalization
import Init.Data.List.FinRange
import Init.Data.List.Sort.Lemmas
import Init.Data.List.Pairwise

namespace HansonToft

structure SortedIndexPermutation {n : Nat} (rank : Fin n → Nat) where
  toIndex : Fin n → Fin n
  fromIndex : Fin n → Fin n
  leftInverse : ∀ a, fromIndex (toIndex a) = a
  rightInverse : ∀ a, toIndex (fromIndex a) = a
  increasing : ∀ a b, a.val < b.val →
    rank (toIndex a) ≤ rank (toIndex b)

theorem SortedIndexPermutation.injective {n : Nat}
    {rank : Fin n → Nat} (e : SortedIndexPermutation rank)
    (a b : Fin n) (h : e.toIndex a = e.toIndex b) :
    a = b := by
  have hBack := congrArg e.fromIndex h
  simpa only [e.leftInverse] using hBack

theorem sorted_index_permutation_exists {n : Nat}
    (rank : Fin n → Nat) :
    Nonempty (SortedIndexPermutation rank) := by
  classical
  let compare : Fin n → Fin n → Bool :=
    fun a b => decide (rank a ≤ rank b)
  let xs := (List.finRange n).mergeSort compare
  have hLength : xs.length = n := by
    simp only [xs, List.length_mergeSort, List.length_finRange]
  have hBase : (List.finRange n).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro a b ha hb hab
    have hValues := congrArg Fin.val hab
    simpa only [List.getElem_finRange, Fin.val_cast] using hValues
  have hSimple : xs.Nodup :=
    hBase.perm (List.mergeSort_perm (List.finRange n) compare).symm
  have hSorted :
      xs.Pairwise (fun a b => rank a ≤ rank b) := by
    have hTrans : ∀ a b c : Fin n,
        compare a b → compare b c → compare a c := by
      intro a b c hab hbc
      simp only [compare, decide_eq_true_eq] at hab hbc ⊢
      omega
    have hTotal : ∀ a b : Fin n, compare a b || compare b a := by
      intro a b
      simp only [compare, Bool.or_eq_true, decide_eq_true_eq]
      omega
    have h := List.pairwise_mergeSort hTrans hTotal (List.finRange n)
    simpa only [compare, decide_eq_true_eq] using h
  let forward : Fin n → Fin n :=
    fun a => xs[a.val]'(by rw [hLength]; exact a.isLt)
  have hInject : ∀ a b, forward a = forward b → a = b := by
    intro a b hab
    apply Fin.ext
    exact hSimple.eq_of_getElem_eq
      (by rw [hLength]; exact a.isLt)
      (by rw [hLength]; exact b.isLt) hab
  have hSurject : ∀ b : Fin n, ∃ a, forward a = b := by
    intro b
    have hMem : b ∈ xs :=
      List.mem_mergeSort.mpr (List.mem_finRange b)
    obtain ⟨j, hj, hEqual⟩ := List.mem_iff_getElem.mp hMem
    refine ⟨⟨j, ?_⟩, ?_⟩
    · simpa only [hLength] using hj
    · exact hEqual
  let backward : Fin n → Fin n :=
    fun b => Classical.choose (hSurject b)
  have hRight : ∀ b, forward (backward b) = b := by
    intro b
    exact Classical.choose_spec (hSurject b)
  refine ⟨⟨forward, backward, ?_, hRight, ?_⟩⟩
  · intro a
    apply hInject
    exact hRight (forward a)
  · intro a b hab
    exact hSorted.rel_getElem_of_lt
      (by rw [hLength]; exact a.isLt)
      (by rw [hLength]; exact b.isLt) hab

noncomputable def cliqueSortingPermutation {k : Nat}
    (color : Vertex k → Fin k) (i : Fin 7) :
    SortedIndexPermutation
      (fun a : Fin (k - 3) => (color (.clique i a)).val) :=
  Classical.choice (sorted_index_permutation_exists _)

noncomputable def cliqueSortTo {k : Nat}
    (color : Vertex k → Fin k) : Vertex k → Vertex k
  | .cycle i => .cycle i
  | .clique i a =>
      .clique i ((cliqueSortingPermutation color i).toIndex a)

noncomputable def cliqueSortFrom {k : Nat}
    (color : Vertex k → Fin k) : Vertex k → Vertex k
  | .cycle i => .cycle i
  | .clique i a =>
      .clique i ((cliqueSortingPermutation color i).fromIndex a)

noncomputable def cliqueSortingRelabeling {k : Nat}
    (color : Vertex k → Fin k) : GraphRelabeling k where
  toVertex := cliqueSortTo color
  fromVertex := cliqueSortFrom color
  leftInverse := by
    intro v
    cases v with
    | cycle i => rfl
    | clique i a =>
        exact congrArg (Vertex.clique i)
          ((cliqueSortingPermutation color i).leftInverse a)
  rightInverse := by
    intro v
    cases v with
    | cycle i => rfl
    | clique i a =>
        exact congrArg (Vertex.clique i)
          ((cliqueSortingPermutation color i).rightInverse a)
  adj_iff := by
    intro u v
    cases u with
    | cycle i =>
        cases v <;> rfl
    | clique i a =>
        cases v with
        | cycle j => rfl
        | clique j b =>
            change
              (i = j ∧
                (cliqueSortingPermutation color i).toIndex a ≠
                  (cliqueSortingPermutation color j).toIndex b) ↔
              (i = j ∧ a ≠ b)
            constructor
            · rintro ⟨hij, hDifferent⟩
              subst j
              refine ⟨rfl, ?_⟩
              intro hab
              exact hDifferent
                (congrArg
                  (cliqueSortingPermutation color i).toIndex hab)
            · rintro ⟨hij, hDifferent⟩
              subst j
              refine ⟨rfl, ?_⟩
              intro hEqual
              exact hDifferent
                ((cliqueSortingPermutation color i).injective a b hEqual)

theorem clique_sorting_strict {k : Nat}
    (color : Vertex k → Fin k)
    (hProper : Proper k k color) :
    ∀ (i : Fin 7) (a b : Fin (k - 3)),
      a.val + 1 = b.val →
      ((relabelColor (cliqueSortingRelabeling color) color)
        (.clique i a)).val <
      ((relabelColor (cliqueSortingRelabeling color) color)
        (.clique i b)).val := by
  intro i a b hNext
  have hab : a ≠ b := by
    intro hEqual
    have hValues := congrArg Fin.val hEqual
    omega
  have hLe :=
    (cliqueSortingPermutation color i).increasing a b (by omega)
  have hIndices :
      (cliqueSortingPermutation color i).toIndex a ≠
        (cliqueSortingPermutation color i).toIndex b := by
    intro hEqual
    exact hab
      ((cliqueSortingPermutation color i).injective a b hEqual)
  have hColors :
      color (.clique i
        ((cliqueSortingPermutation color i).toIndex a)) ≠
      color (.clique i
        ((cliqueSortingPermutation color i).toIndex b)) :=
    hProper _ _ ⟨rfl, hIndices⟩
  have hValues :
      (color (.clique i
        ((cliqueSortingPermutation color i).toIndex a))).val ≠
      (color (.clique i
        ((cliqueSortingPermutation color i).toIndex b))).val := by
    intro hEqual
    exact hColors (Fin.ext hEqual)
  change
    (color (.clique i
      ((cliqueSortingPermutation color i).toIndex a))).val <
    (color (.clique i
      ((cliqueSortingPermutation color i).toIndex b))).val
  omega

theorem normalize_unique_small_coloring
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hProper : Proper (s.val + 4) (s.val + 4) color)
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    ∃ d : Vertex (s.val + 4) → Fin (s.val + 4),
      Proper (s.val + 4) (s.val + 4) d ∧
      HasUniqueFullPath (s.val + 4) d ∧
      EncodingNormalized d := by
  obtain ⟨d, hd, hUniqueD, hMinimum, hHalf⟩ :=
    normalize_cycle_minimum_and_half s color hProper hUnique
  refine ⟨relabelColor (cliqueSortingRelabeling d) d,
    relabel_preserves_proper (cliqueSortingRelabeling d) d hd,
    relabel_preserves_unique (cliqueSortingRelabeling d) d hUniqueD,
    ?_⟩
  refine ⟨clique_sorting_strict d hd, ?_, ?_⟩
  · exact hMinimum
  · exact hHalf

theorem small_coloring_has_no_unique_path
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hProper : Proper (s.val + 4) (s.val + 4) color) :
    ¬ HasUniqueFullPath (s.val + 4) color := by
  intro hUnique
  obtain ⟨d, hd, hUniqueD, hNormalized⟩ :=
    normalize_unique_small_coloring s color hProper hUnique
  exact normalized_coloring_has_no_unique_path
    s d hd hNormalized hUniqueD

#print axioms sorted_index_permutation_exists
#print axioms normalize_unique_small_coloring
#print axioms small_coloring_has_no_unique_path

end HansonToft
