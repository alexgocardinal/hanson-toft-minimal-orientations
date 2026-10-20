import DeletionCorrespondence

namespace HansonToft

theorem color_avoids_deleted_rank {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (color : Vertex (m + 4) → Fin (m + 4))
    (hProper : Proper (m + 4) (m + 4) color)
    (c : Fin (m + 4))
    (hCycle : ∀ i, color (.cycle i) ≠ c)
    (hRemoved : ∀ i, color (deletedVertex removed i) = c)
    (v : Vertex (m + 4))
    (hv : ∀ i, v ≠ deletedVertex removed i) :
    color v ≠ c := by
  cases v with
  | cycle i =>
      exact hCycle i
  | clique i a =>
      intro hc
      have hadj :
          Adj (m + 4) (.clique i a) (deletedVertex removed i) := by
        refine ⟨rfl, ?_⟩
        intro heq
        exact hv i (congrArg (Vertex.clique i) heq)
      exact hProper _ _ hadj (hc.trans (hRemoved i).symm)

theorem proper_coloring_after_deletion {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (color : Vertex (m + 4) → Fin (m + 4))
    (hProper : Proper (m + 4) (m + 4) color)
    (c : Fin (m + 4))
    (hCycle : ∀ i, color (.cycle i) ≠ c)
    (hRemoved : ∀ i, color (deletedVertex removed i) = c) :
    ∃ d : Vertex (m + 3) → Fin (m + 3),
      Proper (m + 3) (m + 3) d ∧
      ∀ u, expandColor c (d u) = color (embedVertex removed u) := by
  have hAvoid : ∀ u : Vertex (m + 3),
      color (embedVertex removed u) ≠ c := by
    intro u
    exact color_avoids_deleted_rank
      removed color hProper c hCycle hRemoved
      (embedVertex removed u) (embedVertex_not_deleted removed u)
  let d : Vertex (m + 3) → Fin (m + 3) :=
    fun u => compressColor c (color (embedVertex removed u)) (hAvoid u)
  refine ⟨d, ?_, ?_⟩
  · intro u v huv heq
    apply hProper (embedVertex removed u) (embedVertex removed v)
      ((embedVertex_adj_iff removed u v).mpr huv)
    calc
      color (embedVertex removed u) = expandColor c (d u) :=
        (expand_compress_color c _ (hAvoid u)).symm
      _ = expandColor c (d v) := congrArg (expandColor c) heq
      _ = color (embedVertex removed v) :=
        expand_compress_color c _ (hAvoid v)
  · intro u
    exact expand_compress_color c _ (hAvoid u)

#print axioms color_avoids_deleted_rank
#print axioms proper_coloring_after_deletion

end HansonToft
