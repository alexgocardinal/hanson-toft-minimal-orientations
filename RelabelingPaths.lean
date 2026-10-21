import NormalizedEncodingContradiction

namespace HansonToft

structure GraphRelabeling (k : Nat) where
  toVertex : Vertex k → Vertex k
  fromVertex : Vertex k → Vertex k
  leftInverse : ∀ v, fromVertex (toVertex v) = v
  rightInverse : ∀ v, toVertex (fromVertex v) = v
  adj_iff : ∀ u v,
    Adj k (toVertex u) (toVertex v) ↔ Adj k u v

def relabelColor {k : Nat}
    (e : GraphRelabeling k) (color : Vertex k → Fin k) :
    Vertex k → Fin k :=
  fun v => color (e.toVertex v)

theorem GraphRelabeling.to_injective {k : Nat}
    (e : GraphRelabeling k) (u v : Vertex k)
    (h : e.toVertex u = e.toVertex v) : u = v := by
  calc
    u = e.fromVertex (e.toVertex u) := (e.leftInverse u).symm
    _ = e.fromVertex (e.toVertex v) := congrArg e.fromVertex h
    _ = v := e.leftInverse v

theorem GraphRelabeling.from_injective {k : Nat}
    (e : GraphRelabeling k) (u v : Vertex k)
    (h : e.fromVertex u = e.fromVertex v) : u = v := by
  calc
    u = e.toVertex (e.fromVertex u) := (e.rightInverse u).symm
    _ = e.toVertex (e.fromVertex v) := congrArg e.toVertex h
    _ = v := e.rightInverse v

theorem GraphRelabeling.from_adj {k : Nat}
    (e : GraphRelabeling k) (u v : Vertex k)
    (h : Adj k u v) :
    Adj k (e.fromVertex u) (e.fromVertex v) := by
  apply (e.adj_iff (e.fromVertex u) (e.fromVertex v)).mp
  simpa only [e.rightInverse] using h

theorem edgesAlong_map_preserved {k : Nat}
    (f : Vertex k → Vertex k)
    (hAdj : ∀ u v, Adj k u v → Adj k (f u) (f v))
    (p : List (Vertex k)) (h : EdgesAlong p) :
    EdgesAlong (p.map f) := by
  revert h
  induction p with
  | nil =>
      intro h
      trivial
  | cons u rest ih =>
      intro h
      cases rest with
      | nil =>
          trivial
      | cons v rest =>
          exact ⟨hAdj u v h.1, ih h.2⟩

theorem full_path_map_preserved {k : Nat}
    (f : Vertex k → Vertex k)
    (sourceColor targetColor : Vertex k → Fin k)
    (hInjective : ∀ u v, f u = f v → u = v)
    (hAdj : ∀ u v, Adj k u v → Adj k (f u) (f v))
    (hColors : ∀ v, targetColor (f v) = sourceColor v)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k sourceColor p) :
    FullIncreasingPath k targetColor (p.map f) := by
  have hRanks :=
    ((fullIncreasingPath_iff_ranks sourceColor p).mp hp).2.2.2
  apply (fullIncreasingPath_iff_ranks targetColor (p.map f)).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using hp.1
  · exact nodup_map_of_injective f hInjective p hp.2.1
  · exact edgesAlong_map_preserved f hAdj p hp.2.2.1
  · exact ranksFrom_map f
      (fun v => (sourceColor v).val)
      (fun v => (targetColor v).val)
      (fun v => congrArg Fin.val (hColors v)) p 0 hRanks

theorem map_to_from {k : Nat}
    (e : GraphRelabeling k) (p : List (Vertex k)) :
    (p.map e.toVertex).map e.fromVertex = p := by
  induction p with
  | nil =>
      rfl
  | cons v rest ih =>
      simp only [List.map_cons, e.leftInverse, ih]

theorem map_from_to {k : Nat}
    (e : GraphRelabeling k) (p : List (Vertex k)) :
    (p.map e.fromVertex).map e.toVertex = p := by
  induction p with
  | nil =>
      rfl
  | cons v rest ih =>
      simp only [List.map_cons, e.rightInverse, ih]

theorem relabel_preserves_proper {k : Nat}
    (e : GraphRelabeling k) (color : Vertex k → Fin k)
    (hProper : Proper k k color) :
    Proper k k (relabelColor e color) := by
  intro u v hAdj hEqual
  exact hProper (e.toVertex u) (e.toVertex v)
    ((e.adj_iff u v).mpr hAdj) hEqual

theorem relabel_path_forward {k : Nat}
    (e : GraphRelabeling k) (color : Vertex k → Fin k)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k (relabelColor e color) p) :
    FullIncreasingPath k color (p.map e.toVertex) := by
  exact full_path_map_preserved e.toVertex
    (relabelColor e color) color
    (GraphRelabeling.to_injective e)
    (fun u v h => (e.adj_iff u v).mpr h)
    (fun v => rfl) p hp

theorem relabel_path_backward {k : Nat}
    (e : GraphRelabeling k) (color : Vertex k → Fin k)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k color p) :
    FullIncreasingPath k (relabelColor e color)
      (p.map e.fromVertex) := by
  exact full_path_map_preserved e.fromVertex
    color (relabelColor e color)
    (GraphRelabeling.from_injective e)
    (GraphRelabeling.from_adj e)
    (fun v => congrArg color (e.rightInverse v)) p hp

theorem relabel_preserves_unique {k : Nat}
    (e : GraphRelabeling k) (color : Vertex k → Fin k)
    (hUnique : HasUniqueFullPath k color) :
    HasUniqueFullPath k (relabelColor e color) := by
  obtain ⟨p, hp, hOnly⟩ := hUnique
  refine ⟨p.map e.fromVertex,
    relabel_path_backward e color p hp, ?_⟩
  intro q hq
  have hMapped := hOnly (q.map e.toVertex)
    (relabel_path_forward e color q hq)
  calc
    q = (q.map e.toVertex).map e.fromVertex :=
      (map_to_from e q).symm
    _ = p.map e.fromVertex :=
      congrArg (fun xs : List (Vertex k) => xs.map e.fromVertex) hMapped

theorem relabel_preserves_two_paths {k : Nat}
    (e : GraphRelabeling k) (color : Vertex k → Fin k)
    (hTwo : HasTwoFullPaths k color) :
    HasTwoFullPaths k (relabelColor e color) := by
  obtain ⟨p, q, hp, hq, hDifferent⟩ := hTwo
  refine ⟨p.map e.fromVertex, q.map e.fromVertex,
    relabel_path_backward e color p hp,
    relabel_path_backward e color q hq, ?_⟩
  intro hEqual
  apply hDifferent
  have hMapped :=
    congrArg (fun xs : List (Vertex k) => xs.map e.toVertex) hEqual
  rw [map_from_to e p, map_from_to e q] at hMapped
  exact hMapped

#print axioms relabel_preserves_proper
#print axioms relabel_preserves_unique
#print axioms relabel_preserves_two_paths

end HansonToft
