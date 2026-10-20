import Init

/-!
  Hanson--Toft seven-cycle graphs: definitions and proof obligations.

  This file intentionally contains no proof of the family theorem. In particular,
  `cycleFiniteCheck` is a Boolean program, not a theorem that its result is true,
  and `sixBases` is a proposition, not a certificate of its truth. The external
  CNF/LRAT traces are checked in the separate CertificateK4--CertificateK9
  modules using native evaluation. The full graph theorem remains unproved here.
-/

namespace HansonToft

/-- The seven cycle vertices and the seven disjoint cliques of order `k - 3`. -/
inductive Vertex (k : Nat) where
  | cycle (i : Fin 7)
  | clique (i : Fin 7) (a : Fin (k - 3))
  deriving DecidableEq, Repr

/-- Membership of `x_j` in `T_i = {x_i, x_(i+1), x_(i+3)}`. -/
def inTriple (i j : Fin 7) : Prop :=
  j.val = i.val ∨ j.val = (i.val + 1) % 7 ∨ j.val = (i.val + 3) % 7

/-- The undirected edge relation of `H_k`. The intended range is `k ≥ 4`. -/
def Adj (k : Nat) : Vertex k → Vertex k → Prop
  | .cycle i, .cycle j =>
      (i.val + 1) % 7 = j.val ∨ (j.val + 1) % 7 = i.val
  | .cycle j, .clique i _ => inTriple i j
  | .clique i _, .cycle j => inTriple i j
  | .clique i a, .clique j b => i = j ∧ a ≠ b

/-- Proper vertex coloring with an ordered palette of `m` colors. -/
def Proper (k m : Nat) (c : Vertex k → Fin m) : Prop :=
  ∀ u v, Adj k u v → c u ≠ c v

/-- Consecutive entries of a list form edges. -/
def EdgesAlong {k : Nat} : List (Vertex k) → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => Adj k u v ∧ EdgesAlong (v :: rest)

/-- A simple path whose colors, in sequence, are `0, ..., k-1`. -/
def FullIncreasingPath (k : Nat) (c : Vertex k → Fin k)
    (p : List (Vertex k)) : Prop :=
  p.length = k ∧ p.Nodup ∧ EdgesAlong p ∧
    ∀ (i : Fin k) (v : Vertex k), p[i.val]? = some v → c v = i

/-- Exactly one such vertex sequence exists. -/
def HasUniqueFullPath (k : Nat) (c : Vertex k → Fin k) : Prop :=
  ∃ p, FullIncreasingPath k c p ∧
    ∀ q, FullIncreasingPath k c q → q = p

/-- The coloring formulation of the target assertion for a fixed `k`. -/
def NoMinimalColoring (k : Nat) : Prop :=
  ∀ c : Vertex k → Fin k, Proper k k c → ¬ HasUniqueFullPath k c

/-- A convenient stronger statement when existence of a full path is known. -/
def HasTwoFullPaths (k : Nat) (c : Vertex k → Fin k) : Prop :=
  ∃ p q, FullIncreasingPath k c p ∧ FullIncreasingPath k c q ∧ p ≠ q

/-- A proper coloring after deleting one undirected edge `{u,v}`. -/
def ProperWithoutEdge (k m : Nat) (u v : Vertex k)
    (c : Vertex k → Fin m) : Prop :=
  ∀ a b, Adj k a b →
    ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) → c a ≠ c b

/-- An edge-critical chromatic-number target. For `k ≥ 4` the graphs have no
    isolated vertices, so edge criticality also gives vertex criticality. -/
def EdgeCriticalStatement (k : Nat) : Prop :=
  (∃ c : Vertex k → Fin k, Proper k k c) ∧
  (∀ c : Vertex k → Fin (k - 1), ¬ Proper k (k - 1) c) ∧
  (∀ u v, Adj k u v →
    ∃ c : Vertex k → Fin (k - 1), ProperWithoutEdge k (k - 1) u v c)

/-- A directed relation selecting exactly one direction of each edge. -/
def IsOrientation (k : Nat) (d : Vertex k → Vertex k → Prop) : Prop :=
  (∀ u v, d u v → Adj k u v) ∧
  (∀ u v, Adj k u v → (d u v ↔ ¬ d v u))

/-- Consecutive vertices follow the orientation. -/
def DirectedEdgesAlong {k : Nat}
    (d : Vertex k → Vertex k → Prop) : List (Vertex k) → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => d u v ∧ DirectedEdgesAlong d (v :: rest)

/-- A simple directed path of `k - 1` edges. -/
def FullDirectedPath (k : Nat) (d : Vertex k → Vertex k → Prop)
    (p : List (Vertex k)) : Prop :=
  p.length = k ∧ p.Nodup ∧ DirectedEdgesAlong d p

/-- The original formulation, allowing orientations with directed cycles. -/
def NoMinimalOrientation (k : Nat) : Prop :=
  ∀ d : Vertex k → Vertex k → Prop, IsOrientation k d →
    ¬ (∃ p, FullDirectedPath k d p ∧
      ∀ q, FullDirectedPath k d q → q = p)

/-- The six finite base obligations. This declaration supplies no proof. -/
def sixBases : Prop :=
  NoMinimalColoring 4 ∧ NoMinimalColoring 5 ∧
  NoMinimalColoring 6 ∧ NoMinimalColoring 7 ∧
  NoMinimalColoring 8 ∧ NoMinimalColoring 9

/-- The full family statement. This declaration supplies no proof. -/
def familyStatement : Prop :=
  ∀ k : Nat, 4 ≤ k → NoMinimalColoring k

/-- The two claims intended for the eventual kernel-checked development. -/
def completeFamilyStatement : Prop :=
  ∀ k : Nat, 4 ≤ k →
    EdgeCriticalStatement k ∧ NoMinimalColoring k ∧ NoMinimalOrientation k

/-! ## A finite program for the cycle inequality -/

/-- Extend a restricted-growth word by an old label or the next fresh label. -/
def extendRgs (xs : List Nat) : List (List Nat) :=
  (List.range (xs.foldl Nat.max 0 + 2)).map (fun a => xs ++ [a])

/-- All restricted-growth words of length `n`, beginning with `0`. -/
def rgsCodes : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
      if n = 0 then [[0]] else (rgsCodes n).flatMap extendRgs

/-- Tests the closing edge as well as the six other edges of `C_7`. -/
def properCycleCode (xs : List Nat) : Bool :=
  xs.length == 7 &&
    (List.range 7).all (fun i => xs[i]? != xs[(i + 1) % 7]?)

def tripleCode (xs : List Nat) (i : Nat) : List (Option Nat) :=
  [xs[i]?, xs[(i + 1) % 7]?, xs[(i + 3) % 7]?]

def codeQ (xs : List Nat) : Nat := xs.eraseDups.length

def codeT (xs : List Nat) : Nat :=
  ((List.range 7).filter (fun i => (tripleCode xs i).eraseDups.length == 2)).length

/-- Checks 162 proper cycle partitions and the bounds `t ≤ 6`, `q+t ≤ 9`.
    A theorem connecting this Boolean value to all proper cycle colorings is still needed. -/
def cycleFiniteCheck : Bool :=
  let codes := (rgsCodes 7).filter properCycleCode
  codes.length == 162 &&
    codes.all (fun xs => decide (codeT xs ≤ 6 ∧ codeQ xs + codeT xs ≤ 9))

end HansonToft
