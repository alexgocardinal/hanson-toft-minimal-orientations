import OrientationPathBridge

namespace HansonToft

/-- Reachability, including the path of length zero. -/
inductive ArcReach {α : Type} (e : α → α → Prop) : α → α → Prop
  | refl (x : α) : ArcReach e x x
  | tail {x y z : α} :
      ArcReach e x y → e y z → ArcReach e x z

theorem ArcReach.trans {α : Type} {e : α → α → Prop}
    {x y z : α}
    (hxy : ArcReach e x y) (hyz : ArcReach e y z) :
    ArcReach e x z := by
  induction hyz with
  | refl => exact hxy
  | tail hPath hEdge ih =>
      exact ArcReach.tail ih hEdge

theorem ArcReach.mono {α : Type}
    {e f : α → α → Prop}
    (hSub : ∀ x y, e x y → f x y)
    {x y : α} (h : ArcReach e x y) :
    ArcReach f x y := by
  induction h with
  | refl => exact ArcReach.refl _
  | tail hPath hEdge ih =>
      exact ArcReach.tail ih (hSub _ _ hEdge)

def ArcAcyclic {α : Type} (e : α → α → Prop) : Prop :=
  ∀ x y, e x y → ¬ ArcReach e y x

def insertArc {α : Type}
    (e : α → α → Prop) (a b : α) : α → α → Prop :=
  fun x y => e x y ∨ (x = a ∧ y = b)

theorem arcReach_insert_cases {α : Type}
    (e : α → α → Prop) (a b : α)
    (hNoBack : ¬ ArcReach e b a)
    {x y : α} (h : ArcReach (insertArc e a b) x y) :
    ArcReach e x y ∨
      (ArcReach e x a ∧ ArcReach e b y) := by
  induction h with
  | refl =>
      exact Or.inl (ArcReach.refl _)
  | @tail y z hPath hEdge ih =>
      rcases hEdge with hOld | ⟨hya, hzb⟩
      · rcases ih with hOldPath | ⟨hPrefix, hSuffix⟩
        · exact Or.inl (ArcReach.tail hOldPath hOld)
        · exact Or.inr ⟨hPrefix, ArcReach.tail hSuffix hOld⟩
      · subst y
        subst z
        rcases ih with hOldPath | ⟨hPrefix, hSuffix⟩
        · exact Or.inr ⟨hOldPath, ArcReach.refl b⟩
        · exact False.elim (hNoBack hSuffix)

theorem insertArc_acyclic {α : Type}
    (e : α → α → Prop) (a b : α)
    (hAcyclic : ArcAcyclic e)
    (hNoBack : ¬ ArcReach e b a) :
    ArcAcyclic (insertArc e a b) := by
  intro x y hEdge hReturn
  rcases hEdge with hOld | ⟨hxa, hyb⟩
  · rcases arcReach_insert_cases e a b hNoBack hReturn with
      hOldReturn | ⟨hPrefix, hSuffix⟩
    · exact hAcyclic x y hOld hOldReturn
    · exact hNoBack
        ((ArcReach.tail hSuffix hOld).trans hPrefix)
  · subst x
    subst y
    rcases arcReach_insert_cases e a b hNoBack hReturn with
      hOldReturn | ⟨hPrefix, hSuffix⟩
    · exact hNoBack hOldReturn
    · exact hNoBack hPrefix

/-- Process a finite arc list, skipping arcs that would close a cycle. -/
noncomputable def greedyAcyclicExtension {α : Type} :
    List (α × α) → (α → α → Prop) → (α → α → Prop)
  | [], e => e
  | (a, b) :: rest, e => by
      classical
      exact if ArcReach e b a then
        greedyAcyclicExtension rest e
      else
        greedyAcyclicExtension rest (insertArc e a b)

theorem greedyAcyclicExtension_extends {α : Type}
    (edges : List (α × α)) (e : α → α → Prop) :
    ∀ x y, e x y → greedyAcyclicExtension edges e x y := by
  classical
  induction edges generalizing e with
  | nil =>
      intro x y h
      exact h
  | cons edge rest ih =>
      obtain ⟨a, b⟩ := edge
      intro x y h
      by_cases hBack : ArcReach e b a
      · simpa only [
          greedyAcyclicExtension, ite_eq_left hBack
        ] using ih e x y h
      · simpa only [
          greedyAcyclicExtension, ite_eq_right hBack
        ] using
          ih (insertArc e a b) x y (Or.inl h)

theorem greedyAcyclicExtension_acyclic {α : Type}
    (edges : List (α × α)) (e : α → α → Prop)
    (hAcyclic : ArcAcyclic e) :
    ArcAcyclic (greedyAcyclicExtension edges e) := by
  classical
  induction edges generalizing e with
  | nil =>
      exact hAcyclic
  | cons edge rest ih =>
      obtain ⟨a, b⟩ := edge
      by_cases hBack : ArcReach e b a
      · simpa only [
          greedyAcyclicExtension, ite_eq_left hBack
        ] using ih e hAcyclic
      · simpa only [
          greedyAcyclicExtension, ite_eq_right hBack
        ] using
          ih (insertArc e a b)
            (insertArc_acyclic e a b hAcyclic hBack)

theorem greedyAcyclicExtension_sound {α : Type}
    (d : α → α → Prop) (edges : List (α × α)) :
    ∀ e : α → α → Prop,
      (∀ x y, e x y → d x y) →
      (∀ p ∈ edges, d p.1 p.2) →
      ∀ x y, greedyAcyclicExtension edges e x y → d x y := by
  classical
  induction edges with
  | nil =>
      intro e hSub hAllowed x y h
      exact hSub x y h
  | cons edge rest ih =>
      obtain ⟨a, b⟩ := edge
      intro e hSub hAllowed x y h
      have hTail : ∀ p ∈ rest, d p.1 p.2 := by
        intro p hp
        exact hAllowed p (List.mem_cons_of_mem _ hp)
      by_cases hBack : ArcReach e b a
      · have hRest : greedyAcyclicExtension rest e x y := by
          simpa only [
            greedyAcyclicExtension, ite_eq_left hBack
          ] using h
        exact ih e hSub hTail x y hRest
      · have hInserted :
            ∀ u v, insertArc e a b u v → d u v := by
          intro u v huv
          rcases huv with hOld | ⟨hua, hvb⟩
          · exact hSub u v hOld
          · subst u
            subst v
            exact hAllowed (a, b) (by simp)
        have hRest :
            greedyAcyclicExtension rest (insertArc e a b) x y := by
          simpa only [
            greedyAcyclicExtension, ite_eq_right hBack
          ] using h
        exact ih (insertArc e a b) hInserted hTail x y hRest

theorem greedyAcyclicExtension_saturated {α : Type}
    (edges : List (α × α)) :
    ∀ (e : α → α → Prop) (p : α × α),
      p ∈ edges →
      greedyAcyclicExtension edges e p.1 p.2 ∨
        ArcReach (greedyAcyclicExtension edges e) p.2 p.1 := by
  classical
  induction edges with
  | nil =>
      intro e p hp
      cases hp
  | cons edge rest ih =>
      obtain ⟨a, b⟩ := edge
      intro e p hp
      have hCases : p = (a, b) ∨ p ∈ rest :=
        List.mem_cons.mp hp
      by_cases hBack : ArcReach e b a
      · have hResult :
            greedyAcyclicExtension rest e p.1 p.2 ∨
              ArcReach (greedyAcyclicExtension rest e) p.2 p.1 := by
          rcases hCases with hEqual | hMem
          · subst p
            right
            exact ArcReach.mono
              (greedyAcyclicExtension_extends rest e) hBack
          · exact ih e p hMem
        simpa only [
          greedyAcyclicExtension, ite_eq_left hBack
        ] using hResult
      · have hResult :
            greedyAcyclicExtension rest (insertArc e a b) p.1 p.2 ∨
              ArcReach
                (greedyAcyclicExtension rest (insertArc e a b))
                p.2 p.1 := by
          rcases hCases with hEqual | hMem
          · subst p
            left
            exact greedyAcyclicExtension_extends
              rest (insertArc e a b) a b (Or.inr ⟨rfl, rfl⟩)
          · exact ih (insertArc e a b) p hMem
        simpa only [
          greedyAcyclicExtension, ite_eq_right hBack
        ] using hResult

#print axioms insertArc_acyclic
#print axioms greedyAcyclicExtension_acyclic
#print axioms greedyAcyclicExtension_sound
#print axioms greedyAcyclicExtension_saturated

end HansonToft
