/-
# The bridge case of Howie's Case 2: definitions

Howie's Case 2 (`Work.ORLocInd.Howie.case2`) splits, after the choice of the maximal relator `m`
and of an arrow `e` of `path m` with maximal code `c = P.edgeOf e`, into

* the **connected case**: `e.right` is joined to `e.left` by a path of `Γ ∖ e`; and
* the **bridge case**: no such path exists, i.e. `e` is a bridge of `Γ ∖ e`.

The proofs of the two cases are quite different: the connected case is a direct induction, while
the bridge case first shows that the presentation obtained by deleting one side of the bridge is
again non-indicable, and then applies the induction to *that* presentation.

This file contains the vocabulary of the bridge case:

* `ReachRight P e y` / `ReachLeft P e y` — `y` is joined to `e.right` (resp. `e.left`) by a path of
  `Γ ∖ e`, the graph obtained by deleting the arrows of code `P.edgeOf e`;
* `InSide P e y` — `y` lies in one of the two sides of the bridge;
* `restrictSide P e side L` — the labelling `L` restricted to the arrows lying inside `side`;
* `SideIndicable P m e side` — there is a labelling vanishing on all relators except `r_m` whose
  `pathSum` is non-zero on a closed path running inside `side` and avoiding `e`'s code;
* `keepRight P e` — the subgraph obtained by deleting the `ReachRight` side of the bridge (the
  arrows outside `e`'s code whose endpoints both fail to be `ReachRight`);
* `bridgeRelator P m e`, `bridgePresentation P m e` — the subpresentation of `P` on that subgraph
  obtained by dropping the relator `m` and the relators based in the `ReachRight` side.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.DelReach
import Submission.Work.ORLocInd.Howie.CoverPresentation

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.ambiguousOpen false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## The two sides of the bridge -/

/-- `ReachRight P e y`: the vertex `y` is joined to `e.right` by a path of `Γ` avoiding the
unoriented edge `e`. -/
def ReachRight (P : Presentation V) (e : Quiver.Total V) (y : V) : Prop :=
  ∃ q : Quiver.Path e.right y, Avoids P e q

/-- `ReachLeft P e y`: the vertex `y` is joined to `e.left` by a path of `Γ` avoiding the
unoriented edge `e` (this is `DelReach P e y`). -/
def ReachLeft (P : Presentation V) (e : Quiver.Total V) (y : V) : Prop :=
  ∃ q : Quiver.Path e.left y, Avoids P e q

/-- `y` lies in one of the two sides of the bridge, i.e. in the same component of `Γ ∖ e` as
`e.right` or in the same component of `Γ ∖ e` as `e.left`. -/
def InSide (P : Presentation V) (e : Quiver.Total V) (y : V) : Prop :=
  ReachRight P e y ∨ ReachLeft P e y

theorem reachLeft_iff_delReach (P : Presentation V) (e : Quiver.Total V) (y : V) :
    ReachLeft P e y ↔ DelReach P e y := Iff.rfl

/-! ## Restricting a labelling to a side -/

/-- The label of `g` for the labelling `L` restricted to the arrows which avoid the code of `e`
and both of whose endpoints lie in `side`. -/
noncomputable def restrictSideFun (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) (g : Quiver.Total V) : ℤ := by
  classical
  exact if side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e then L.toFun g else 0

theorem restrictSideFun_of (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) (g : Quiver.Total V)
    (h : side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e) :
    restrictSideFun P e side L g = L.toFun g := by
  unfold restrictSideFun
  exact if_pos h

theorem restrictSideFun_not (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) (g : Quiver.Total V)
    (h : ¬ (side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e)) :
    restrictSideFun P e side L g = 0 := by
  unfold restrictSideFun
  exact if_neg h

/-- The labelling `L` restricted to the arrows which avoid the code of `e` and both of whose
endpoints lie in `side`.  The result is again balanced, whatever `side` is. -/
noncomputable def restrictSide (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) : Labelling V where
  toFun := restrictSideFun P e side L
  balanced g := by
    classical
    unfold restrictSideFun
    have h1 : (Quiver.totalReverse g).left = g.right := rfl
    have h2 : (Quiver.totalReverse g).right = g.left := rfl
    have h3 : P.edgeOf (Quiver.totalReverse g) = P.edgeOf g := P.edgeOf_reverse g
    rw [h1, h2, h3]
    by_cases h : side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e
    · rw [if_pos ⟨h.2.1, h.1, h.2.2⟩, if_pos h, L.balanced g]
    · rw [if_neg h, if_neg (fun hh => h ⟨hh.2.1, hh.1, hh.2.2⟩), neg_zero]

@[simp] theorem restrictSide_apply_of (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) (g : Quiver.Total V)
    (h : side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e) :
    (restrictSide P e side L).toFun g = L.toFun g :=
  restrictSideFun_of P e side L g h

@[simp] theorem restrictSide_apply_not (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) (g : Quiver.Total V)
    (h : ¬ (side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e)) :
    (restrictSide P e side L).toFun g = 0 :=
  restrictSideFun_not P e side L g h

/-- A path all of whose arrows run inside `side` and avoid the code of `e`. -/
def SideLoop (P : Presentation V) (e : Quiver.Total V) (side : V → Prop) {x y : V}
    (β : Quiver.Path x y) : Prop :=
  ∀ g ∈ β.arrowList, side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e

/-- The `pathSum` of a labelling restricted to a side, on a path running inside that side. -/
theorem pathSum_restrictSide (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) {x y : V} (β : Quiver.Path x y) (hβ : SideLoop P e side β) :
    pathSum (restrictSide P e side L).toFun β = pathSum L.toFun β := by
  induction β with
  | nil => rw [pathSum_nil, pathSum_nil]
  | cons p g ih =>
      have h' : SideLoop P e side p := fun h hh => hβ h (List.mem_append.mpr (Or.inl hh))
      have hg := hβ (Quiver.Total.mk _ _ g) (List.mem_append.mpr (Or.inr (by simp)))
      rw [pathSum_cons, pathSum_cons, ih h', restrictSide_apply_of _ _ _ _ _ hg]

/-- The `pathSum` of a labelling restricted to a side, on a path whose arrows all fail to lie
inside the side (the restriction then vanishes). -/
theorem pathSum_restrictSide_eq_zero (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    (L : Labelling V) {x y : V} (β : Quiver.Path x y)
    (hβ : ∀ g ∈ β.arrowList, ¬ (side g.left ∧ side g.right ∧ P.edgeOf g ≠ P.edgeOf e)) :
    pathSum (restrictSide P e side L).toFun β = 0 := by
  induction β with
  | nil => rw [pathSum_nil]
  | cons p g ih =>
      have h' : ∀ h ∈ p.arrowList,
          ¬ (side h.left ∧ side h.right ∧ P.edgeOf h ≠ P.edgeOf e) :=
        fun h hh => hβ h (List.mem_append.mpr (Or.inl hh))
      have hg := hβ (Quiver.Total.mk _ _ g) (List.mem_append.mpr (Or.inr (by simp)))
      rw [pathSum_cons, ih h', restrictSide_apply_not _ _ _ _ _ hg, add_zero]

/-- There is a labelling which vanishes on all relators except `r_m` and whose `pathSum` is
non-zero on some closed path running inside `side` and avoiding the code of `e`. -/
def SideIndicable (P : Presentation V) (m : P.ι) (e : Quiver.Total V) (side : V → Prop) :
    Prop :=
  ∃ (L : Labelling V) (x : V) (β : Quiver.Path x x),
    (∀ i : P.ι, i ≠ m → pathSum L.toFun (P.path i) = 0) ∧
    SideLoop P e side β ∧ pathSum L.toFun β ≠ 0

/-! ## The subgraph and the subpresentation of the bridge case -/

/-- The subgraph of `Γ` obtained by deleting the arrows of code `P.edgeOf e` **and** all the
arrows with an endpoint in the `ReachRight` side of the bridge.

The predicate is stated symmetrically on the two endpoints so that it is automatically invariant
under reversal; for the arrows actually kept (those with code `≠ P.edgeOf e`) it is equivalent to
"the arrows of `Γ ∖ e` with no endpoint in the `ReachRight` side". -/
noncomputable def keepRight (P : Presentation V) (e : Quiver.Total V) : Keep V where
  pred g := P.edgeOf g ≠ P.edgeOf e ∧
    ¬ (ReachRight P e g.left ∨ ReachRight P e g.right)
  rev g := by
    show (P.edgeOf (Quiver.totalReverse g) ≠ P.edgeOf e ∧
        ¬ (ReachRight P e (Quiver.totalReverse g).left ∨
            ReachRight P e (Quiver.totalReverse g).right)) ↔ _
    rw [P.edgeOf_reverse]
    constructor
    · intro h; exact ⟨h.1, fun hh => h.2 hh.symm⟩
    · intro h; exact ⟨h.1, fun hh => h.2 hh.symm⟩

/-- The relators kept in the bridge subpresentation: those other than `m` whose base vertex is
outside the `ReachRight` side. -/
def bridgeRelator (P : Presentation V) (m : P.ι) (e : Quiver.Total V) (i : P.ι) : Prop :=
  i ≠ m ∧ ¬ ReachRight P e (P.base i)

@[simp] theorem keepRight_pred (P : Presentation V) (e : Quiver.Total V) (g : Quiver.Total V) :
    (keepRight P e).pred g = (P.edgeOf g ≠ P.edgeOf e ∧
      ¬ (ReachRight P e g.left ∨ ReachRight P e g.right)) := rfl

theorem keepRight_pred_iff (P : Presentation V) (e : Quiver.Total V) (g : Quiver.Total V) :
    (keepRight P e).pred g ↔ (P.edgeOf g ≠ P.edgeOf e ∧
      ¬ (ReachRight P e g.left ∨ ReachRight P e g.right)) := Iff.rfl

@[simp] theorem bridgeRelator_iff (P : Presentation V) (m : P.ι) (e : Quiver.Total V)
    (i : P.ι) : bridgeRelator P m e i ↔ (i ≠ m ∧ ¬ ReachRight P e (P.base i)) := Iff.rfl

/-- The subpresentation of the bridge case: the arrows outside the `ReachRight` side and the
relators other than `m` based outside that side. -/
noncomputable def bridgePresentation (P : Presentation V) (m : P.ι) (e : Quiver.Total V) :
    Presentation (DelV (keepRight P e)) :=
  P.deleteSub (keepRight P e) (bridgeRelator P m e)

end Work.ORLocInd.Howie
