/-
# The bridge presentation of Howie's Case 2 is non-indicable

Let `P` be a graph presentation with edge code `P.edgeOf`, `m` a relator and `e` an arrow whose
code occurs in the relator `m`.  Assume

* every relator other than `m` avoids the code of `e` (`hbrl`);
* `e` is a *bridge* of `Γ ∖ e`, i.e. `e.right` cannot be joined to `e.left` avoiding `e` (`hbr`);
* `P` has no indicable labelling (`hnon`);
* the `e.left`-side of the bridge is not side-indicable (`hside`).

Then the *bridge presentation* `P.deleteSub (keepRight P e) (bridgeRelator P m e)` — the
subpresentation consisting of the arrows outside the `ReachRight` side of the bridge and of the
relators other than `m` based outside that side — has no indicable labelling either.

The proof is the following.  Suppose `L'` is an indicable labelling of the bridge presentation,
witnessed by the closed path `β'`, and let `L := extendLabelling (keepRight P e) L'` be its
extension to `Γ` by `0`.  Write `β` for the erasure of `β'` to `Γ`.

* `L` vanishes on every relator `i ≠ m` of `P` (this is
  `C2.extendLabelling_vanishes_of_bridge`): such a relator avoids the code of `e`, so it lies
  inside a single component of `Γ ∖ e`; if that component is not the `ReachRight` one the relator
  is one of the relators of the bridge presentation (where `L'` vanishes), and if it is, every
  arrow of the relator has a `ReachRight` endpoint, so `L` vanishes on all of them.
* If `β` starts in the `ReachLeft` side (`hcase`), then `β` is a closed path running inside that
  side (`C2.sideLoop_erasePath_of_reachLeft`), and `L` exhibits `SideIndicable P m e
  (ReachLeft P e)`, contradicting `hside`.
* Otherwise `β` starts in neither side: the arrows of `β` are kept, so no endpoint of `β` is
  `ReachRight`, and `¬ ReachLeft` propagates along `β` (which avoids the code of `e`).  Hence all
  the vertices of `β` lie *outside* both sides, so the labelling
  `M := restrictSide P e (Outside P e) L` agrees with `L` on `β`
  (`C2.pathSum_restrictSide_erasePath_of_outside`) while vanishing on *every* relator of `P`
  (`C2.restrictSide_outside_vanishes`): on the relators `i ≠ m` because either all their vertices
  are outside the two sides (and then `M = L`, which vanishes there) or none is (and then
  `M = 0`); and on the relator `m` because the arrow of `P.path m` of code `P.edgeOf e` is `e` or
  `e⁻¹`, whose endpoints lie in the two sides.  Thus `M` is an indicable labelling of `P`,
  contradicting `hnon`.

The four quoted pieces of the argument are proved in the sibling files
`C2/extendLabelling_vanishes_of_bridge.lean`, `C2/restrictSide_outside_vanishes.lean`,
`C2/sideLoop_erasePath_of_reachLeft.lean` and `C2/pathSum_restrictSide_erasePath_of_outside.lean`;
only the small lemma `nhl_not_reachRight_start_of_dpath_keepRight` below is proved here.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.Case2Labelling
import Submission.Work.ORLocInd.Howie.C2.extendLabelling_vanishes_of_bridge
import Submission.Work.ORLocInd.Howie.C2.restrictSide_outside_vanishes
import Submission.Work.ORLocInd.Howie.C2.sideLoop_erasePath_of_reachLeft
import Submission.Work.ORLocInd.Howie.C2.pathSum_restrictSide_erasePath_of_outside

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.ORLocInd.Howie.C2

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## A nonempty loop of the kept subgraph starts outside the `ReachRight` side -/

/-- A nonempty loop all of whose arrows are kept by `keepRight P e` starts outside the
`ReachRight` side of the bridge: its last arrow has no endpoint in that side. -/
theorem nhl_not_reachRight_start_of_dpath_keepRight (P : Presentation V) (e : Quiver.Total V)
    {x : V} (β : dpath (keepRight P e) x x) (hβ : β ≠ Quiver.Path.nil) :
    ¬ ReachRight P e x := by
  cases β with
  | nil => exact absurd rfl hβ
  | cons p f => exact fun h => f.2.2 (Or.inr h)

/-! ## The bridge presentation is non-indicable -/

theorem not_hasIndicableLabelling_bridgePresentation {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (m : P.ι)
    (e : Quiver.Total V)
    (he : ∃ g ∈ (P.path m).arrowList, P.edgeOf g = P.edgeOf e)
    (hbrl : ∀ i : P.ι, i ≠ m → Work.ORLocInd.Howie.Avoids P e (P.path i))
    (hbr : ∀ q : Quiver.Path e.right e.left, Work.ORLocInd.Howie.Avoids P e q → False)
    (hnon : ¬ P.HasIndicableLabelling)
    (hside : ¬ Work.ORLocInd.Howie.SideIndicable P m e (Work.ORLocInd.Howie.ReachLeft P e)) :
    ¬ (Work.ORLocInd.Howie.bridgePresentation P m e).HasIndicableLabelling := by
  intro hbrid
  rw [bridgePresentation] at hbrid
  obtain ⟨L', hL', x, β', hβ'⟩ := hbrid
  have hvan := extendLabelling_vanishes_of_bridge P m e hbrl L' hL'
  have hK : ∀ g : Quiver.Total V, (keepRight P e).pred g → P.edgeOf g ≠ P.edgeOf e :=
    fun g hg => hg.1
  by_cases hcase : ReachLeft P e x
  · -- the witness path lies in the `ReachLeft` side: the left side is side-indicable
    refine hside ⟨extendLabelling (keepRight P e) L', x, DelV.erasePath (keepRight P e) x β',
      hvan, sideLoop_erasePath_of_reachLeft P e (keepRight P e) hK β' hcase, ?_⟩
    rw [← pathSum_erasePath (keepRight P e) L' β']
    exact hβ'
  · -- otherwise the witness path lies outside the two sides: `P` is indicable
    have hβ'ne : β' ≠ Quiver.Path.nil := by
      intro h
      rw [h] at hβ'
      exact hβ' (pathSum_nil L'.toFun x)
    have hSx : ¬ ReachRight P e x ∧ ¬ ReachLeft P e x :=
      ⟨nhl_not_reachRight_start_of_dpath_keepRight P e β' hβ'ne, hcase⟩
    refine hnon ⟨restrictSide P e (fun y => ¬ ReachRight P e y ∧ ¬ ReachLeft P e y)
        (extendLabelling (keepRight P e) L'),
      restrictSide_outside_vanishes P hsep m e he _ hvan, x,
      DelV.erasePath (keepRight P e) x β', ?_⟩
    rw [pathSum_restrictSide_erasePath_of_outside P e (keepRight P e) hK
      (extendLabelling (keepRight P e) L') hSx β']
    rw [← pathSum_erasePath (keepRight P e) L' β']
    exact hβ'

end Work.ORLocInd.Howie.C2
