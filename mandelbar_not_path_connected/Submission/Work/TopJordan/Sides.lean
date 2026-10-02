/-
# The two sides of a Jordan curve, unconditionally

`Work.Top.Sides C` (`Submission/Work/Top/Jordan.lean`) packages the bounded and the unbounded
component of the complement of a Jordan curve `C`, together with the facts that both are open,
preconnected, disjoint, jointly fill `Cᶜ`, that the bounded one is bounded, the unbounded one is
unbounded, and that both have `C` as frontier.  The only field of that area that is not proved is
`Work.Top.JordanForm`, the existence of such a pair.

Here the existence is discharged from the commons Jordan curve theorem
(`Commons.Topology.Jordan.plane_separation` and
`Commons.Topology.Connected.frontier_component_compl_range`):

* `exists_sidesOfCurve` / `sidesOfCurve γ hγ : Work.Top.Sides (Set.range γ)` for an injective
  continuous map `γ : C(Circle, ℂ)` of the circle;
* `exists_sidesOf` / `sidesOf hC : Work.Top.Sides C` for any `Work.Top.IsJordanCurve C`.

Consequently every lemma about `Work.Top.Sides` in the area `Submission/Work/Top` is available
without the hypothesis `Work.Top.JordanForm`.
-/
import Mathlib
import Submission.Work.Top.Jordan
import Submission.Work.TopJordan.Components
import Submission.Work.TopJordan.CurveModel
import Submission.Commons.Topology.Jordan.plane_separation
import Submission.Commons.Topology.Connected.frontier_component_compl_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Set

namespace Work.TopJordan

noncomputable section

/-- **The two sides of a Jordan curve given as an injective continuous map of `Circle`.**

The bounded side is the connected component of the complement containing an arbitrary point of
the bounded open piece delivered by `Commons.Topology.Jordan.plane_separation`, and likewise for
the unbounded side; the frontiers are `Commons.Topology.Connected.
frontier_component_compl_range`. -/
theorem exists_sidesOfCurve (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) :
    ∃ S : Work.Top.Sides (Set.range γ), True := by
  classical
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hd, hUb, hVb, hUV⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγ
  obtain ⟨u, hu⟩ := hUc.1
  obtain ⟨v, hv⟩ := hVc.1
  have hUsub : U ⊆ (Set.range γ)ᶜ := by rw [← hUV]; exact Set.subset_union_left
  have hVsub : V ⊆ (Set.range γ)ᶜ := by rw [← hUV]; exact Set.subset_union_right
  have hnotpre : ¬ IsPreconnected (Set.range γ)ᶜ :=
    not_isPreconnected_compl_of_open_split hUo hVo hd hUc.1 hVc.1 hUV
  have hUeq : connectedComponentIn (Set.range γ)ᶜ u = U :=
    eq_connectedComponentIn_of_open_split hUo hVo hUV hd hUc.2 hu
  have hVeq : connectedComponentIn (Set.range γ)ᶜ v = V :=
    eq_connectedComponentIn_of_open_split hVo hUo (by rw [Set.union_comm, hUV]) hd.symm hVc.2 hv
  have hopen : IsOpen (Set.range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hfrontU :=
    Commons.Topology.Connected.frontier_component_compl_range γ hγ hnotpre u (hUsub hu)
  have hfrontV :=
    Commons.Topology.Connected.frontier_component_compl_range γ hγ hnotpre v (hVsub hv)
  exact ⟨
    { I := connectedComponentIn (Set.range γ)ᶜ u
      O := connectedComponentIn (Set.range γ)ᶜ v
      isOpen_I := hopen.connectedComponentIn
      isOpen_O := hopen.connectedComponentIn
      union_eq := by rw [hUeq, hVeq, hUV]
      disjoint := by rw [hUeq, hVeq]; exact hd
      preconnected_I := isPreconnected_connectedComponentIn
      preconnected_O := isPreconnected_connectedComponentIn
      bounded_I := by rw [hUeq]; exact hUb
      unbounded_O := by
        intro n
        rw [hVeq]
        exact exists_norm_ge_of_not_isBounded hVb n
      frontier_I := hfrontU
      frontier_O := hfrontV }, trivial⟩

/-- The two sides of a Jordan curve given as an injective continuous map of `Circle`. -/
noncomputable def sidesOfCurve (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) :
    Work.Top.Sides (Set.range γ) :=
  Classical.choose (exists_sidesOfCurve γ hγ)

/-- **The two sides of a Jordan curve `C`.** -/
theorem exists_sidesOf {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    ∃ S : Work.Top.Sides C, True := by
  classical
  obtain ⟨γ, hγ, hrange⟩ := hC
  have h1 : ∃ S : Work.Top.Sides (Set.range γ), True :=
    ⟨(range_toCircle γ) ▸ sidesOfCurve (toCircle γ) (toCircle_injective hγ), trivial⟩
  rwa [hrange] at h1

/-- **The two sides of a Jordan curve `C`.** -/
noncomputable def sidesOf {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) : Work.Top.Sides C :=
  Classical.choose (exists_sidesOf hC)

/-- The sides of `Set.range γ` have `Set.range γ` as frontier. -/
@[simp] theorem frontier_sidesOfCurve_I (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) :
    frontier (sidesOfCurve γ hγ).I = Set.range γ :=
  (sidesOfCurve γ hγ).frontier_I

/-- The sides of `Set.range γ` have `Set.range γ` as frontier. -/
@[simp] theorem frontier_sidesOfCurve_O (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) :
    frontier (sidesOfCurve γ hγ).O = Set.range γ :=
  (sidesOfCurve γ hγ).frontier_O

end

end Work.TopJordan
