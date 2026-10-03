/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# A free vertex is enough at `l = 1`: HNN splittings over free groups

The `l = 1` case of the target `Work.OROneRel.magnus_step_root_no_eps_zero` asks for a one-relator
group `⟨β | v⟩` with `¬ IsProperPower v`, `relatorNorm v < relatorNorm u`, and an HNN decomposition
`⟨α | u⟩ ≅ HNNExtension (⟨β | v⟩) A B φ`.  Because a generator is never a proper power
(`Work.OROneRel.not_isProperPower_of`) and has norm `1`, the *simplest* possible vertex at `l = 1` is
the free group on `Option γ` presented by the single terminal relator `of none`:

    ⟨Option γ | of none⟩ ≅ F γ      (`Work.OROneRel.presentedGroup_option_none_iso_freeGroup`).

This file records the consequence: **any** HNN splitting of `⟨α | u⟩` over a *free* vertex group
(over subgroups of that free group, which may be proper — the associated subgroups are not required
to be everything) produces the target's conclusion at `l = 1`.  This strictly generalises the two
routes already in the workspace:

* `magnusStepDataOne_of_freeKernel` (`Submission/Work/OROneRel/magnusStepData_cpRelator.lean`) is the
  case `A = B = ⊤` with the free vertex identified as `ker χ` for a primitive killing weight (the
  `⊤`-route, i.e. the semidirect product with `ℤ`);
* `hasMMStepData_of_mul_free` / `mmStepData_of_norm_three` use the case `A = B = ⊥`
  (a free product with `ℤ`).

The root tracking at `l = 1` is automatic: both `PresentedGroup.mk u` and `PresentedGroup.mk v` are
the class of a defining relator, hence `1`.

The hypothesis of the main theorem is therefore the sharp `l = 1` obligation in "free vertex" form:
`⟨α | u⟩` must be an HNN extension of a free group.  For `d = 2` this holds
(`isFreeGroup_ker_rescaledChi` + the `⊤`-route, since the kernel of a primitive killing character is
then free and the extension splits); for `d ≥ 3` it is open, and for `l ≥ 2` the vertex necessarily
carries `ℤ/l`-torsion, so the free-vertex statement is *not* available there (see
`NOTES_magnus_step_root_no_eps_zero.md`, SESSION 6 §3 and SESSION 7 §2).
-/

import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv
import Submission.Work.OROneRel.presentedGroup_option_none_iso_freeGroup
import Submission.Work.OROneRel.not_isProperPower_of

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The norm of a generator is `1`. -/
private theorem relatorNorm_of_gen {γ : Type u} (x : γ) : relatorNorm (FreeGroup.of x) = 1 := by
  classical
  rw [relatorNorm, FreeGroup.norm_of]

/-- **The target's conclusion at `l = 1` from an HNN splitting over a free vertex group.**

If `⟨α | u ^ 1⟩` is isomorphic to the HNN extension of the free group `F γ` over arbitrary subgroups
`A`, `B ≤ F γ` (with the isomorphism as given), then the Magnus step holds for `u` at `l = 1` with

* `β = Option γ` and `v = FreeGroup.of none` (so that `⟨β | v ^ 1⟩ ≅ F γ` through
  `Work.OROneRel.presentedGroup_option_none_iso_freeGroup`),
* `relatorNorm v = 1 < relatorNorm u` (from `2 ≤ relatorNorm u`) and `¬ IsProperPower v`,
* the associated subgroups `A'`, `B'` and the comparison isomorphism obtained by transporting
  `A`, `B`, `φ` along `⟨β | v⟩ ≅ F γ` (`Work.OROneRel.hnnExtension_iso_of_baseMulEquiv`),
* the tracking element `c = 1`, since at `l = 1` both classes involved are trivial. -/
theorem magnusStepData_one_of_hnnOfFreeGroup {α : Type u} (u : FreeGroup α)
    (hn : 2 ≤ relatorNorm u) (γ : Type u) (A B : Subgroup (FreeGroup γ)) (φ : A ≃* B)
    (e : PresentedGroup ({u ^ 1} : Set (FreeGroup α)) ≃* HNNExtension (FreeGroup γ) A B φ) :
    MagnusStepData u 1 := by
  classical
  -- the vertex presentation `⟨Option γ | of none⟩ ≅ F γ`
  obtain ⟨eB⟩ := presentedGroup_option_none_iso_freeGroup (γ := γ)
  -- transport the whole HNN structure along `eB.symm`
  obtain ⟨A', B', φ', E, -, -, -, -⟩ :=
    hnnExtension_iso_of_baseMulEquiv eB.symm A B φ
  refine ⟨Option γ, FreeGroup.of (none : Option γ), not_isProperPower_of (none : Option γ), ?_, ?_⟩
  · -- the norm of the root
    rw [relatorNorm_of_gen]
    omega
  · -- the vertex is the free group `F γ` presented by the terminal relator `of none`
    rw [show ({(FreeGroup.of (none : Option γ)) ^ 1} : Set (FreeGroup (Option γ)))
        = {FreeGroup.of (none : Option γ)} from by rw [pow_one]]
    exact ⟨A', B', φ', e.trans E, ⟨1, by
      rw [PresentedGroup.one_of_mem (Set.mem_singleton_iff.mpr (by rw [pow_one])),
        PresentedGroup.one_of_mem (Set.mem_singleton _)]
      simp⟩⟩

/-- **Sanity check: the `⊤`-route is the special case of `A = B = ⊤`.**  Recorded to document that
`magnusStepData_one_of_hnnOfFreeGroup` really does subsume the free-kernel route of
`Work.OROneRel.magnusStepDataOne_of_freeKernel` (which realises `⟨α | u⟩` as `F γ ⋊ ℤ`, i.e. the HNN
with both associated subgroups the whole vertex). -/
example {α : Type u} (u : FreeGroup α) (hn : 2 ≤ relatorNorm u) (γ : Type u)
    (φ : (⊤ : Subgroup (FreeGroup γ)) ≃* (⊤ : Subgroup (FreeGroup γ)))
    (e : PresentedGroup ({u ^ 1} : Set (FreeGroup α)) ≃*
      HNNExtension (FreeGroup γ) ⊤ ⊤ φ) :
    MagnusStepData u 1 :=
  magnusStepData_one_of_hnnOfFreeGroup u hn γ ⊤ ⊤ φ e

end Work.OROneRel
