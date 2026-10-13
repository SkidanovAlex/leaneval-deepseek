/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.FinalCore` — (1) + (1a′) at the lead's own type

The integration redesign makes this area the owner of `FinalV2.Producers.core1_1a3`:

> one linear `E` at the profile exponent carrying the two packages on the class `C` **and** the
> order-`3` limit closure `EllLimOK3`, from `ClassC.ExistsEllSolC`.

This module states and proves that conclusion **from the two small-α obligations** of the design
(`Defs3.SmallCompact3` and `Defs3.SmallUniq3`), at the lead's `Work.FTS.FinalV2.EllLimOK3` — so that
the moment those two land, the unconditional producer is

  `core1_1a3_of_small_obligations hE hcomp huniq`.

(The names `core1_1a3_proved` / the identical type requested by the lead are delivered *once the two
obligations are closed*; until then this is the proved conditional form, with the obligations
dispatched — `ClosedUniq3_small` is the uniqueness port and is owned here.)

The bridge `Lead_EllLimOK3_iff` records that the area's `Defs3.EllLimOK3` is the lead's
`FinalV2.EllLimOK3` (identical bodies).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.Closed3
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS_EllLimOK.exists_ellLimOK3_of_closed
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.FinalV2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- The area's `EllLimOK3` is the lead's `FinalV2.EllLimOK3`, verbatim. -/
theorem Lead_EllLimOK3_iff (α : ℝ) (E : Fn → Fn) :
    EllLimOK3 α E ↔ Work.FTS.FinalV2.EllLimOK3 α E :=
  Iff.rfl

/-- **Final (1) + (1a′) from `ExistsEllSolC` and the two small-α obligations**, stated at the
lead's `Work.FTS.FinalV2.EllLimOK3` — the exact conclusion of `FinalV2.Producers.core1_1a3`.

The thresholds are threaded (`min α₀ α₁`): `α₀` is `ExistsEllSolC`'s, `α₁` is the threshold of the
two obligations. -/
theorem core1_1a3_of_small_obligations (hE : Work.FTS.ClassC.ExistsEllSolC)
    (hcomp : SmallCompact3) (huniq : SmallUniq3) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
      Work.FTS.FinalV2.EllLimOK3 (pExp α) E := by
  obtain ⟨Ce, hCe, α₀, hα₀, hPkg⟩ := hE
  obtain ⟨αg, hαg, hglue⟩ := ClosedE3_of_smallObligations hcomp huniq
  refine ⟨Ce, hCe, min α₀ αg, lt_min hα₀ hαg, fun α hα hle => ?_⟩
  have hα₀' : pExp α ≤ α₀ := le_trans hle (min_le_left _ _)
  have hαg' : pExp α ≤ αg := le_trans hle (min_le_right _ _)
  have hp : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  obtain ⟨E, hE1⟩ := hPkg (pExp α) hp hα₀'
  have hsol : ∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
      Work.FTS.StrongGlobal.IsBslSolPos (pExp α) g (E g) :=
    fun g hg => Work.FTS.StrongGlobal.IsBslSol.toPos (hE1 g hg).1.sol
  have hsm : ∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
      ContDiffOn ℝ 3 (Function.uncurry (E g)) Work.Construction.Qd :=
    fun g hg => contDiffOn_of_smoothOpen (hE1 g hg).1.smooth 3
  have hcl : ClosedE3 (pExp α) E := hglue (pExp α) hp hαg' Ce E hE1
  obtain ⟨E', hE'C, hok⟩ := exists_ellLimOK3_of_closed E hsol hsm hcl
  refine ⟨E', fun g hg => ?_, (Lead_EllLimOK3_iff _ E').mp hok⟩
  rw [hE'C g hg]
  exact hE1 g hg

end Work.FTS_EllLimOK
