/-
Pointwise estimates for the L¹-convergence of mollifications (`Work.MRMT.Weyl.moll_tendsto_L1_loc`).

* `moll_sub_integral`: since the kernel has integral one, subtracting `f z` from the mollification
  at `z` writes it as the integral of `ρ y • (f (z - y) - f z)`;
* `norm_moll_sub_le`: for a nonnegative kernel this gives the pointwise bound
  `‖moll ρ f z - f z‖ ≤ ∫ y, ρ y * ‖f (z - y) - f z‖`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

noncomputable section

open Work.MRMT

/-- Pointwise identity for the mollification: if `ρ` is continuous, has compact support and
`∫ ρ = 1`, then `moll ρ f z - f z = ∫ y, (ρ y : ℂ) * (f (z - y) - f z)`. -/
theorem moll_sub_integral {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hρ1 : ∫ y, ρ y = 1) (z : ℂ) :
    moll ρ f z - f z = ∫ y, (ρ y : ℂ) * (f (z - y) - f z) := by
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρcs
  have hint : Integrable (fun t => (ρ t : ℂ) * f (z - t)) volume := by
    have h := hρcs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρc hf z
    simp only [ConvolutionExistsAt] at h
    exact h
  have hconst : Integrable (fun t => (ρ t : ℂ) * f z) volume := hρint.ofReal.mul_const _
  have h1 : ∫ y, (ρ y : ℂ) = ((∫ y, ρ y : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hρint
  have hfz : f z = ∫ t, (ρ t : ℂ) * f z := by
    rw [integral_mul_const]
    rw [h1, hρ1]
    simp
  conv_lhs => rw [moll_apply ρ f z, hfz, ← integral_sub hint hconst]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

/-- Pointwise bound for the difference between a mollification and the original function, in terms
of the L¹-difference of translates of `f`. -/
theorem norm_moll_sub_le {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hρ1 : ∫ y, ρ y = 1)
    (hρnn : ∀ y, 0 ≤ ρ y) (z : ℂ) :
    ‖moll ρ f z - f z‖ ≤ ∫ y, ρ y * ‖f (z - y) - f z‖ := by
  rw [moll_sub_integral hf hρc hρcs hρ1 z]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ‖(ρ y : ℝ) • (f (z - y) - f z)‖ = ρ y * ‖f (z - y) - f z‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρnn y)]

end

end Work.MRMT.Weyl
