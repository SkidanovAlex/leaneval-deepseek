import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_EllLimOK.L2Mem_of_HkMem_zero
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(Ψ z θ / cos θ)²` on the angular interval, from `ℋ⁰`-membership

The `ℋ⁰`-weighted integrand of `g` is

`HkIntegrand α 0 g z θ = (g z θ · w(z) / sin(2θ)^{η/2})²`

(`Work.FTS_EllLimOK.HkIntegrand_zero_eq`), and on the *interior* of the quadrant the weight
`w(z)/sin(2θ)^{η/2}` is `≥ 1` (`Work.FTS_EllLimOK.one_le_weight`): for every `z > 0` the
weighted integrand therefore dominates `(g z θ)²` *pointwise* on `(0, π/2)`.  Since
`HkMem α 0 g` provides the integrability of the weighted integrand on the *closed* angular
interval `Iθ = [0, π/2]`, domination yields the integrability of `(g z ·)²` on the open
interval — the a.e. strong measurability of `(g z ·)²` coming from continuity of the slice.

Applied to `g z θ = Ψ z θ / cos θ` with `Ψ` smooth on the open quadrant (whose `θ`-slice at
`z > 0` is continuous on `(0, π/2)`, and `cos` does not vanish there) this is exactly the
statement consumed by the pinning argument at the corner `θ = π/2`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Pinning

set_option autoImplicit false

/-- **Integrability on the open angular interval from `ℋ⁰`-membership.**  If `g ∈ ℋ⁰`
(weighted) and the angular slice `θ ↦ g z θ` is continuous on `(0, π/2)` at some `z > 0`,
then `(g z ·)²` is integrable on `(0, π/2)`. -/
lemma integrableOn_sq_of_HkMem_zero {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn (fun θ : ℝ => g z θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (g z θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
  -- the weighted integrand is integrable on the closed angular interval
  have hIθ : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ :=
    hmem.1 z (Set.mem_Ici.mpr hz.le)
  have hone : IntegrableOn (fun θ : ℝ => (g z θ
      * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS_EllLimOK.HkIntegrand_zero_eq] using hIθ
  -- and hence on the open interval
  have hsub : IntegrableOn (fun θ : ℝ => (g z θ
      * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hone.mono_set Set.Ioo_subset_Icc_self
  -- domination there by the weighted integrand, which is `≥` it in the interior
  refine Integrable.mono' hsub ?_ ?_
  · exact (hcont.pow 2).aestronglyMeasurable measurableSet_Ioo
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hb := Work.FTS_EllLimOK.sq_le_HkIntegrand_zero_pt (α := α) hz hθ.1 hθ.2 (g := g)
    rw [Work.FTS_EllLimOK.HkIntegrand_zero_eq] at hb
    simpa only [Real.norm_of_nonneg (sq_nonneg (g z θ))] using hb

theorem integrableOn_div_cos_sq_of_HkMem {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmem : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ)) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Ψ z θ / Real.cos θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hcont : ContinuousOn (fun θ : ℝ => Ψ z θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((hsm.curry_θ hz).continuousOn).div Real.continuousOn_cos ?_
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  exact integrableOn_sq_of_HkMem_zero hmem hz hcont

end Work.FTS_EllLimOK.Pinning
