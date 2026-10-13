/-
Copyright: work module for the Elgindi finite-time singularity project.

# Extraction of a pure `D_z`-slot of `HkMem` in the unweighted form

`Work.Spaces.HkMem α k g` records the integrability of the *weighted* angular sums inside the
`ℋ^k`-integrand `Work.Spaces.HkIntegrand`, in particular of the single term

  `θ ↦ (D_z^i g (z,θ) · w(z) / sin(2θ)^{η/2})²`.

The estimate that consumes this fact (`remov/SourceBound`) needs the *unweighted* form

  `θ ↦ (D_z^i g (z,θ))² · sin(2θ)^{-η}`,

which differs from the weighted one by the positive constant `w(z)²` (the identity
`Work.FTS.EllipticEst.mul_w_sin_rpow_sq`).  Since the honest measure-theoretic restriction of
integrability across a.e. equality requires measurability of the target, the a.e. strong
measurability of the target slice is taken as a hypothesis here; everything else is immediate
from the a.e. domination

  `(D_z^i g (z,θ))² · sin(2θ)^{-η} ≤ w(z)^{-2} · HkIntegrand α k g z θ`

(valid for every `θ ∈ Iθ`, from `Work.Spaces.sq_le_HkIntegrand_z`) and `Integrable.mono'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

theorem integrableOn_DzIter_sq_mul_sEta {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) (i : ℕ) (hi : i ≤ k) {z : ℝ} (hz : 0 < z)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  -- the radial weight is positive, so its square is invertible
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwpos)
  set c : ℝ := ((Work.Spaces.w z) ^ 2)⁻¹ with hc
  have hcnonneg : 0 ≤ c := by rw [hc]; positivity
  -- dominate by `c · HkIntegrand`, which is integrable on the angular slice
  refine MeasureTheory.Integrable.mono' ((hmem.1 z hzI).const_mul c) haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
  have hE : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hE)]
  -- the weighted summand is a nonnegative summand of `HkIntegrand`
  have hT := Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi
  rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq (Work.Spaces.DzIter i g z θ) (Work.Spaces.w z) hθ]
    at hT
  have hcW : c * (Work.Spaces.w z) ^ 2 = 1 := by rw [hc]; exact inv_mul_cancel₀ hw2ne
  calc (Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (c * (Work.Spaces.w z) ^ 2)
          * ((Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        rw [hcW, one_mul]
    _ = c * ((Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) := by ring
    _ ≤ c * Work.Spaces.HkIntegrand α k g z θ := mul_le_mul_of_nonneg_left hT hcnonneg

end Work.FTS.EllipticEst.remov.SourceBound
