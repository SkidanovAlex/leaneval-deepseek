import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pinning integrability: the `(η+4)`-weighted `cos²·Ψ²` tail

The pinning argument at the corner `θ = π/2` consumes the integrability of the *tail*

`θ ↦ (cos θ · Ψ z θ)² · sin(2θ)^{-(η+4)}` on `(π/6, π/2)`

from the integrability of the `ℋ`-type integrand `(Ψ z θ / cos θ)² · sin(2θ)^{-η}` on the
closed angular interval.  The two integrands differ pointwise by the factor

`cos⁴θ · sin(2θ)^{-4} = 1 / (16 sin⁴θ)`,

and on `(π/6, π/2)` we have `sin θ ≥ 1/2`, so this factor is `≤ 1`.  Hence the tail is
dominated by the given integrand and integrability transfers by `Integrable.mono'`.
-/

namespace Work.FTS_EllLimOK.Pinning

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- **Pointwise comparison.**  If `0 < c ≤ S` then the `(η+4)`-weighted square is dominated by
the `η`-weighted one:

`|(c p)² S^{-(η+4)}| ≤ (p/c)² S^{-η}`.

Indeed the quotient of the two sides is `c⁴ S^{-4} ≤ 1`, which is exactly `c⁴ ≤ S⁴`. -/
private lemma abs_cos_mul_sq_rpow_le {η c p S : ℝ} (hc : 0 < c) (hS : 0 < S) (hcs : c ≤ S) :
    |(c * p) ^ 2 * S ^ (-(η + 4))| ≤ (p / c) ^ 2 * S ^ (-η) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hS4 : (0 : ℝ) < S ^ 4 := by positivity
  have hc4le : c ^ 4 ≤ S ^ 4 := pow_le_pow_left₀ hc.le hcs 4
  have hSinv : S ^ (-4 : ℝ) = (S ^ 4)⁻¹ := by
    rw [Real.rpow_neg hS.le]
    norm_num
  -- `c⁴ / S⁴ ≤ 1`
  have hmain : c ^ 4 * (S ^ 4)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact div_le_one_of_le₀ hc4le hS4.le
  -- `c² / S⁴ ≤ 1 / c²`
  have hratio : c ^ 2 * (S ^ 4)⁻¹ ≤ (c ^ 2)⁻¹ := by
    have h1 : (c ^ 2 * (S ^ 4)⁻¹) * c ^ 2 ≤ ((c ^ 2)⁻¹) * c ^ 2 := by
      rw [show (c ^ 2 * (S ^ 4)⁻¹) * c ^ 2 = c ^ 4 * (S ^ 4)⁻¹ by ring,
        inv_mul_cancel₀ (ne_of_gt hc2)]
      exact hmain
    exact (mul_le_mul_iff_left₀ hc2).mp h1
  have hSpow : S ^ (-(η + 4)) = (S ^ 4)⁻¹ * S ^ (-η) := by
    rw [show -(η + 4) = -η + -4 by ring, Real.rpow_add hS, hSinv]
    ring
  have hnn : 0 ≤ (c * p) ^ 2 * S ^ (-(η + 4)) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hS _))
  rw [abs_of_nonneg hnn, mul_pow, hSpow]
  calc c ^ 2 * p ^ 2 * ((S ^ 4)⁻¹ * S ^ (-η))
      = c ^ 2 * (S ^ 4)⁻¹ * (p ^ 2 * S ^ (-η)) := by ring
    _ ≤ (c ^ 2)⁻¹ * (p ^ 2 * S ^ (-η)) :=
        mul_le_mul_of_nonneg_right hratio
          (mul_nonneg (sq_nonneg p) (le_of_lt (Real.rpow_pos_of_pos hS _)))
    _ = (p / c) ^ 2 * S ^ (-η) := by rw [div_pow, div_eq_mul_inv]; ring

theorem integrableOn_cos_sq_rpow_tail {η : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (hz : 0 < z)
    (h : MeasureTheory.IntegrableOn
      (fun θ => (Ψ z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 4)))
      (Set.Ioo (Real.pi / 6) (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo (Real.pi / 6) (Real.pi / 2)
  have hs_meas : MeasurableSet s := measurableSet_Ioo
  -- the interval is contained in the closed angular interval
  have hsub : s ⊆ Work.Spaces.Iθ := fun _ hx =>
    ⟨le_of_lt (by linarith [Real.pi_pos, hx.1]), le_of_lt hx.2⟩
  have hH : IntegrableOn (fun θ : ℝ => (Ψ z θ / Real.cos θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-η)) s := h.mono_set hsub
  -- positivity of `sin 2θ` and `cos θ` on `s`
  have hSpos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
  have hcpos : ∀ θ ∈ s, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  -- and `cos θ ≤ sin 2θ`, because `sin θ ≥ sin (π/6) = 1/2`
  have hcS : ∀ θ ∈ s, Real.cos θ ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have hsin : (1 : ℝ) / 2 ≤ Real.sin θ := by
      have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := Real.pi / 6) (y := θ) (by linarith [Real.pi_pos]) (le_of_lt hθ.2) (le_of_lt hθ.1)
      rwa [Real.sin_pi_div_six] at h1
    rw [Real.sin_two_mul]
    nlinarith [hsin, (hcpos θ hθ).le]
  -- the tail integrand is continuous on `s`
  have hcont : ContinuousOn (fun θ : ℝ => (Real.cos θ * Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(η + 4))) s := by
    have hΨ : ContinuousOn (fun θ : ℝ => Ψ z θ) s :=
      ((hsm.curry_θ hz).continuousOn).mono fun _ hθ =>
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ((Real.continuous_cos.continuousOn.mul hΨ).pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        fun _ hθ => Or.inl (ne_of_gt (hSpos _ hθ)))
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.cos θ * Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(η + 4))) (volume.restrict s) :=
    hcont.aestronglyMeasurable hs_meas
  change Integrable (fun θ : ℝ => (Real.cos θ * Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(η + 4))) (volume.restrict s)
  refine Integrable.mono' hH hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' hs_meas]
  exact Filter.Eventually.of_forall fun θ hθ =>
    abs_cos_mul_sq_rpow_le (hS := hSpos θ hθ) (hc := hcpos θ hθ) (hcs := hcS θ hθ)

end Work.FTS_EllLimOK.Pinning
