import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.Coercivity.K_facts
import Submission.Work.FTS.EllipticEst.ang_integrals
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.CAux.integrableOn_GamK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Technical preliminaries for `GammaL2Bnd`

The elementary ingredients of the angular `L²`-estimate `|Γ/c − K|₂ ≤ 7/10`
(the paper's `GammaAssumption`), with `Γ(θ) = (sinθ cos²θ)^{α/3}`,
`K(θ) = 3 sinθ cos²θ` on `Iθ = [0,π/2]`:

* the Bernoulli-type `rpow` inequality `u(1−u^p) ≤ p(1−u)` for `0 ≤ u ≤ 1`;
* the pointwise core `(u^p − 3u)² ≤ (1 − 3u)² + 6p(1−u)`;
* the three angular integrals `∫_{Iθ} 1 = π/2`, `∫_{Iθ} sinθcos²θ = 1/3`,
  `∫_{Iθ} (sinθcos²θ)² = π/32`;
* the resulting bound `∫_{Iθ}(Γ − K)² ≤ 25π/32 − 2 + 6p(π/2)`;
* the normalisation bounds `c ≤ 1` and `1 − c ≤ 3p(π/2)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.GamL2

/-! ## The elementary `rpow` inequality -/

/-- For `0 < u ≤ 1` and `p ≥ 0`: `u (1 − u^p) ≤ p (1 − u)`.

This is the Bernoulli-type inequality obtained from `1 − u^p ≤ p(−log u)` (which
is `1 − e^{p log u} ≤ −p log u`, i.e. `1 + x ≤ e^x` applied to `x = p log u`) and
`−log u ≤ (1−u)/u` (which is `log x ≤ x − 1` at `x = u⁻¹`). -/
lemma unit_sub_pow_le (u p : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hp : 0 ≤ p) :
    u * (1 - u ^ p) ≤ p * (1 - u) := by
  have h1 : 1 - u ^ p ≤ p * (-Real.log u) := by
    have h := Real.add_one_le_exp (Real.log u * p)
    rw [Real.rpow_def_of_pos hu0]
    linarith
  have h2 : -Real.log u ≤ (1 - u) / u := by
    have h := Real.one_sub_inv_le_log_of_pos hu0
    have h3 : -Real.log u ≤ u⁻¹ - 1 := by linarith
    have h4 : u⁻¹ - 1 = (1 - u) / u := by field_simp
    rwa [h4] at h3
  have h3 : u * (1 - u ^ p) ≤ u * (p * (-Real.log u)) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hu0)
  refine le_trans h3 ?_
  have h5 : u * (p * (-Real.log u)) ≤ u * (p * ((1 - u) / u)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hp) (le_of_lt hu0)
  have h6 : u * (p * ((1 - u) / u)) = p * (1 - u) := by field_simp
  rwa [h6] at h5

/-- The same inequality in the form used for `u = sinθcos²θ` (where `u` may vanish
at the endpoints of `Iθ`). -/
lemma unit_sub_pow_le' (u p : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hp : 0 ≤ p) :
    u * (1 - u ^ p) ≤ p * (1 - u) := by
  rcases hu0.eq_or_lt with h | h
  · subst h
    rw [zero_mul, sub_zero, mul_one]
    exact hp
  · exact unit_sub_pow_le u p h hu1 hp

/-- The pointwise core of the estimate: for `0 ≤ u ≤ 1` and `0 < p ≤ 1`,

  `(u^p − 3u)² ≤ 1 − 6u + 6p(1 − u) + 9u² = (1 − 3u)² + 6p(1 − u)`.

Indeed `(u^p − 3u)² = (u^p)² − 6u·u^p + 9u²`, and `(u^p)² ≤ 1` while
`u·u^p ≥ u − p(1 − u)` (`unit_sub_pow_le'`). -/
lemma pow_sub_three_mul_sq_le (u p : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    (u ^ p - 3 * u) ^ 2 ≤ 1 - 6 * u + 6 * p * (1 - u) + 9 * u ^ 2 := by
  rcases eq_or_lt_of_le hu0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt hp0)]
    nlinarith [hp0]
  · have hup : u ^ p ≤ 1 := Real.rpow_le_one hu0 hu1 (le_of_lt hp0)
    have hup0 : 0 ≤ u ^ p := Real.rpow_nonneg hu0 p
    have hlow : u - p * (1 - u) ≤ u * u ^ p := by
      have h' := unit_sub_pow_le u p h hu1 (le_of_lt hp0)
      nlinarith [h']
    have hsq : (u ^ p - 3 * u) ^ 2 = (u ^ p) ^ 2 - 6 * (u * u ^ p) + 9 * u ^ 2 := by ring
    have hsq2 : (u ^ p) ^ 2 ≤ 1 := by nlinarith [hup, hup0]
    rw [hsq]
    nlinarith [hsq2, hlow]

/-! ## The three elementary angular integrals -/

/-- `∫_{Iθ} 1 = vol(Iθ) = π/2`. -/
lemma int_Iθ_one : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- `∫_{Iθ} sinθ cos²θ = 1/3`, from `∫_{Iθ} K = 1` and `K = 3 sinθcos²θ`. -/
lemma int_Iθ_sinCos2 : (∫ θ in Work.Spaces.Iθ, Real.sin θ * Real.cos θ ^ 2) = 1 / 3 := by
  have h : (∫ θ in Work.Spaces.Iθ, 3 * (Real.sin θ * Real.cos θ ^ 2)) = 1 := by
    rw [← Work.Coercivity.integral_Itheta_K]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Spaces.K]; ring
  rw [MeasureTheory.integral_const_mul] at h
  linarith

/-- `∫_{Iθ} (sinθ cos²θ)² = π/32`. -/
lemma int_Iθ_sinCos2_sq :
    (∫ θ in Work.Spaces.Iθ, (Real.sin θ * Real.cos θ ^ 2) ^ 2) = Real.pi / 32 := by
  simpa only [Work.Elliptic.sinCos2] using Work.FTS.EllipticEst.ang_integrals.2.1

/-! ## Integrability on `Iθ` -/

/-- A continuous function on the compact interval `Iθ` is integrable there. -/
lemma integrableOn_of_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    IntegrableOn f Work.Spaces.Iθ := hf.integrableOn_Icc

end Work.FTS.CoercivityFix.Coer1T.GamL2
