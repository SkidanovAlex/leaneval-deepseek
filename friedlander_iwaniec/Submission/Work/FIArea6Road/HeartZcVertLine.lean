import Mathlib
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16.mellin_inversion

set_option autoImplicit false

namespace Work.FIArea6Road

open MeasureTheory intervalIntegral

/-- `∫_a^b (1 + (θy)²)⁻¹ dy ≤ π/θ` for `θ > 0` (with `a, b : ℝ` arbitrary: the substitution
`u = θy` gives `θ⁻¹ (arctan (θb) - arctan (θa))` and `arctan` lies in `(-π/2, π/2)`). -/
private lemma integral_one_add_mul_sq_inv_le (θ a b : ℝ) (hθ : 0 < θ) :
    ∫ y in a..b, (1 + (θ * y) ^ 2)⁻¹ ≤ Real.pi / θ := by
  have hsub := intervalIntegral.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) hθ.ne'
      (a := a) (b := b)
  have harctan : Real.arctan (θ * b) - Real.arctan (θ * a) ≤ Real.pi := by
    have h1 := Real.arctan_lt_pi_div_two (θ * b)
    have h2 := Real.neg_pi_div_two_lt_arctan (θ * a)
    linarith
  rw [hsub, integral_inv_one_add_sq]
  calc θ⁻¹ • (Real.arctan (θ * b) - Real.arctan (θ * a))
      = θ⁻¹ * (Real.arctan (θ * b) - Real.arctan (θ * a)) := by rw [smul_eq_mul]
    _ ≤ θ⁻¹ * Real.pi := mul_le_mul_of_nonneg_left harctan (inv_nonneg.mpr hθ.le)
    _ = Real.pi / θ := by rw [div_eq_mul_inv]; ring

theorem HeartZcVertLine
    (Pa : Work.FITop.Params) (p : ℝ → ℝ) (Zc : ℂ → ℂ) (σ K : ℝ)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hpd : ∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ)))
    (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (hK : 0 ≤ K)
    (hZc : ∀ y : ℝ, |y| ≤ Work.FIArea6Hecke.heightT Pa →
        ‖Zc ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K) :
    ‖∫ y in (-(Work.FIArea6Hecke.heightT Pa))..(Work.FIArea6Hecke.heightT Pa),
        mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I)
          * Zc ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ Real.pi * (10 ^ 7 * K) * Pa.N ^ σ := by
  have hNpos : 0 < Pa.N := by have := Pa.hN1; linarith
  have hθpos : 0 < Pa.θ := Pa.hθ0
  -- the smoothing parameter is at most `1`
  have hθ1 : Pa.θ ≤ 1 := by
    rw [Pa.hθ]
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
    · have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
      have hlog3 : (1 : ℝ) < Real.log (Pa.x : ℝ) := by
        have h3 : Real.exp 1 < (Pa.x : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three hx3
        have h4 := Real.log_lt_log (Real.exp_pos 1) h3
        rwa [Real.log_exp] at h4
      linarith
    · have h2 : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by norm_num
      linarith [Pa.hA, Pa.hA', h2]
  -- the second derivative bound in the normalisation required by `mellin_decay`
  have hd2 : ∀ u : ℝ, |iteratedDeriv 2 p u| ≤ 1048576 / (Pa.θ * Pa.N) ^ 2 := by
    intro u
    have h := hpd 2 (by norm_num) u
    have hc : Work.FITop4.cMoll 2 = 1048576 := by unfold Work.FITop4.cMoll; norm_num
    rw [hc] at h
    have hexp : (-((2 : ℕ) : ℝ)) = -(2 : ℝ) := by norm_num
    rw [hexp] at h
    have key : (Pa.θ * Pa.N) ^ (-(2 : ℝ)) = ((Pa.θ * Pa.N) ^ 2)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt (mul_pos hθpos hNpos)), Real.rpow_two]
    rw [key] at h
    rwa [div_eq_mul_inv]
  set T : ℝ := Work.FIArea6Hecke.heightT Pa with hT
  have hTpos : 0 < T := by
    rw [hT]; unfold Work.FIArea6Hecke.heightT; positivity
  have hle : -T ≤ T := by linarith
  -- **(16.28)**: the pointwise decay of the Mellin transform, off the single point `y = 0`
  have hpt : ∀ y : ℝ, y ≠ 0 →
      ‖mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ 10000000 * Pa.θ * Pa.N ^ σ * (1 + (Pa.θ * y) ^ 2)⁻¹ := by
    intro y hy
    rw [Work.FIArea5.S16.mellin_mollifier_eq_interval hNpos hθpos hpsupp]
    exact Work.FIArea5.S16.mellin_decay p Pa.N Pa.θ hNpos hθpos hθ1 hpC hp0 hp1 hpsupp hd2
      σ y hσ hσ2 hy
  have hcontg : Continuous (fun y : ℝ => (1 + (Pa.θ * y) ^ 2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro y; positivity
  have hgint : IntervalIntegrable
      (fun y : ℝ => K * (10000000 * Pa.θ * Pa.N ^ σ * (1 + (Pa.θ * y) ^ 2)⁻¹)) volume
      (-T) T :=
    ((hcontg.const_mul (10000000 * Pa.θ * Pa.N ^ σ)).const_mul K).intervalIntegrable (-T) T
  -- the dominating inequality, almost everywhere
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (-T) T →
      ‖mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)
          * Zc ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ K * (10000000 * Pa.θ * Pa.N ^ σ * (1 + (Pa.θ * t) ^ 2)⁻¹) := by
    have hne : ∀ᵐ t : ℝ, t ≠ 0 := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with t ht0 htIoc
    have htT : |t| ≤ T := by
      rw [abs_le]; exact ⟨by linarith [htIoc.1], htIoc.2⟩
    rw [norm_mul, mul_comm K]
    exact mul_le_mul (hpt t ht0) (hZc t htT) (norm_nonneg _) (by positivity)
  calc ‖∫ y in (-T)..T, mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I)
          * Zc ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ ∫ y in (-T)..T, K * (10000000 * Pa.θ * Pa.N ^ σ * (1 + (Pa.θ * y) ^ 2)⁻¹) :=
        intervalIntegral.norm_integral_le_of_norm_le hle hae hgint
    _ = K * (10000000 * Pa.θ * Pa.N ^ σ * ∫ y in (-T)..T, (1 + (Pa.θ * y) ^ 2)⁻¹) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ K * (10000000 * Pa.θ * Pa.N ^ σ * (Real.pi / Pa.θ)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact integral_one_add_mul_sq_inv_le Pa.θ (-T) T hθpos
    _ = Real.pi * (10 ^ 7 * K) * Pa.N ^ σ := by
        rw [show (10000000 : ℝ) = (10 : ℝ) ^ 7 by norm_num]
        field_simp

end Work.FIArea6Road
