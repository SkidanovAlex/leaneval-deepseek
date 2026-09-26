import Mathlib
import Submission.Work.Asymptotics.KfunClearSharp
import Submission.Work.Asymptotics.DivisorFunnelBound
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul

/-!
# The CKMRV kernel far from the three funnel points

This file proves `Work.Asymptotics.FunnelFar`: on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and for
`0 < t ≤ 1`, away from the three points `i/t`, `±1 + i/t` (the `S`- and `T`-translates of the
contour point `it` on which `j` meets `j(it)`), the CKMRV kernel `Kaxis (Kfun ℓ d) τ t` is
bounded by `C (1 + 1/t)^m exp (-(c/t))`.

The proof follows `Work.Asymptotics.KfunClearSharp`, but applies the slash bounds to the kernels
`K_±` themselves rather than to the pole-cleared kernels:

* `KPlus_slash_bound_funnel` / `KMinusFunnelSlash` bound `K_±(τ, it)` by the divisor
  `Δ(i/t)(j τ - j(i/t))` times the cusp factors `e^{-2π/t}`, `e^{-π/t}`;
* the divisor is bounded below by a constant (and by `c e^{2π(Im τ - 1/t)}` above the diagonal)
  using `E_jdiff_large` at the point `S τ ∈ E`, the lower bound `‖Δ(i/t)‖ ≥ c e^{-2π/t}`, and
  the elementary fact that `e^{2πλ} - e^{2πix}` stays away from `0` off the three disks.
-/

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## §1  Elementary estimates -/

/-- `‖1 - e^{iθ}‖^2 = 2 - 2 cos θ`. -/
lemma normSq_one_sub_exp (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [show Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I by
    rw [Complex.exp_mul_I]; simp]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `(1+y)^A e^{-σ y}` is bounded on `y ≥ 0`. -/
lemma poly_mul_exp_le (A : ℝ) (σ : ℝ) (hA : 0 ≤ A) (hσ : 0 < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ y : ℝ, 0 ≤ y → (1 + y) ^ A * Real.exp (-(σ * y)) ≤ K := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, A ≤ (n : ℝ) := ⟨⌈A⌉₊, Nat.le_ceil A⟩
  have hfactpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hσn : (0 : ℝ) < σ ^ n := pow_pos hσ n
  have hdnn : (0:ℝ) ≤ (n.factorial : ℝ) / σ ^ n := div_nonneg hfactpos.le hσn.le
  set K : ℝ := 2 ^ n * ((n.factorial : ℝ) / σ ^ n + 1) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨K, hKpos, fun y hy => ?_⟩
  have hbase : (1 + y) ^ A ≤ (1 + y) ^ n := by
    rw [← Real.rpow_natCast (1 + y) n]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hn
  have hmul : (1 + y) ^ A * Real.exp (-(σ * y)) ≤ (1 + y) ^ n * Real.exp (-(σ * y)) :=
    mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg _)
  have hkey : (1 + y) ^ n * Real.exp (-(σ * y)) ≤ K := by
    by_cases h : y ≤ 1
    · have h2 : (1 + y) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      have h3 : Real.exp (-(σ * y)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      have h4 : (1 + y) ^ n * Real.exp (-(σ * y)) ≤ 2 ^ n * 1 :=
        mul_le_mul h2 h3 (Real.exp_nonneg _) (by positivity)
      have h5 : (2:ℝ)^n * 1 ≤ K := by
        rw [hK]
        have := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ (n.factorial : ℝ) / σ ^ n + 1)
          (by positivity : (0:ℝ) ≤ 2^n)
        linarith
      linarith
    · have hy1 : 1 ≤ y := le_of_lt (not_le.mp h)
      have h2 : (1 + y) ^ n ≤ (2 * y) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      have h3 : (2 * y) ^ n = 2 ^ n * y ^ n := mul_pow 2 y n
      have h4 : y ^ n * Real.exp (-(σ * y)) ≤ (n.factorial : ℝ) / σ ^ n := by
        have h5 := Real.pow_div_factorial_le_exp (σ * y) (by positivity) n
        have h6 : (σ * y) ^ n ≤ Real.exp (σ * y) * (n.factorial : ℝ) := (div_le_iff₀ hfactpos).mp h5
        have h7 : (σ * y) ^ n * Real.exp (-(σ * y)) ≤ (n.factorial : ℝ) := by
          calc (σ * y) ^ n * Real.exp (-(σ * y))
              ≤ (Real.exp (σ * y) * (n.factorial : ℝ)) * Real.exp (-(σ * y)) :=
                mul_le_mul_of_nonneg_right h6 (Real.exp_nonneg _)
            _ = (n.factorial : ℝ) * (Real.exp (σ * y) * Real.exp (-(σ * y))) := by ring
            _ = (n.factorial : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        have h8 : (σ * y) ^ n = σ ^ n * y ^ n := mul_pow σ y n
        rw [h8] at h7
        rw [div_eq_mul_inv, le_mul_inv_iff₀ hσn, mul_comm (y ^ n * Real.exp (-(σ * y))) (σ ^ n),
          ← mul_assoc]
        exact h7
      calc (1 + y) ^ n * Real.exp (-(σ * y)) ≤ (2 * y) ^ n * Real.exp (-(σ * y)) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
        _ = 2 ^ n * (y ^ n * Real.exp (-(σ * y))) := by rw [h3]; ring
        _ ≤ 2 ^ n * ((n.factorial : ℝ) / σ ^ n) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ K := by
            rw [hK]
            have := mul_le_mul_of_nonneg_left (by linarith :
              (n.factorial : ℝ) / σ ^ n ≤ (n.factorial : ℝ) / σ ^ n + 1) (by positivity : (0:ℝ) ≤ 2^n)
            linarith
  linarith

lemma exp_neg_pi_eight_le_three_quarters : Real.exp (-(Real.pi / 8)) ≤ 3 / 4 := by
  have hlog : Real.log (4/3) ≤ Real.pi / 8 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4/3 by norm_num)
    have h2 : (3:ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have h : -(Real.pi / 8) ≤ Real.log (3/4) := by
    rw [show (3:ℝ)/4 = (4/3)⁻¹ by norm_num, Real.log_inv]
    linarith
  calc Real.exp (-(Real.pi / 8)) ≤ Real.exp (Real.log (3/4)) := Real.exp_le_exp.mpr h
    _ = 3/4 := Real.exp_log (by norm_num)

/-- In the window `|l| ≤ 1/16`, when `(x,l)` is at distance `≥ 1/4` from `0` and `1` and
`|x| < 1`, the numbers `e^{2πl}` and `e^{2πix}` are at distance `≥ 1/4`. -/
lemma ExpGeomWindow (x l : ℝ) (hx : |x| < 1) (hl : |l| ≤ 1 / 16)
    (h1 : (1 / 4 : ℝ) ^ 2 ≤ x ^ 2 + l ^ 2)
    (h2 : (1 / 4 : ℝ) ^ 2 ≤ (x - 1) ^ 2 + l ^ 2)
    (h3 : (1 / 4 : ℝ) ^ 2 ≤ (x + 1) ^ 2 + l ^ 2) :
    (1 / 4 : ℝ) ≤ ‖(Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)) -
      Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hl2 : l ^ 2 ≤ 1 / 256 := by
    have h := abs_le.mp hl
    nlinarith [h.1, h.2]
  have hxlt1 : x < 1 := (abs_lt.mp hx).2
  have hxgt1 : -1 < x := (abs_lt.mp hx).1
  have ha0 : 0 ≤ 1 / 4 - 4 * l ^ 2 := by nlinarith [hl2]
  have ha2 : (1 / 4 - 4 * l ^ 2) ^ 2 ≤ 1 / 16 - l ^ 2 := by
    have h4 : 16 * l ^ 2 * l ^ 2 ≤ l ^ 2 / 16 := by nlinarith [hl2, sq_nonneg l]
    nlinarith [h4]
  have step : ∀ z : ℝ, (1 / 4 : ℝ) ^ 2 ≤ z ^ 2 + l ^ 2 → 1 / 4 - 4 * l ^ 2 ≤ |z| := by
    intro z hz
    have hz2 : 1 / 16 - l ^ 2 ≤ z ^ 2 := by linarith [hz]
    have hkey : (1 / 4 - 4 * l ^ 2) ^ 2 ≤ z ^ 2 := le_trans ha2 hz2
    calc 1 / 4 - 4 * l ^ 2 = |1 / 4 - 4 * l ^ 2| := (abs_of_nonneg ha0).symm
      _ ≤ |z| := sq_le_sq.mp hkey
  have hxa : 1 / 4 - 4 * l ^ 2 ≤ |x| := step x h1
  have hx1 : 1 / 4 - 4 * l ^ 2 ≤ |x - 1| := step (x - 1) h2
  have hx1' : 1 / 4 - 4 * l ^ 2 ≤ |x + 1| := step (x + 1) h3
  have hxu : |x| ≤ 3 / 4 + 4 * l ^ 2 := by
    by_cases hx0 : 0 ≤ x
    · have hneg : x - 1 < 0 := by linarith
      have hval : |x - 1| = 1 - x := by rw [abs_of_neg hneg]; ring
      rw [hval] at hx1
      rw [abs_of_nonneg hx0]
      linarith
    · have hx0' : x < 0 := not_le.mp hx0
      have hpos : 0 < x + 1 := by linarith
      have hval : |x + 1| = x + 1 := abs_of_pos hpos
      rw [hval] at hx1'
      rw [abs_of_neg hx0']
      linarith
  have htheta : 0 ≤ Real.pi / 2 - 8 * Real.pi * l ^ 2 := by nlinarith [hl2, hpi]
  have hsin : Real.cos (Real.pi / 2 - 8 * Real.pi * l ^ 2) ≤ 8 * Real.pi * l ^ 2 := by
    rw [Real.cos_pi_div_two_sub]
    exact Real.sin_le (by positivity)
  have hbound : ∀ u : ℝ, 1 / 4 - 4 * l ^ 2 ≤ u → u ≤ 3 / 4 + 4 * l ^ 2 →
      Real.cos (2 * Real.pi * u) ≤ 8 * Real.pi * l ^ 2 := by
    intro u hu1 hu2
    have hlo : Real.pi / 2 - 8 * Real.pi * l ^ 2 ≤ 2 * Real.pi * u := by nlinarith [hu1, hpi]
    by_cases hp : 2 * Real.pi * u ≤ Real.pi
    · exact le_trans (Real.cos_le_cos_of_nonneg_of_le_pi htheta hp hlo) hsin
    · have hp' : Real.pi ≤ 2 * Real.pi * u := le_of_lt (not_le.mp hp)
      have hcu : Real.cos (2 * Real.pi * u) = Real.cos (2 * Real.pi - 2 * Real.pi * u) :=
        (Real.cos_two_pi_sub (2 * Real.pi * u)).symm
      have hb_hi : 2 * Real.pi - 2 * Real.pi * u ≤ Real.pi := by linarith
      have hb_lo : Real.pi / 2 - 8 * Real.pi * l ^ 2 ≤ 2 * Real.pi - 2 * Real.pi * u := by
        nlinarith [hu2, hpi]
      rw [hcu]
      exact le_trans (Real.cos_le_cos_of_nonneg_of_le_pi htheta hb_hi hb_lo) hsin
  have hcosX : Real.cos (2 * Real.pi * x) ≤ 8 * Real.pi * l ^ 2 := by
    have habs : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * |x|) := by
      rw [← Real.cos_abs (2 * Real.pi * x),
        show |2 * Real.pi * x| = 2 * Real.pi * |x| by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]]
    rw [habs]
    exact hbound |x| hxa hxu
  have hB : (5 / 4 : ℝ) ≤ ‖(1 : ℂ) - Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ := by
    have hsq := normSq_one_sub_exp (2 * Real.pi * x)
    have h16 : 16 * Real.pi * l ^ 2 ≤ 3.15 / 16 := by nlinarith [hl2, Real.pi_lt_d2]
    have h5 : (5 / 4 : ℝ) ^ 2 ≤
        ‖(1 : ℂ) - Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ ^ 2 := by
      rw [hsq]
      nlinarith [hcosX, h16]
    exact (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 5/4) (norm_nonneg _)
      (by norm_num : (2:ℕ) ≠ 0)).mp h5
  have hA : ‖(1 : ℂ) - Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)‖ ≤ 1 := by
    have hexp2 : Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ) = ((Real.exp (2 * Real.pi * l)) : ℂ) := by
      rw [Complex.ofReal_exp]
    rw [hexp2, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hl16 : l ≤ 1 / 16 := (abs_le.mp hl).2
    have hlog : 2 * Real.pi * l ≤ Real.log 2 := by
      have h1' : 2 * Real.pi * l ≤ 2 * Real.pi * (1/16) := by nlinarith [hpi, hl16]
      have h2' : 2 * Real.pi * (1/16) = Real.pi / 8 := by ring
      have h3' : Real.pi / 8 ≤ Real.log 2 := by nlinarith [Real.pi_lt_d2, Real.log_two_gt_d9]
      linarith
    have hexpLe : Real.exp (2 * Real.pi * l) ≤ 2 := by
      calc Real.exp (2 * Real.pi * l) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hlog
        _ = 2 := Real.exp_log (by norm_num)
    have hpos : 0 < Real.exp (2 * Real.pi * l) := Real.exp_pos _
    rw [abs_le]
    constructor <;> linarith
  have hsub : ‖(1:ℂ) - Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖
      - ‖(1:ℂ) - Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)‖
      ≤ ‖Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)
          - Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ := by
    have h := abs_norm_sub_norm_le ((1:ℂ) - Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I))
      ((1:ℂ) - Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ))
    have h2' : ((1:ℂ) - Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I))
        - ((1:ℂ) - Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ))
        = Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)
          - Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I) := by ring
    rw [h2'] at h
    exact (abs_le.mp h).2
  linarith

/-- Below the window: for `l ≤ -1/16` the numbers `e^{2πl}` and `e^{2πix}` are at distance
`≥ 1/4`. -/
lemma exp_sub_exp_ge_low (x l : ℝ) (hl : l ≤ -1 / 16) :
    (1 / 4 : ℝ) ≤ ‖(Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)) -
      Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hB : ‖Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hA : ‖Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)‖ ≤ 3 / 4 := by
    rw [Complex.norm_exp]
    simp only [Complex.ofReal_re]
    have h4 : 2 * Real.pi * l ≤ -(Real.pi / 8) := by nlinarith [hl, hpi]
    calc Real.exp (2 * Real.pi * l) ≤ Real.exp (-(Real.pi / 8)) := Real.exp_le_exp.mpr h4
      _ ≤ 3 / 4 := exp_neg_pi_eight_le_three_quarters
  have h := norm_sub_norm_le (Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I))
    (Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ))
  rw [norm_sub_rev] at h
  linarith [h, hA, hB]

/-- Above the window: for `l ≥ 1/16`, `‖e^{2πl} - e^{2πix}‖ ≥ (1/4) e^{2πl}`. -/
lemma exp_sub_exp_ge_high (x l : ℝ) (hl : 1 / 16 ≤ l) :
    (1 / 4 : ℝ) * Real.exp (2 * Real.pi * l) ≤ ‖(Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)) -
      Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hB : ‖Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hA : ‖Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ)‖ = Real.exp (2 * Real.pi * l) := by
    rw [Complex.norm_exp]; simp
  have h := norm_sub_norm_le (Complex.exp (((2 * Real.pi * l : ℝ)) : ℂ))
    (Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I))
  rw [hA, hB] at h
  have h2 : Real.exp (-(2 * Real.pi * l)) ≤ 3 / 4 := by
    calc Real.exp (-(2 * Real.pi * l)) ≤ Real.exp (-(Real.pi / 8)) :=
          Real.exp_le_exp.mpr (by nlinarith [hl, hpi])
      _ ≤ 3 / 4 := exp_neg_pi_eight_le_three_quarters
  have hpos : 0 < Real.exp (2 * Real.pi * l) := Real.exp_pos _
  have h3 : (1 / 4 : ℝ) * Real.exp (2 * Real.pi * l) ≤ Real.exp (2 * Real.pi * l) - 1 := by
    have hmul : Real.exp (2 * Real.pi * l) * Real.exp (-(2 * Real.pi * l)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [h2, hpos, hmul]
  linarith [h, h3]

/-- The elementary identity `e^{2πλ}(1 - e^{2πi(τ-w)}) = e^{2πλ} - e^{2πi Re τ}` for
`w = i/t` and `λ = Im τ - 1/t`. -/
lemma exp_ident (τ : ℍ) (t : ℝ) (ht : 0 < t) :
    let w : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)
    Complex.exp (((2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹ : ℝ)) : ℂ)
      - Complex.exp ((((2 * Real.pi * τ.re : ℝ)) : ℂ) * Complex.I)
      = ((Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹)) : ℂ) *
        (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (w : ℂ)))) := by
  intro w
  have hwcoe : (w : ℂ) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := rfl
  have hcoe : (τ : ℂ) - (w : ℂ) = ((τ.re : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hwcoe]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (w : ℂ))
      = (((-(2 * Real.pi * (τ.im - t⁻¹)) : ℝ)) : ℂ)
        + (((2 * Real.pi * τ.re : ℝ)) : ℂ) * Complex.I := by
    rw [hcoe]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring_nf
  have hexp1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (w : ℂ)))
      = Complex.exp ((((-(2 * Real.pi * (τ.im - t⁻¹)) : ℝ)) : ℂ))
        * Complex.exp ((((2 * Real.pi * τ.re : ℝ)) : ℂ) * Complex.I) := by
    rw [harg, Complex.exp_add]
  rw [hexp1, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  set A : ℂ := ↑(Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹)) with hA
  set B : ℂ := Complex.exp (((-(2 * Real.pi * (τ.im - t⁻¹)) : ℝ)) : ℂ) with hB
  set E : ℂ := Complex.exp ((((2 * Real.pi * τ.re : ℝ)) : ℂ) * Complex.I) with hE
  have h2 : A * B = 1 := by
    rw [hA, hB, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add,
      show (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹) + (-(2 * Real.pi * (τ.im - t⁻¹))) = 0 from by ring,
      Real.exp_zero]
    norm_num
  have key : A * (B * E) = E := by rw [← mul_assoc, h2, one_mul]
  have hgoal : A - E = A * (1 - B * E) := by
    rw [show A - E = A - A * (B * E) from by rw [key]]
    ring
  simpa [hA, hB, hE] using hgoal

/-- `‖a + b i‖^2 = a^2 + b^2` for real `a`, `b`. -/
lemma norm_sq_add_I (a b : ℝ) :
    ‖(((a : ℝ)) : ℂ) + ((b : ℝ) : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The divisor lower bound away from the three funnel points.** -/
lemma divisor_far_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), τ ∈ DomainD → 2 ≤ τ.im → t ≤ 1 →
      (1 / 4 ≤ ‖(τ : ℂ) - ((t⁻¹ : ℝ) : ℂ) * Complex.I‖) →
      (1 / 4 ≤ ‖(τ : ℂ) - ((1 : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I)‖) →
      (1 / 4 ≤ ‖(τ : ℂ) - ((-1 : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I)‖) →
      (c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun τ -
                Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖ ∧
       (t⁻¹ + 1 / 16 ≤ τ.im →
        c * Real.exp (2 * Real.pi * (τ.im - t⁻¹)) ≤
          ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
             (Work.Kernels.jInvariantFun τ -
               Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖)) := by
  obtain ⟨cJ, hcJ, hJ⟩ := E_jdiff_large
  obtain ⟨cDa, CDa, hcDa, hCDa, hDlt⟩ := SpikeCircle.DeltaFunBoundsHalf
  refine ⟨cDa * cJ / 4, by positivity, ?_⟩
  intro τ t ht hDτ h2 ht1 hd1 hd2 hd3
  have hs0 : 0 < t⁻¹ := inv_pos.mpr ht
  have hs1 : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  set w : ℍ := Work.Kernels.imagAxis t⁻¹ hs0 with hw
  have hwcoe : (w : ℂ) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := by rw [hw]; rfl
  have hwim : w.im = t⁻¹ := by rw [hw]; simp [Work.Kernels.imagAxis]
  rw [← hwcoe] at hd1 hd2 hd3
  have hE : ModularGroup.S • τ ∈ KEpsilon := by
    rw [mem_KEpsilon]
    exact ⟨S_smul_mem_DomainD hDτ, by rw [S_smul_S_smul]; exact h2⟩
  have hJapp := hJ (ModularGroup.S • τ) t⁻¹ hs0 hE hs1
  rw [S_smul_S_smul, KernelFacts.jInvariantFun_S_smul, ← hw] at hJapp
  have hDlb : cDa * Real.exp (-(2 * Real.pi * t⁻¹)) ≤ ‖Work.Kernels.DeltaFun w‖ := by
    have h := (hDlt w (by rw [hwim]; linarith)).1
    rwa [hwim] at h
  set Φ : ℝ := ‖(1 : ℂ) - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (w : ℂ)))‖ with hΦ
  set Ψ : ℝ := ‖Complex.exp (((2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹ : ℝ)) : ℂ)
      - Complex.exp ((((2 * Real.pi * τ.re : ℝ)) : ℂ) * Complex.I)‖ with hΨ
  have hrel : Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹) * Φ = Ψ := by
    rw [hΦ, hΨ]
    have hid := exp_ident τ t ht
    have hnn : (0:ℝ) < Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹) := Real.exp_pos _
    calc Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹)
          * ‖1 - Complex.exp (2 * Real.pi * Complex.I * ((τ:ℂ) - (w:ℂ)))‖
        = ‖((Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹)) : ℂ)
            * (1 - Complex.exp (2 * Real.pi * Complex.I * ((τ:ℂ) - (w:ℂ))))‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnn]
      _ = ‖Complex.exp (((2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹ : ℝ)) : ℂ)
            - Complex.exp ((((2 * Real.pi * τ.re : ℝ)) : ℂ) * Complex.I)‖ := by
          rw [← hid]
  have hDmain : cDa * cJ * Ψ ≤ ‖Work.Kernels.DeltaFun w *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)‖ := by
    have hexpadd : Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹)
        = Real.exp (-(2 * Real.pi * t⁻¹)) * Real.exp (2 * Real.pi * τ.im) := by
      rw [← Real.exp_add]; congr 1; ring
    have hstep : cDa * cJ * Ψ = (cDa * Real.exp (-(2 * Real.pi * t⁻¹)))
        * (cJ * Real.exp (2 * Real.pi * τ.im) * Φ) := by
      rw [← hrel, hexpadd]; ring
    rw [hstep, norm_mul]
    exact mul_le_mul hDlb hJapp (by positivity) (norm_nonneg _)
  constructor
  · -- the constant lower bound
    have hcase : (1 / 4 : ℝ) ≤ Ψ := by
      by_cases hA : τ.im ≤ t⁻¹ + 1 / 16
      · by_cases hA1 : τ.im ≤ t⁻¹ - 1 / 16
        · have hlow := exp_sub_exp_ge_low τ.re (τ.im - t⁻¹) (by linarith)
          have heq : (((2 * Real.pi * (τ.im - t⁻¹) : ℝ)) : ℂ)
              = ((2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹ : ℝ) : ℂ) := by push_cast; ring
          rw [heq] at hlow
          simpa [hΨ] using hlow
        · have hA2' : τ.im - t⁻¹ ≤ 1 / 16 := by linarith
          have hx1 : |τ.re| < 1 := by
            have h := mem_DomainD.mp hDτ
            rw [abs_lt]; exact ⟨h.1, h.2.1⟩
          have hz1 : (τ : ℂ) - (w : ℂ)
              = ((τ.re : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I) := by
            apply Complex.ext <;>
            simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
              UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hwcoe]
          have hz2 : (τ : ℂ) - (1 + (w : ℂ))
              = (((τ.re - 1 : ℝ)) : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I := by
            apply Complex.ext <;>
            simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
              UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hwcoe]
          have hz3 : (τ : ℂ) - ((-1 : ℂ) + (w : ℂ))
              = (((τ.re + 1 : ℝ)) : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I := by
            apply Complex.ext <;>
            simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
              UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hwcoe]
          have hd1' : (1 / 4 : ℝ) ^ 2 ≤ τ.re ^ 2 + (τ.im - t⁻¹) ^ 2 := by
            have h := hd1
            rw [hz1] at h
            have h2 := norm_sq_add_I τ.re (τ.im - t⁻¹)
            have hnn : (0:ℝ) ≤ ‖(((τ.re : ℝ)) : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I‖ :=
              norm_nonneg _
            nlinarith [h, hnn, h2]
          have hd2' : (1 / 4 : ℝ) ^ 2 ≤ (τ.re - 1) ^ 2 + (τ.im - t⁻¹) ^ 2 := by
            have h := hd2
            rw [hz2] at h
            have h2 := norm_sq_add_I (τ.re - 1) (τ.im - t⁻¹)
            have hnn : (0:ℝ) ≤ ‖(((τ.re - 1 : ℝ)) : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I‖ :=
              norm_nonneg _
            nlinarith [h, hnn, h2]
          have hd3' : (1 / 4 : ℝ) ^ 2 ≤ (τ.re + 1) ^ 2 + (τ.im - t⁻¹) ^ 2 := by
            have h := hd3
            rw [hz3] at h
            have h2 := norm_sq_add_I (τ.re + 1) (τ.im - t⁻¹)
            have hnn : (0:ℝ) ≤ ‖(((τ.re + 1 : ℝ)) : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I‖ :=
              norm_nonneg _
            nlinarith [h, hnn, h2]
          have hA1'' : -(1 / 16 : ℝ) ≤ τ.im - t⁻¹ := by linarith [not_le.mp hA1]
          have hwin := ExpGeomWindow τ.re (τ.im - t⁻¹) hx1 (abs_le.mpr ⟨hA1'', hA2'⟩) hd1' hd2' hd3'
          have heq : (((2 * Real.pi * (τ.im - t⁻¹) : ℝ)) : ℂ)
              = ((2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹ : ℝ) : ℂ) := by push_cast; ring
          rw [heq] at hwin
          simpa [hΨ] using hwin
      · -- above the diagonal (but within `t⁻¹ + 1/16`)
        have hl0 : 0 ≤ τ.im - t⁻¹ := by linarith [not_le.mp hA]
        have hhigh := exp_sub_exp_ge_high τ.re (τ.im - t⁻¹) (by linarith)
        have hgoal : (1 / 4 : ℝ) ≤ Ψ := by
          have hceq : (((2 * Real.pi * (τ.im - t⁻¹) : ℝ)) : ℂ)
              = ((2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹ : ℝ) : ℂ) := by push_cast; ring
          rw [hceq] at hhigh
          have hone : (1:ℝ) ≤ Real.exp (2 * Real.pi * (τ.im - t⁻¹)) :=
            Real.one_le_exp_iff.mpr (by nlinarith [Real.pi_pos, hl0])
          rw [hΨ]
          nlinarith [hhigh, hone]
        exact hgoal
    have h1 : cDa * cJ / 4 ≤ cDa * cJ * Ψ := by
      have hpos : 0 < cDa * cJ / 4 := by positivity
      nlinarith [hcase, hpos, hcJ, hcDa]
    linarith
  · intro hB
    have hhigh := exp_sub_exp_ge_high τ.re (τ.im - t⁻¹) (by linarith)
    have hceq : (((2 * Real.pi * (τ.im - t⁻¹) : ℝ)) : ℂ)
        = ((2 * Real.pi * τ.im - 2 * Real.pi * t⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hceq] at hhigh
    have hPsinv : 0 < cDa * cJ / 4 := by positivity
    have hex : 0 < Real.exp (2 * Real.pi * (τ.im - t⁻¹)) := Real.exp_pos _
    have hΨlb : (1 / 4 : ℝ) * Real.exp (2 * Real.pi * (τ.im - t⁻¹)) ≤ Ψ := by
      rw [hΨ]; exact hhigh
    nlinarith [hDmain, hΨlb, hPsinv, hcJ, hcDa, hex]

/-! ## §1b  The arithmetic of the two regimes -/

/-- Case `Im τ ≤ 1/t + 1/16`: the `K_+` bound. -/
lemma boundA_plus (Cp Ap cDv D w s : ℝ) (hCp : 0 < Cp) (hAp : 0 ≤ Ap) (hcDv : 0 < cDv)
    (hDpos : 0 < D) (hDge : cDv ≤ D) (htau : 1 + w ≤ 4 * (1 + s)) (hs : 0 ≤ s) (hw : 0 ≤ w) :
    Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) / D
      ≤ (Cp * 4 ^ Ap / cDv) * (1 + s) ^ Ap * Real.exp (-(Real.pi / 2 * s)) := by
  have hNp : 0 ≤ Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) :=
    mul_nonneg (mul_nonneg hCp.le (Real.rpow_nonneg (by linarith) Ap)) (Real.exp_nonneg _)
  have hinv : D⁻¹ ≤ cDv⁻¹ := (inv_le_inv₀ hDpos hcDv).mpr hDge
  have hstep1 : Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) / D
      ≤ Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) / cDv := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hNp
  have hexp_le : Real.exp (-(2 * Real.pi * s)) ≤ Real.exp (-(Real.pi / 2 * s)) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hs]
  have hpow : (1 + w) ^ Ap ≤ 4 ^ Ap * (1 + s) ^ Ap := by
    calc (1 + w) ^ Ap ≤ (4 * (1 + s)) ^ Ap := Real.rpow_le_rpow (by linarith) htau hAp
      _ = 4 ^ Ap * (1 + s) ^ Ap := Real.mul_rpow (by norm_num) (by linarith)
  have hstep2 : Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) / cDv
      ≤ (Cp * 4 ^ Ap / cDv) * (1 + s) ^ Ap * Real.exp (-(Real.pi / 2 * s)) := by
    calc Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) / cDv
        = (Cp / cDv) * ((1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s))) := by ring
      _ ≤ (Cp / cDv) * ((4 ^ Ap * (1 + s) ^ Ap) * Real.exp (-(Real.pi / 2 * s))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hpow hexp_le (Real.exp_nonneg _) (by positivity)
      _ = (Cp * 4 ^ Ap / cDv) * (1 + s) ^ Ap * Real.exp (-(Real.pi / 2 * s)) := by ring
  linarith [hstep1, hstep2]

/-- Case `Im τ ≤ 1/t + 1/16`: the `K_-` bound. -/
lemma boundA_minus (Cm Am cDv D w s : ℝ) (hCm : 0 < Cm) (hAm : 0 ≤ Am) (hcDv : 0 < cDv)
    (hDpos : 0 < D) (hDge : cDv ≤ D) (htau : 1 + w ≤ 4 * (1 + s)) (hs : 0 ≤ s) (hw : 0 ≤ w) :
    Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) / D
      ≤ (Cm * 4 ^ Am / cDv) * (1 + s) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * s)) := by
  have h1s : (0:ℝ) < 1 + s := by linarith
  have hNp : 0 ≤ Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (by linarith) Am))
      (by positivity)) (Real.exp_nonneg _)
  have hinv : D⁻¹ ≤ cDv⁻¹ := (inv_le_inv₀ hDpos hcDv).mpr hDge
  have hstep1 : Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) / D
      ≤ Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) / cDv := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hNp
  have hexp_le : Real.exp (-(Real.pi * s)) ≤ Real.exp (-(Real.pi / 2 * s)) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hs]
  have hpow : (1 + w) ^ Am ≤ 4 ^ Am * (1 + s) ^ Am := by
    calc (1 + w) ^ Am ≤ (4 * (1 + s)) ^ Am := Real.rpow_le_rpow (by linarith) htau hAm
      _ = 4 ^ Am * (1 + s) ^ Am := Real.mul_rpow (by norm_num) (by linarith)
  have hpow2 : (1 + s) ^ Am * (1 + s) ^ ((2:ℕ):ℝ) = (1 + s) ^ (Am + 2) := by
    rw [← Real.rpow_add h1s]; norm_num
  have hstep2 : Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) / cDv
      ≤ (Cm * 4 ^ Am / cDv) * (1 + s) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * s)) := by
    have h3 : (1 + w) ^ Am * Real.exp (-(Real.pi * s))
        ≤ (4 ^ Am * (1 + s) ^ Am) * Real.exp (-(Real.pi / 2 * s)) :=
      mul_le_mul hpow hexp_le (Real.exp_nonneg _) (by positivity)
    calc Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) / cDv
        = (Cm / cDv) * ((1 + s) ^ 2 * ((1 + w) ^ Am * Real.exp (-(Real.pi * s)))) := by ring
      _ ≤ (Cm / cDv) * ((1 + s) ^ 2 * ((4 ^ Am * (1 + s) ^ Am)
            * Real.exp (-(Real.pi / 2 * s)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (Cm / cDv) * 4 ^ Am * ((1 + s) ^ Am * (1 + s) ^ ((2:ℕ):ℝ))
            * Real.exp (-(Real.pi / 2 * s)) := by
          rw [(Real.rpow_natCast (1 + s) 2).symm]; ring
      _ = (Cm * 4 ^ Am / cDv) * (1 + s) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * s)) := by
          rw [hpow2]; ring
  linarith [hstep1, hstep2]

/-- Case `1/t + 1/16 ≤ Im τ`: the `K_+` bound, with `δ = Im τ - 1/t`. -/
lemma boundB_plus (Cp Ap cDv D w s δ Lp : ℝ) (hCp : 0 < Cp) (hAp : 0 ≤ Ap) (hcDv : 0 < cDv)
    (hDpos : 0 < D) (hDge : cDv * Real.exp (2 * Real.pi * δ) ≤ D)
    (htau : 1 + w ≤ (s + 2) * (1 + δ)) (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hs : 1 ≤ s)
    (hLp : (1 + δ) ^ Ap * Real.exp (-(2 * Real.pi * δ)) ≤ Lp) (hLp0 : 0 ≤ Lp) :
    Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) / D
      ≤ (Cp * Lp * 3 ^ Ap / cDv) * (1 + s) ^ Ap * Real.exp (-(Real.pi / 2 * s)) := by
  have hexpδ : 0 < Real.exp (2 * Real.pi * δ) := Real.exp_pos _
  have hDpos2 : 0 < cDv * Real.exp (2 * Real.pi * δ) := mul_pos hcDv hexpδ
  have hNp : 0 ≤ Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) :=
    mul_nonneg (mul_nonneg hCp.le (Real.rpow_nonneg (by linarith) Ap)) (Real.exp_nonneg _)
  have hinv : D⁻¹ ≤ (cDv * Real.exp (2 * Real.pi * δ))⁻¹ := (inv_le_inv₀ hDpos hDpos2).mpr hDge
  have hstep1 : Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s)) / D
      ≤ Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s))
          / (cDv * Real.exp (2 * Real.pi * δ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hNp
  have h1 : (1 + w) ^ Ap ≤ (s + 2) ^ Ap * (1 + δ) ^ Ap := by
    calc (1 + w) ^ Ap ≤ ((s + 2) * (1 + δ)) ^ Ap := Real.rpow_le_rpow (by linarith) htau hAp
      _ = (s + 2) ^ Ap * (1 + δ) ^ Ap := Real.mul_rpow (by linarith) (by linarith)
  have h2 : (s + 2) ^ Ap ≤ 3 ^ Ap * (1 + s) ^ Ap := by
    have hh : s + 2 ≤ 3 * (1 + s) := by linarith
    calc (s + 2) ^ Ap ≤ (3 * (1 + s)) ^ Ap := Real.rpow_le_rpow (by linarith) hh hAp
      _ = 3 ^ Ap * (1 + s) ^ Ap := Real.mul_rpow (by norm_num) (by linarith)
  have h8 : (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * δ)) ≤ 3 ^ Ap * (1 + s) ^ Ap * Lp := by
    calc (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * δ))
        ≤ ((s + 2) ^ Ap * (1 + δ) ^ Ap) * Real.exp (-(2 * Real.pi * δ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = (s + 2) ^ Ap * ((1 + δ) ^ Ap * Real.exp (-(2 * Real.pi * δ))) := by ring
      _ ≤ (s + 2) ^ Ap * Lp := mul_le_mul_of_nonneg_left hLp (Real.rpow_nonneg (by linarith) Ap)
      _ ≤ (3 ^ Ap * (1 + s) ^ Ap) * Lp := mul_le_mul_of_nonneg_right h2 hLp0
  have h9 : Real.exp (-(2 * Real.pi * s)) ≤ Real.exp (-(Real.pi / 2 * s)) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hs]
  have h10 : ((1 + w) ^ Ap * Real.exp (-(2 * Real.pi * δ))) * Real.exp (-(2 * Real.pi * s))
      ≤ (3 ^ Ap * (1 + s) ^ Ap * Lp) * Real.exp (-(Real.pi / 2 * s)) :=
    mul_le_mul h8 h9 (Real.exp_nonneg _) (by positivity)
  have hstep2 : Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s))
        / (cDv * Real.exp (2 * Real.pi * δ))
      ≤ (Cp * Lp * 3 ^ Ap / cDv) * (1 + s) ^ Ap * Real.exp (-(Real.pi / 2 * s)) := by
    have hsplit : Cp * (1 + w) ^ Ap * Real.exp (-(2 * Real.pi * s))
          / (cDv * Real.exp (2 * Real.pi * δ))
        = (Cp / cDv) * (((1 + w) ^ Ap * Real.exp (-(2 * Real.pi * δ)))
            * Real.exp (-(2 * Real.pi * s))) := by
      rw [div_eq_mul_inv, mul_inv, (Real.exp_neg (2 * Real.pi * δ)).symm]; ring
    rw [hsplit]
    calc (Cp / cDv) * (((1 + w) ^ Ap * Real.exp (-(2 * Real.pi * δ)))
            * Real.exp (-(2 * Real.pi * s)))
        ≤ (Cp / cDv) * ((3 ^ Ap * (1 + s) ^ Ap * Lp) * Real.exp (-(Real.pi / 2 * s))) :=
          mul_le_mul_of_nonneg_left h10 (by positivity)
      _ = (Cp * Lp * 3 ^ Ap / cDv) * (1 + s) ^ Ap * Real.exp (-(Real.pi / 2 * s)) := by ring
  linarith [hstep1, hstep2]

/-- Case `1/t + 1/16 ≤ Im τ`: the `K_-` bound, with `δ = Im τ - 1/t`. -/
lemma boundB_minus (Cm Am cDv D w s δ Lm : ℝ) (hCm : 0 < Cm) (hAm : 0 ≤ Am) (hcDv : 0 < cDv)
    (hDpos : 0 < D) (hDge : cDv * Real.exp (2 * Real.pi * δ) ≤ D)
    (htau : 1 + w ≤ (s + 2) * (1 + δ)) (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hs : 1 ≤ s)
    (hLm : (1 + δ) ^ Am * Real.exp (-(2 * Real.pi * δ)) ≤ Lm) (hLm0 : 0 ≤ Lm) :
    Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) / D
      ≤ (Cm * Lm * 3 ^ Am / cDv) * (1 + s) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * s)) := by
  have h1s : (0:ℝ) < 1 + s := by linarith
  have hexpδ : 0 < Real.exp (2 * Real.pi * δ) := Real.exp_pos _
  have hDpos2 : 0 < cDv * Real.exp (2 * Real.pi * δ) := mul_pos hcDv hexpδ
  have hNp : 0 ≤ Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (by linarith) Am))
      (by positivity)) (Real.exp_nonneg _)
  have hinv : D⁻¹ ≤ (cDv * Real.exp (2 * Real.pi * δ))⁻¹ := (inv_le_inv₀ hDpos hDpos2).mpr hDge
  have hstep1 : Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s)) / D
      ≤ Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s))
          / (cDv * Real.exp (2 * Real.pi * δ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hNp
  have h1 : (1 + w) ^ Am ≤ (s + 2) ^ Am * (1 + δ) ^ Am := by
    calc (1 + w) ^ Am ≤ ((s + 2) * (1 + δ)) ^ Am := Real.rpow_le_rpow (by linarith) htau hAm
      _ = (s + 2) ^ Am * (1 + δ) ^ Am := Real.mul_rpow (by linarith) (by linarith)
  have h2 : (s + 2) ^ Am ≤ 3 ^ Am * (1 + s) ^ Am := by
    have hh : s + 2 ≤ 3 * (1 + s) := by linarith
    calc (s + 2) ^ Am ≤ (3 * (1 + s)) ^ Am := Real.rpow_le_rpow (by linarith) hh hAm
      _ = 3 ^ Am * (1 + s) ^ Am := Real.mul_rpow (by norm_num) (by linarith)
  have h8 : (1 + w) ^ Am * Real.exp (-(2 * Real.pi * δ)) ≤ 3 ^ Am * (1 + s) ^ Am * Lm := by
    calc (1 + w) ^ Am * Real.exp (-(2 * Real.pi * δ))
        ≤ ((s + 2) ^ Am * (1 + δ) ^ Am) * Real.exp (-(2 * Real.pi * δ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = (s + 2) ^ Am * ((1 + δ) ^ Am * Real.exp (-(2 * Real.pi * δ))) := by ring
      _ ≤ (s + 2) ^ Am * Lm := mul_le_mul_of_nonneg_left hLm (Real.rpow_nonneg (by linarith) Am)
      _ ≤ (3 ^ Am * (1 + s) ^ Am) * Lm := mul_le_mul_of_nonneg_right h2 hLm0
  have h9 : ((1 + s) ^ ((2:ℕ):ℝ)) * Real.exp (-(Real.pi * s))
      ≤ ((1 + s) ^ ((2:ℕ):ℝ)) * Real.exp (-(Real.pi / 2 * s)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) 2)
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hs]
  have hpows : (1 + s) ^ Am * (1 + s) ^ ((2:ℕ):ℝ) = (1 + s) ^ (Am + 2) := by
    rw [← Real.rpow_add h1s]; norm_num
  have h10 : ((1 + w) ^ Am * Real.exp (-(2 * Real.pi * δ)))
        * ((1 + s) ^ ((2:ℕ):ℝ) * Real.exp (-(Real.pi * s)))
      ≤ (3 ^ Am * (1 + s) ^ Am * Lm)
        * ((1 + s) ^ ((2:ℕ):ℝ) * Real.exp (-(Real.pi / 2 * s))) :=
    mul_le_mul h8 h9 (by positivity) (by positivity)
  have hstep2 : Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s))
        / (cDv * Real.exp (2 * Real.pi * δ))
      ≤ (Cm * Lm * 3 ^ Am / cDv) * (1 + s) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * s)) := by
    have hsplit : Cm * (1 + w) ^ Am * (1 + s) ^ 2 * Real.exp (-(Real.pi * s))
          / (cDv * Real.exp (2 * Real.pi * δ))
        = (Cm / cDv) * (1 + s) ^ 2
            * (((1 + w) ^ Am * Real.exp (-(2 * Real.pi * δ))) * Real.exp (-(Real.pi * s))) := by
      rw [div_eq_mul_inv, mul_inv, (Real.exp_neg (2 * Real.pi * δ)).symm]; ring
    rw [hsplit]
    calc (Cm / cDv) * (1 + s) ^ 2
          * (((1 + w) ^ Am * Real.exp (-(2 * Real.pi * δ))) * Real.exp (-(Real.pi * s)))
        = (Cm / cDv) * (((1 + w) ^ Am * Real.exp (-(2 * Real.pi * δ)))
            * ((1 + s) ^ ((2:ℕ):ℝ) * Real.exp (-(Real.pi * s)))) := by
          rw [(Real.rpow_natCast (1 + s) 2).symm]; ring
      _ ≤ (Cm / cDv) * ((3 ^ Am * (1 + s) ^ Am * Lm)
            * ((1 + s) ^ ((2:ℕ):ℝ) * Real.exp (-(Real.pi / 2 * s)))) :=
          mul_le_mul_of_nonneg_left h10 (by positivity)
      _ = (Cm * Lm * 3 ^ Am / cDv) * (1 + s) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * s)) := by
          rw [show (3 ^ Am * (1 + s) ^ Am * Lm)
                * ((1 + s) ^ ((2:ℕ):ℝ) * Real.exp (-(Real.pi / 2 * s)))
              = (3 ^ Am * Lm) * ((1 + s) ^ Am * (1 + s) ^ ((2:ℕ):ℝ))
                * Real.exp (-(Real.pi / 2 * s)) from by ring, hpows]
          ring
  linarith [hstep1, hstep2]

/-- Combination of the two half-bounds. -/
lemma combine_bounds (P N A B QE C : ℝ) (hP : P ≤ A * QE) (hN : N ≤ B * QE)
    (hQE : 0 ≤ QE) (hAB : (A + B) / 2 ≤ C) : (P + N) / 2 ≤ C * QE := by
  have h : (P + N) / 2 ≤ ((A + B) / 2) * QE := by nlinarith [hP, hN]
  linarith [h, mul_le_mul_of_nonneg_right hAB hQE]

/-! ## §2  The main theorem -/

theorem FunnelFar (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C c m : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ m ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        t ≤ 1 →
        (1 / 4 ≤ ‖(τ : ℂ) - ((t⁻¹ : ℝ) : ℂ) * Complex.I‖ ∧
         1 / 4 ≤ ‖(τ : ℂ) - ((1 : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I)‖ ∧
         1 / 4 ≤ ‖(τ : ℂ) - ((-1 : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I)‖) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ C * (1 + 1 / t) ^ m * Real.exp (-(c / t)) := by
  obtain ⟨Cp, Ap, hCp, hAp, hPfun⟩ := KPlus_slash_bound_funnel d hd
  obtain ⟨Cm, Am, hCm, hAm, hMfun⟩ := KMinusFunnelSlash ℓ d hd
  obtain ⟨cDv, hcDv, hDlem⟩ := divisor_far_bound
  obtain ⟨Lp, hLp0, hLpb⟩ := poly_mul_exp_le Ap (2 * Real.pi) hAp (by positivity)
  obtain ⟨Lm, hLm0, hLmb⟩ := poly_mul_exp_le Am (2 * Real.pi) hAm (by positivity)
  refine ⟨max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am) / (2 * cDv)) 1 + 1,
    Real.pi / 2, max Ap (Am + 2), ?_, by positivity, le_trans hAp (le_max_left _ _), ?_⟩
  · positivity
  · intro τ t ht hDτ h2 ht1 hdist hne
    obtain ⟨hd1, hd2, hd3⟩ := hdist
    have hs0 : 0 < t⁻¹ := inv_pos.mpr ht
    have hs1 : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
    set w : ℍ := Work.Kernels.imagAxis t⁻¹ hs0 with hw
    have hwcoe : (w : ℂ) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := by rw [hw]; rfl
    have hwim : w.im = t⁻¹ := by rw [hw]; simp [Work.Kernels.imagAxis]
    have hwn : ‖(w : ℂ)‖ = t⁻¹ := by
      rw [hwcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs0]
    have hSw : ModularGroup.S • w = Work.Kernels.imagAxis t ht := by
      rw [hw]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.modular_S_smul]
      show (-(((t⁻¹ : ℝ) : ℂ) * Complex.I))⁻¹ = ((t : ℝ) : ℂ) * Complex.I
      rw [inv_neg, mul_inv, Complex.inv_I]
      push_cast
      field_simp
    have hjw : Work.Kernels.jInvariantFun w
        = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      rw [← hSw, KernelFacts.jInvariantFun_S_smul]
    have hne' : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun w := by
      rw [hjw]; exact hne
    have hw13 : 1 / 3 ≤ w.im := by rw [hwim]; linarith
    obtain ⟨hDvA, hDvB⟩ := hDlem τ t ht hDτ h2 ht1 hd1 hd2 hd3
    set D : ℝ := ‖Work.Kernels.DeltaFun w *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)‖ with hDdef
    -- the two slash bounds
    have hP := hPfun τ w hDτ h2 hw13 hne'
    have hM := hMfun τ w hDτ h2 hw13 hne'
    have hKplus : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ ≤
        Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(2 * Real.pi * t⁻¹)) / D := by
      have hq : ‖Work.Kernels.qParamFun w‖ = Real.exp (-(2 * Real.pi * t⁻¹)) := by
        rw [norm_qParamFun, hwim]
      have h1 : ‖(w : ℂ) ^ ((d : ℤ) / 2 - 2)
            * Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ ≤
          Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(2 * Real.pi * t⁻¹)) / D := by
        have := hP
        rw [hSw, hq] at this
        exact this
      have hk : 1 ≤ (t⁻¹) ^ ((d : ℤ) / 2 - 2) := by
        apply one_le_zpow₀ hs1
        rcases hd with rfl | rfl <;> norm_num
      have h2' : ‖(w : ℂ) ^ ((d : ℤ) / 2 - 2)‖ = (t⁻¹) ^ ((d : ℤ) / 2 - 2) := by
        rw [norm_zpow, hwn]
      calc ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖
          ≤ (t⁻¹) ^ ((d : ℤ) / 2 - 2)
              * ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ := by
            nlinarith [hk, norm_nonneg (Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht))]
        _ = ‖(w : ℂ) ^ ((d : ℤ) / 2 - 2)
              * Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ := by
            rw [norm_mul, h2']
        _ ≤ _ := h1
    have hKminus : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤
        Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)) / D := by
      have h1 : ‖(w : ℂ) ^ ((d : ℤ) / 2 - 2)
            * Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤
          Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t⁻¹) ^ 2
            * Real.exp (-(Real.pi * t⁻¹)) / D := by
        have := hM
        rw [hSw, hwn, hwim] at this
        exact this
      have hk : 1 ≤ (t⁻¹) ^ ((d : ℤ) / 2 - 2) := by
        apply one_le_zpow₀ hs1
        rcases hd with rfl | rfl <;> norm_num
      have h2' : ‖(w : ℂ) ^ ((d : ℤ) / 2 - 2)‖ = (t⁻¹) ^ ((d : ℤ) / 2 - 2) := by
        rw [norm_zpow, hwn]
      calc ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
          ≤ (t⁻¹) ^ ((d : ℤ) / 2 - 2)
              * ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ := by
            nlinarith [hk, norm_nonneg (Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht))]
        _ = ‖(w : ℂ) ^ ((d : ℤ) / 2 - 2)
              * Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ := by
            rw [norm_mul, h2']
        _ ≤ _ := h1
    -- the elementary helpers on the two regimes
    have hnormτ : ‖(τ : ℂ)‖ ≤ τ.im + 1 := by
      have hre : -1 < τ.re ∧ τ.re < 1 := by
        have h := mem_DomainD.mp hDτ
        exact ⟨h.1, h.2.1⟩
      have hsq : ‖(τ : ℂ)‖ ^ 2 ≤ (τ.im + 1) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        nlinarith [hre.1, hre.2, sq_nonneg τ.re, sq_nonneg (τ.im + 1), τ.im_pos]
      nlinarith [norm_nonneg (τ : ℂ), hsq]
    have hDpos : 0 < D := by
      rw [hDdef]
      exact norm_pos_iff.mpr (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero w) (sub_ne_zero.mpr hne'))
    have htri : ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖
        ≤ (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖
            + ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖) / 2 := by
      rw [Work.Kernels.Kfun, norm_div]
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2n]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    set M : ℝ := max Ap (Am + 2) with hMdef
    set QE : ℝ := (1 + t⁻¹) ^ M * Real.exp (-(Real.pi / 2 * t⁻¹)) with hQEdef
    have hQEpos : 0 ≤ QE := by rw [hQEdef]; positivity
    have hApow : (1 + t⁻¹) ^ Ap ≤ (1 + t⁻¹) ^ M :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have hMpow : (1 + t⁻¹) ^ (Am + 2) ≤ (1 + t⁻¹) ^ M :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
    have hstepM : ∀ (C B : ℝ), 0 ≤ C → B * QE ≤ C * QE → B * QE ≤ C * QE := fun _ _ _ h => h
    have hCfin : ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
        / (2 * cDv)) ≤ max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
        / (2 * cDv)) 1 := le_max_left _ _
    have hCA : (Cp * 4 ^ Ap / cDv + Cm * 4 ^ Am / cDv) / 2
        ≤ max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
          / (2 * cDv)) 1 + 1 := by
      have heq : (Cp * 4 ^ Ap / cDv + Cm * 4 ^ Am / cDv) / 2
          = (Cp * 4 ^ Ap + Cm * 4 ^ Am) / (2 * cDv) := by ring
      rw [heq]
      have hnum : Cp * 4 ^ Ap + Cm * 4 ^ Am
          ≤ Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am := by
        have h2 : 0 ≤ Cp * Lp * 3 ^ Ap := by positivity
        have h3 : 0 ≤ Cm * Lm * 3 ^ Am := by positivity
        linarith
      have h1 := div_le_div_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ 2 * cDv)
      have h2' : max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
      / (2 * cDv)) 1 ≤ max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
      / (2 * cDv)) 1 + 1 := by linarith
      linarith [h1, h2']
    have hCB : (Cp * Lp * 3 ^ Ap / cDv + Cm * Lm * 3 ^ Am / cDv) / 2
        ≤ max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
          / (2 * cDv)) 1 + 1 := by
      have heq : (Cp * Lp * 3 ^ Ap / cDv + Cm * Lm * 3 ^ Am / cDv) / 2
          = (Cp * Lp * 3 ^ Ap + Cm * Lm * 3 ^ Am) / (2 * cDv) := by ring
      rw [heq]
      have hnum : Cp * Lp * 3 ^ Ap + Cm * Lm * 3 ^ Am
          ≤ Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am := by
        have h2 : 0 ≤ Cp * 4 ^ Ap := by positivity
        have h3 : 0 ≤ Cm * 4 ^ Am := by positivity
        linarith
      have h1 := div_le_div_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ 2 * cDv)
      have h2' : max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
      / (2 * cDv)) 1 ≤ max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
      / (2 * cDv)) 1 + 1 := by linarith
      linarith [h1, h2']
    have hfinal : ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖
        ≤ (max ((Cp * 4 ^ Ap + Cp * Lp * 3 ^ Ap + Cm * 4 ^ Am + Cm * Lm * 3 ^ Am)
              / (2 * cDv)) 1 + 1) * QE := by
      by_cases hcase : τ.im ≤ t⁻¹ + 1 / 16
      · have htau : 1 + ‖(τ : ℂ)‖ ≤ 4 * (1 + t⁻¹) := by linarith [hnormτ, hcase, hs1]
        have hP1 := boundA_plus Cp Ap cDv D ‖(τ : ℂ)‖ (t⁻¹) hCp hAp hcDv hDpos hDvA htau hs0.le
          (norm_nonneg _)
        have hM1 := boundA_minus Cm Am cDv D ‖(τ : ℂ)‖ (t⁻¹) hCm hAm hcDv hDpos hDvA htau hs0.le
          (norm_nonneg _)
        have hPfin : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖
            ≤ (Cp * 4 ^ Ap / cDv) * QE := by
          refine le_trans (le_trans hKplus hP1) ?_
          rw [hQEdef]
          calc (Cp * 4 ^ Ap / cDv) * (1 + t⁻¹) ^ Ap * Real.exp (-(Real.pi / 2 * t⁻¹))
              = (Cp * 4 ^ Ap / cDv) * ((1 + t⁻¹) ^ Ap * Real.exp (-(Real.pi / 2 * t⁻¹))) := by ring
            _ ≤ (Cp * 4 ^ Ap / cDv)
                * ((1 + t⁻¹) ^ M * Real.exp (-(Real.pi / 2 * t⁻¹))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_right hApow (Real.exp_nonneg _)
        have hMfin : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
            ≤ (Cm * 4 ^ Am / cDv) * QE := by
          refine le_trans (le_trans hKminus hM1) ?_
          rw [hQEdef]
          calc (Cm * 4 ^ Am / cDv) * (1 + t⁻¹) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * t⁻¹))
              = (Cm * 4 ^ Am / cDv)
                * ((1 + t⁻¹) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * t⁻¹))) := by ring
            _ ≤ (Cm * 4 ^ Am / cDv)
                * ((1 + t⁻¹) ^ M * Real.exp (-(Real.pi / 2 * t⁻¹))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_right hMpow (Real.exp_nonneg _)
        exact le_trans htri (combine_bounds _ _ _ _ QE _ hPfin hMfin hQEpos hCA)
      · have hge : t⁻¹ + 1 / 16 ≤ τ.im := le_of_lt (not_le.mp hcase)
        have hδ : 0 ≤ τ.im - t⁻¹ := by linarith
        have hδpos : 1 / 16 ≤ τ.im - t⁻¹ := by linarith
        have htau : 1 + ‖(τ : ℂ)‖ ≤ (t⁻¹ + 2) * (1 + (τ.im - t⁻¹)) := by
          have h1 : 1 + ‖(τ : ℂ)‖ ≤ τ.im + 2 := by linarith [hnormτ]
          have h2 : τ.im + 2 = (t⁻¹ + 2) + (τ.im - t⁻¹) := by ring
          have h3 : (t⁻¹ + 2) + (τ.im - t⁻¹) ≤ (t⁻¹ + 2) * (1 + (τ.im - t⁻¹)) := by
            nlinarith [hs0.le, hδ]
          linarith [h1, le_of_eq h2, h3]
        have hDgeB : cDv * Real.exp (2 * Real.pi * (τ.im - t⁻¹)) ≤ D := by
          have := hDvB hge
          rwa [hDdef] at this
        have hLpB : (1 + (τ.im - t⁻¹)) ^ Ap * Real.exp (-(2 * Real.pi * (τ.im - t⁻¹))) ≤ Lp :=
          hLpb (τ.im - t⁻¹) hδ
        have hLmB : (1 + (τ.im - t⁻¹)) ^ Am * Real.exp (-(2 * Real.pi * (τ.im - t⁻¹))) ≤ Lm :=
          hLmb (τ.im - t⁻¹) hδ
        have hP1 := boundB_plus Cp Ap cDv D ‖(τ : ℂ)‖ (t⁻¹) (τ.im - t⁻¹) Lp hCp hAp hcDv hDpos
          hDgeB htau hδ (norm_nonneg _) hs1 hLpB hLp0.le
        have hM1 := boundB_minus Cm Am cDv D ‖(τ : ℂ)‖ (t⁻¹) (τ.im - t⁻¹) Lm hCm hAm hcDv hDpos
          hDgeB htau hδ (norm_nonneg _) hs1 hLmB hLm0.le
        have hPfin : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖
            ≤ (Cp * Lp * 3 ^ Ap / cDv) * QE := by
          refine le_trans (le_trans hKplus hP1) ?_
          rw [hQEdef]
          calc (Cp * Lp * 3 ^ Ap / cDv) * (1 + t⁻¹) ^ Ap * Real.exp (-(Real.pi / 2 * t⁻¹))
              = (Cp * Lp * 3 ^ Ap / cDv) * ((1 + t⁻¹) ^ Ap * Real.exp (-(Real.pi / 2 * t⁻¹))) := by
                ring
            _ ≤ (Cp * Lp * 3 ^ Ap / cDv)
                * ((1 + t⁻¹) ^ M * Real.exp (-(Real.pi / 2 * t⁻¹))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_right hApow (Real.exp_nonneg _)
            _ = (Cp * Lp * 3 ^ Ap / cDv) * ((1 + t⁻¹) ^ M * Real.exp (-(Real.pi / 2 * t⁻¹))) := rfl
        have hMfin : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
            ≤ (Cm * Lm * 3 ^ Am / cDv) * QE := by
          refine le_trans (le_trans hKminus hM1) ?_
          rw [hQEdef]
          calc (Cm * Lm * 3 ^ Am / cDv) * (1 + t⁻¹) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * t⁻¹))
              = (Cm * Lm * 3 ^ Am / cDv)
                * ((1 + t⁻¹) ^ (Am + 2) * Real.exp (-(Real.pi / 2 * t⁻¹))) := by ring
            _ ≤ (Cm * Lm * 3 ^ Am / cDv)
                * ((1 + t⁻¹) ^ M * Real.exp (-(Real.pi / 2 * t⁻¹))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_right hMpow (Real.exp_nonneg _)
        exact le_trans htri (combine_bounds _ _ _ _ QE _ hPfin hMfin hQEpos hCB)
    have hKaxis : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        = ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖ := by
      rw [Work.Kernels.Kaxis, dif_pos ht]
    rw [hKaxis,
      show (1 + 1 / t) = (1 + t⁻¹) by rw [one_div],
      show -(Real.pi / 2 / t) = -(Real.pi / 2 * t⁻¹) by rw [div_eq_mul_inv]]
    exact le_trans hfinal (le_of_eq (by rw [hQEdef]; ring))

end Work.Asymptotics
