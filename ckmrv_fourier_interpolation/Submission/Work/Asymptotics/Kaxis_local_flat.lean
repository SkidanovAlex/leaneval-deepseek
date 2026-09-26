import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.KPlus_slash_cusp_ball
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq
import Submission.Work.Asymptotics.KMinus_slash_cusp_ball
import Submission.Work.Asymptotics.KaxisMid.LocalMiddle
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-! ## 0. Exponential decay beats every power -/

/-- For `0 < t ≤ 1`, `exp (-(c/t)) ≤ K * t^N`. -/
lemma exp_neg_div_le_mul_rpow (c N : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      Real.exp (-(c / t)) ≤ K * t ^ N := by
  set m : ℕ := Nat.ceil N with hm
  have hmN : N ≤ (m : ℝ) := Nat.le_ceil N
  set K : ℝ := (m.factorial : ℝ) / c ^ m with hK
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
    exact div_pos h1 (pow_pos hc m)
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t ht ht1 => ?_⟩
  have hmf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have hpow : (c / t) ^ m / (m.factorial : ℝ) ≤ Real.exp (c / t) :=
    Real.pow_div_factorial_le_exp (c / t) (by positivity) m
  have hpos : 0 < (c / t) ^ m / (m.factorial : ℝ) := by positivity
  have hkey : Real.exp (-(c / t)) ≤ K * t ^ m := by
    have hinv : (Real.exp (c / t))⁻¹ ≤ ((c / t) ^ m / (m.factorial : ℝ))⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hpow
    have hval : ((c / t) ^ m / (m.factorial : ℝ))⁻¹ = (m.factorial : ℝ) * t ^ m / c ^ m := by
      rw [inv_div, div_pow]
      field_simp
    rw [← Real.exp_neg, hval] at hinv
    have h2 : (m.factorial : ℝ) * t ^ m / c ^ m = K * t ^ m := by rw [hK]; ring
    rw [← h2]
    exact hinv
  have hmle : t ^ m ≤ t ^ N := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 hmN
    simpa [Real.rpow_natCast] using h
  calc Real.exp (-(c / t)) ≤ K * t ^ m := hkey
    _ ≤ K * t ^ N := mul_le_mul_of_nonneg_left hmle hKpos.le
    _ ≤ max K 1 * t ^ N :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le N)

/-! ## 1. The CKMRV cusp bound for `K_+` (cleanliness-free) -/

/-- **CKMRV Lemma 4.12 `(quotientbounds1new)` for `K_+`**, in the `γ = I` case, on the region
`Im z ≥ 1`.  This is `Work.Asymptotics.KPlus_slash_cusp_ball` with the (unused and, for balls
meeting the imaginary axis, false) hygiene hypothesis removed; the proof is the same, through
`Xi8_eq`/`Xi24_eq` and `Xi8_bound`/`Xi24_bound`. -/
theorem KPlus_slash_ball (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KPlus d τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  rcases hd with rfl | rfl
  · obtain ⟨C, hC, hX⟩ := Xi8_bound τ₀ R
    set c8 : ℂ := (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hc8
    have hc8ne : c8 ≠ 0 := by
      rw [hc8]
      refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
      exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    refine ⟨max (C / ‖c8‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun τ z hτ hz hne => ?_⟩
    set D : ℂ := Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) with hD
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
    have hXi : (z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z) = Xi8 τ z / (c8 * D) := by
      rw [eq_div_iff (mul_ne_zero hc8ne hD0), hc8, hD, mul_comm]
      exact Xi8_eq τ z hne
    have hzpow : (z : ℂ) ^ (-((2 : ℤ) - (((8 : ℕ)) : ℤ) / 2)) = (z : ℂ) ^ 2 := by
      have h2 : -((2 : ℤ) - (((8 : ℕ)) : ℤ) / 2) = ((2 : ℕ) : ℤ) := by norm_num
      rw [h2, _root_.zpow_natCast]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hq := hX τ z hτ hz
    have hqn : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := norm_qParamFun z
    have hc8n : ‖c8‖ = ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ := by rw [hc8]
    have hDn : ‖D‖ = ‖Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by rw [hD]
    have hqle : Real.exp (-(2 * Real.pi * z.im))
        ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im)) := by
      have h1 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, z.im_pos]
      have h3 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by
        have h := norm_nonneg (z : ℂ); linarith
      have h2 : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 := by nlinarith
      nlinarith [Real.exp_pos (-(Real.pi * z.im))]
    have hc8pos : 0 < ‖c8‖ := norm_pos_iff.mpr hc8ne
    calc ‖Xi8 τ z‖ / (‖c8‖ * ‖D‖)
        ≤ C * ‖Work.Kernels.qParamFun z‖ / (‖c8‖ * ‖D‖) :=
          div_le_div_of_nonneg_right hq (by positivity)
      _ = C / ‖c8‖ * (Real.exp (-(2 * Real.pi * z.im)) / ‖D‖) := by
          rw [hqn]; ring_nf
      _ ≤ C / ‖c8‖ * (((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))) / ‖D‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right hqle (norm_nonneg D)
      _ ≤ max (C / ‖c8‖) 1 *
            (((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))) / ‖D‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max (C / ‖c8‖) 1 * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
            Real.exp (-(Real.pi * z.im)) / ‖D‖ := by ring
      _ = max (C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 *
            (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
          rw [hc8n, hDn]
  · obtain ⟨C, hC, hX⟩ := Xi24_bound τ₀ R
    set c24 : ℂ := (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hc24
    have hc24ne : c24 ≠ 0 := by
      rw [hc24]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
      · simp [Work.Kernels.c1728]
      · exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    refine ⟨max (C / ‖c24‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun τ z hτ hz hne => ?_⟩
    set D : ℂ := Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) with hD
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
    have hXi : (z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z) = Xi24 τ z / (c24 * D) := by
      rw [eq_div_iff (mul_ne_zero hc24ne hD0), hc24, hD, mul_comm]
      exact Xi24_eq τ z hne
    have hzpow : (z : ℂ) ^ (-((2 : ℤ) - (((24 : ℕ)) : ℤ) / 2)) = (z : ℂ) ^ 10 := by
      have h2 : -((2 : ℤ) - (((24 : ℕ)) : ℤ) / 2) = ((10 : ℕ) : ℤ) := by norm_num
      rw [h2, _root_.zpow_natCast]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hq := hX τ z hτ hz
    have hqn : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := norm_qParamFun z
    have hc24n : ‖c24‖ = ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ := by
      rw [hc24]
    have hDn : ‖D‖ = ‖Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by rw [hD]
    have hqle : Real.exp (-(2 * Real.pi * z.im))
        ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im)) := by
      have h1 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, z.im_pos]
      have h3 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by
        have h := norm_nonneg (z : ℂ); linarith
      have h2 : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 := by nlinarith
      nlinarith [Real.exp_pos (-(Real.pi * z.im))]
    calc ‖Xi24 τ z‖ / (‖c24‖ * ‖D‖)
        ≤ C * ‖Work.Kernels.qParamFun z‖ / (‖c24‖ * ‖D‖) :=
          div_le_div_of_nonneg_right hq (by positivity)
      _ = C / ‖c24‖ * (Real.exp (-(2 * Real.pi * z.im)) / ‖D‖) := by
          rw [hqn]; ring_nf
      _ ≤ C / ‖c24‖ * (((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))) / ‖D‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right hqle (norm_nonneg D)
      _ ≤ max (C / ‖c24‖) 1 *
            (((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))) / ‖D‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max (C / ‖c24‖) 1 * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
            Real.exp (-(Real.pi * z.im)) / ‖D‖ := by ring
      _ = max (C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 *
            (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
          rw [hc24n, hDn]

/-! ## 2. The CKMRV cusp bound for `K_-` (cleanliness-free) -/

/-- **CKMRV Lemma 4.12 `(quotientbounds1new)` for `K_-`**, with the hygiene hypothesis removed. -/
theorem KMinus_slash_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
  slash_cusp_ball_of ℓ d hd hR (KMinusCuspBallBound ℓ d hd hR) (KMinusCuspBallLimit ℓ d hd)
    (mdiff_eta ℓ d)


/-! ## 3. The divisor factor near the cusp `0` -/

/-- **The divisor factor `Δ(i y)(j τ − j(i y))` is bounded below by `1/4`** for `y` large, uniformly
for all `τ` with `‖j τ‖ ≤ M`.  Indeed `Δ(w)j(w) = E₄(w)³` with `E₄(i y) → 1` and `Δ(i y) → 0`,
so `Δ(i y)(j τ − j(i y)) = Δ(i y) j τ − E₄(i y)³ → −1` uniformly. -/
lemma divisor_factor_lower (M : ℝ) (hM : 0 ≤ M) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ (y : ℝ) (hy : 0 < y), Y ≤ y → ∀ τ : UpperHalfPlane,
      ‖Work.Kernels.jInvariantFun τ‖ ≤ M →
      (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis y hy) *
        (Work.Kernels.jInvariantFun τ -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis y hy))‖ := by
  obtain ⟨Ce, hCe, hE4⟩ := E4Fun_two_term
  obtain ⟨Cd, hCd, hΔ⟩ := DeltaFun_upper
  set cE : ℝ := 240 + Ce + 1 with hcE
  have hcE1 : (240 : ℝ) ≤ cE := by rw [hcE]; linarith
  have hcE0 : 0 < cE := lt_of_lt_of_le (by norm_num) hcE1
  have hqlim : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun y : ℝ => 2 * Real.pi * y) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
    have h3 : Filter.Tendsto (fun y : ℝ => -(2 * Real.pi * y)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h2
    exact Real.tendsto_exp_atBot.comp h3
  set B : ℝ := M * Cd + 7 * cE with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hev : ∀ᶠ y : ℝ in Filter.atTop,
      B * Real.exp (-(2 * Real.pi * y)) ≤ 1 / 4 := by
    have h : Filter.Tendsto (fun y : ℝ => B * Real.exp (-(2 * Real.pi * y))) Filter.atTop
        (nhds 0) := by simpa using hqlim.const_mul B
    exact h.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max Y₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy hY τ hjτ => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hY
  have hy0 : Y₀ ≤ y := le_trans (le_max_left _ _) hY
  set w : UpperHalfPlane := Work.Kernels.imagAxis y hy with hw
  have hwim : w.im = y := by simp [hw, Work.Kernels.imagAxis]
  have hhqy1 : Real.exp (-(2 * Real.pi * y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hy1]
  -- `‖Δ w‖ ≤ Cd * Real.exp (-(2 * Real.pi * y))`
  have hΔb : ‖Work.Kernels.DeltaFun w‖ ≤ Cd * Real.exp (-(2 * Real.pi * y)) := by
    have h1 := hΔ w (by rw [hwim]; exact hy1)
    have h2 : ‖Work.Kernels.qParamFun w‖ = Real.exp (-(2 * Real.pi * y)) := by
      rw [norm_qParamFun, hwim]
    rw [h2] at h1
    exact h1
  -- `‖E₄ w − 1‖ ≤ cE * Real.exp (-(2 * Real.pi * y))`
  have hE4b : ‖Work.Kernels.E4Fun w - 1‖ ≤ cE * Real.exp (-(2 * Real.pi * y)) := by
    have h1 := hE4 w (by rw [hwim]; exact hy1)
    have h2 : ‖Work.Kernels.qParamFun w‖ = Real.exp (-(2 * Real.pi * y)) := by
      rw [norm_qParamFun, hwim]
    rw [h2] at h1
    have h3 : ‖(240 : ℂ) * Work.Kernels.qParamFun w‖ = 240 * Real.exp (-(2 * Real.pi * y)) := by
      rw [norm_mul, h2]; norm_num
    have hsplit : ‖Work.Kernels.E4Fun w - 1‖
        ≤ ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w‖
          + 240 * Real.exp (-(2 * Real.pi * y)) := by
      have h := norm_add_le (Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w)
        ((240 : ℂ) * Work.Kernels.qParamFun w)
      rw [show Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
          + 240 * Work.Kernels.qParamFun w = Work.Kernels.E4Fun w - 1 from by ring, h3] at h
      exact h
    have h4 : Real.exp (-(2 * Real.pi * y)) ^ 2 ≤ Real.exp (-(2 * Real.pi * y)) := by nlinarith [Real.exp_pos (-(2 * Real.pi * y)), hhqy1]
    have h5 : Ce * Real.exp (-(2 * Real.pi * y)) ^ 2 ≤ Ce * Real.exp (-(2 * Real.pi * y)) := mul_le_mul_of_nonneg_left h4 hCe.le
    have h6 := le_trans h1 h5
    have h7 : Ce * Real.exp (-(2 * Real.pi * y)) + 240 * Real.exp (-(2 * Real.pi * y)) ≤ cE * Real.exp (-(2 * Real.pi * y)) := by
      rw [hcE]; nlinarith [Real.exp_pos (-(2 * Real.pi * y))]
    linarith [hsplit, h6, h7]
  -- `‖E₄ w ^ 3 − 1‖ ≤ 7 * cE * Real.exp (-(2 * Real.pi * y))`
  have hE4n : ‖Work.Kernels.E4Fun w‖ ≤ 2 := by
    have h7 : 7 * cE * Real.exp (-(2 * Real.pi * y)) ≤ B * Real.exp (-(2 * Real.pi * y)) := by
      rw [hB]
      have := Real.exp_pos (-(2 * Real.pi * y))
      nlinarith [mul_nonneg hM hCd.le]
    have h8 : B * Real.exp (-(2 * Real.pi * y)) ≤ 1 / 4 := hY₀ y hy0
    have h9 : cE * Real.exp (-(2 * Real.pi * y)) ≤ 7 * cE * Real.exp (-(2 * Real.pi * y)) := by
      have := Real.exp_pos (-(2 * Real.pi * y))
      nlinarith [hcE0]
    have h3 : cE * Real.exp (-(2 * Real.pi * y)) ≤ 1 := by linarith
    have h5 := norm_add_le (Work.Kernels.E4Fun w - 1) (1 : ℂ)
    rw [show Work.Kernels.E4Fun w - 1 + 1 = Work.Kernels.E4Fun w from by ring, norm_one] at h5
    linarith [h5, hE4b, h3]
  have hcube : ‖Work.Kernels.E4Fun w ^ 3 - 1‖ ≤ 7 * cE * Real.exp (-(2 * Real.pi * y)) := by
    have h2 : ‖Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1‖ ≤ 7 := by
      have h7 : ‖Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1‖
          ≤ ‖Work.Kernels.E4Fun w ^ 2‖ + ‖Work.Kernels.E4Fun w‖ + ‖(1 : ℂ)‖ :=
        le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
      rw [norm_pow, norm_one] at h7
      nlinarith [h7, hE4n, norm_nonneg (Work.Kernels.E4Fun w)]
    have hfac : Work.Kernels.E4Fun w ^ 3 - 1
        = (Work.Kernels.E4Fun w - 1)
          * (Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1) := by ring
    rw [hfac, norm_mul]
    calc ‖Work.Kernels.E4Fun w - 1‖ *
          ‖Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1‖
        ≤ (cE * Real.exp (-(2 * Real.pi * y))) * 7 := mul_le_mul hE4b h2 (norm_nonneg _) (by positivity)
      _ = 7 * cE * Real.exp (-(2 * Real.pi * y)) := by ring
  -- conclusion
  have hΔj' : ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ‖
      ≤ Cd * Real.exp (-(2 * Real.pi * y)) * M := by
    rw [norm_mul]
    exact mul_le_mul hΔb hjτ (norm_nonneg _) (by positivity)
  have hkey : Work.Kernels.DeltaFun w *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)
      = Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ - Work.Kernels.E4Fun w ^ 3 := by
    rw [mul_sub, Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
  rw [hkey]
  have hxa : ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
      - Work.Kernels.E4Fun w ^ 3 + 1‖ ≤ B * Real.exp (-(2 * Real.pi * y)) := by
    have hsplit : Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
        - Work.Kernels.E4Fun w ^ 3 + 1
        = Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
          + (1 - Work.Kernels.E4Fun w ^ 3) := by ring
    rw [hsplit]
    calc ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
          + (1 - Work.Kernels.E4Fun w ^ 3)‖
        ≤ ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ‖
          + ‖1 - Work.Kernels.E4Fun w ^ 3‖ := norm_add_le _ _
      _ ≤ Cd * Real.exp (-(2 * Real.pi * y)) * M + 7 * cE * Real.exp (-(2 * Real.pi * y)) := by
          refine add_le_add hΔj' ?_
          rw [norm_sub_rev]
          exact hcube
      _ = B * Real.exp (-(2 * Real.pi * y)) := by rw [hB]; ring
  have hxb : B * Real.exp (-(2 * Real.pi * y)) ≤ 1 / 4 := hY₀ y hy0
  have hxc : 1 - B * Real.exp (-(2 * Real.pi * y)) ≤
      ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ - Work.Kernels.E4Fun w ^ 3‖ := by
    have h10 := abs_norm_sub_norm_le (Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
      - Work.Kernels.E4Fun w ^ 3 + 1) (1 : ℂ)
    rw [show Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
        - Work.Kernels.E4Fun w ^ 3 + 1 - 1
        = Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun w ^ 3 from by ring, norm_one] at h10
    have h11 : ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
        - Work.Kernels.E4Fun w ^ 3 + 1‖ ≤ 1 := by linarith [hxa, hxb]
    have h12 : |‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun w ^ 3 + 1‖ - 1|
        = 1 - ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun w ^ 3 + 1‖ := by
      rw [abs_of_nonpos (by linarith [h11])]
      ring
    rw [h12] at h10
    linarith [h10]
  linarith [hxc, hxb]

/-! ## 4. The cusp bounds on a compact set -/

/-- **Cusp-`0` flatness from a slash bound.**  If a kernel `Kf` satisfies the CKMRV Lemma 4.12
bound `(quotientbounds1new)` on the ball `closedBall τ₁ R` for the weight `2 - d/2`, and the
divisor factor is bounded below by `1/4` on `Im z ≥ Y`, then `Kf` is flat along the contour:
`‖Kf τ (i t)‖ ≤ C t^{-24} exp (-π/t)` for `t ≤ δ`, uniformly on the ball. -/
theorem cusp_bound_of_slash (Kf : ℍ → ℍ → ℂ) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₁ : ℍ} {R C M Y : ℝ} (hC : 0 ≤ C)
    (hslash : ∀ (τ z : ℍ), dist τ τ₁ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Kf τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
    (hjM : ∀ τ : ℍ, dist τ τ₁ ≤ R → ‖Work.Kernels.jInvariantFun τ‖ ≤ M)
    (hY0 : 0 < Y)
    (hdiv : ∀ (y : ℝ) (hy : 0 < y), Y ≤ y → ∀ τ : ℍ,
      ‖Work.Kernels.jInvariantFun τ‖ ≤ M →
      (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis y hy) *
        (Work.Kernels.jInvariantFun τ -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis y hy))‖) :
    ∃ C' M' δ : ℝ, 0 < C' ∧ 0 ≤ M' ∧ 0 < δ ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      dist τ τ₁ ≤ R → t ≤ δ →
        ‖Kf τ (Work.Kernels.imagAxis t ht)‖ ≤ C' * t ^ (-M') * Real.exp (-(Real.pi / t)) := by
  refine ⟨16 * C + 1, 24, min 1 Y⁻¹, by positivity, by norm_num,
    lt_min one_pos (inv_pos.mpr hY0), fun τ t ht hτ htδ => ?_⟩
  have ht1 : t ≤ 1 := le_trans htδ (min_le_left _ _)
  have htY : t ≤ Y⁻¹ := le_trans htδ (min_le_right _ _)
  have hyY : Y ≤ t⁻¹ := by
    have h1 : t ≤ 1 / Y := by rw [← inv_eq_one_div]; exact htY
    have h2 : t * Y ≤ 1 := (le_div_iff₀ hY0).mp h1
    rw [inv_eq_one_div]
    exact (le_div_iff₀ ht).mpr (by rwa [mul_comm] at h2)
  have hjτ : ‖Work.Kernels.jInvariantFun τ‖ ≤ M := hjM τ hτ
  set z : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hz
  have hzim : z.im = t⁻¹ := by simp [hz, Work.Kernels.imagAxis]
  have hz1 : 1 ≤ z.im := by
    rw [hzim, inv_eq_one_div]
    exact (one_le_div₀ ht).mpr ht1
  have hznz : (z : ℂ) ≠ 0 := by
    intro hh
    have hpos := z.im_pos
    rw [← UpperHalfPlane.coe_im z, hh] at hpos
    simp at hpos
  have hznorm : ‖(z : ℂ)‖ = t⁻¹ := by
    have h1 : (z : ℂ) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := rfl
    rw [h1, Complex.norm_def, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I,
      mul_one, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (inv_pos.mpr ht).le]
  have hzS : ModularGroup.S • z = Work.Kernels.imagAxis t ht := by
    rw [hz, Work.Asymptotics.imagAxis_smul_S]
    apply UpperHalfPlane.ext
    simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk, inv_inv]
  have hdel : (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [hz]
    exact hdiv t⁻¹ (inv_pos.mpr ht) hyY τ hjτ
  have hjz : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro hcon
    have hzero : ‖Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ = 0 := by
      rw [hcon, sub_self, mul_zero, norm_zero]
    linarith [hdel, hzero]
  have hb := hslash τ z hτ hz1 hjz
  rw [hzS] at hb
  have hexp : Real.exp (-(Real.pi * z.im)) = Real.exp (-(Real.pi / t)) := by
    rw [hzim, div_eq_mul_inv]
  rw [hexp] at hb
  have hnum : ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
      Kf τ (Work.Kernels.imagAxis t ht)‖
      ≤ (16 * C) * t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)) := by
    have hzn : (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) ≤ 4 * t ^ (-(2 : ℝ)) := by
      have h2 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
      have h3 : 1 + ‖(z : ℂ)‖ ≤ 2 * t⁻¹ := by rw [hznorm]; linarith
      have h4 : (1 + ‖(z : ℂ)‖) ^ 2 ≤ (2 * t⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
      have h5 : (2 * t⁻¹) ^ 2 = 4 * t ^ (-(2 : ℝ)) := by
        have h6 : t ^ (-(2 : ℝ)) = (t ^ 2)⁻¹ := by
          rw [Real.rpow_neg ht.le]; norm_num
        rw [h6, mul_pow, inv_pow]; norm_num
      linarith [h4, h5.ge, h5.le]
    have h4 : C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi / t)) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        ≤ C * (4 * t ^ (-(2 : ℝ))) * Real.exp (-(Real.pi / t)) / (1 / 4) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) hdel
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzn hC) (Real.exp_nonneg _)
    refine le_trans hb (le_trans h4 (le_of_eq ?_))
    ring
  have hzm : ‖(z : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)‖ ≤ 1 := by
    rw [norm_zpow, hznorm]
    refine zpow_le_one_of_nonpos₀ ((one_le_inv₀ ht).mpr ht1) ?_
    rcases hd with hd8 | hd24
    · subst hd8; norm_num
    · subst hd24; norm_num
  have hfinal : ‖Kf τ (Work.Kernels.imagAxis t ht)‖
      ≤ (16 * C + 1) * t ^ (-(24 : ℝ)) * Real.exp (-(Real.pi / t)) := by
    have h24 : t ^ (-(2 : ℝ)) ≤ t ^ (-(24 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
    have hsplit : Kf τ (Work.Kernels.imagAxis t ht)
        = (z : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2) *
          ((z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Kf τ (Work.Kernels.imagAxis t ht)) := by
      rw [← mul_assoc, ← zpow_add₀ hznz, add_neg_cancel, zpow_zero, one_mul]
    have h1 : ‖Kf τ (Work.Kernels.imagAxis t ht)‖
        ≤ ‖(z : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)‖ *
          ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Kf τ (Work.Kernels.imagAxis t ht)‖ := by
      conv_lhs => rw [hsplit]
      exact norm_mul_le _ _
    have h2 : ‖(z : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)‖ *
          ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Kf τ (Work.Kernels.imagAxis t ht)‖
        ≤ 1 * ((16 * C) * t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t))) :=
      mul_le_mul hzm hnum (norm_nonneg _) (by norm_num)
    have h3 : (1 : ℝ) * ((16 * C) * t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)))
        ≤ (16 * C) * t ^ (-(24 : ℝ)) * Real.exp (-(Real.pi / t)) := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h24 (mul_nonneg (by norm_num) hC)) (Real.exp_nonneg _)
    have h4 : (16 * C) * t ^ (-(24 : ℝ)) * Real.exp (-(Real.pi / t))
        ≤ (16 * C + 1) * t ^ (-(24 : ℝ)) * Real.exp (-(Real.pi / t)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht.le _))
        (Real.exp_nonneg _)
    linarith [h1, h2, h3, h4]
  exact hfinal

/-- **Cusp-`0` flatness of `K_+`** on the contour, uniformly on a compact `K ⊆ 𝒟`. -/
theorem KPlus_cusp_bound (d : ℕ) (hd : d = 8 ∨ d = 24) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∃ C M δ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 < δ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      τ ∈ K → t ≤ δ →
        ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖
          ≤ C * t ^ (-M) * Real.exp (-(Real.pi / t)) := by
  obtain ⟨R, hr⟩ := (Metric.isBounded_iff_subset_closedBall
    (⟨Complex.I, by simp⟩ : UpperHalfPlane)).mp hK.isBounded
  set τ₁ : UpperHalfPlane := ⟨Complex.I, by simp⟩ with hτ₁
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : ∀ τ : ℍ, τ ∈ K → dist τ τ₁ ≤ R' := by
    intro τ hτ
    have h1 : dist τ τ₁ ≤ R := Metric.mem_closedBall.mp (hr hτ)
    calc dist τ τ₁ ≤ R := h1
      _ ≤ R' := le_max_left R 1
  obtain ⟨C1, hC1, hslash⟩ := KPlus_slash_ball d hd hR'pos
  have hC1pos : 0 < C1 := hC1
  obtain ⟨M, hMpos, hjM⟩ := exists_bound_on_closedBall continuous_jInvariantFun τ₁ R'
  obtain ⟨Y, hYpos, hdiv⟩ := divisor_factor_lower M hMpos.le
  obtain ⟨C', M', δ, hC', hM', hδ, hb⟩ := cusp_bound_of_slash (Work.Kernels.KPlus d) d hd
    hC1pos.le hslash (fun τ hτ => hjM τ hτ)
    hYpos hdiv
  exact ⟨C', M', δ, hC', hM', hδ, fun τ t ht hτ htδ => hb τ t ht (hKR τ hτ) htδ⟩

/-- **Cusp-`0` flatness of `K_-`** on the contour, uniformly on a compact `K ⊆ 𝒟`. -/
theorem KMinus_cusp_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∃ C M δ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 < δ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      τ ∈ K → t ≤ δ →
        ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
          ≤ C * t ^ (-M) * Real.exp (-(Real.pi / t)) := by
  obtain ⟨R, hr⟩ := (Metric.isBounded_iff_subset_closedBall
    (⟨Complex.I, by simp⟩ : UpperHalfPlane)).mp hK.isBounded
  set τ₁ : UpperHalfPlane := ⟨Complex.I, by simp⟩ with hτ₁
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : ∀ τ : ℍ, τ ∈ K → dist τ τ₁ ≤ R' := by
    intro τ hτ
    have h1 : dist τ τ₁ ≤ R := Metric.mem_closedBall.mp (hr hτ)
    calc dist τ τ₁ ≤ R := h1
      _ ≤ R' := le_max_left R 1
  obtain ⟨C1, hC1, hslash⟩ := KMinus_slash_ball ℓ d hd hR'pos
  have hC1pos : 0 < C1 := hC1
  obtain ⟨M, hMpos, hjM⟩ := exists_bound_on_closedBall continuous_jInvariantFun τ₁ R'
  obtain ⟨Y, hYpos, hdiv⟩ := divisor_factor_lower M hMpos.le
  obtain ⟨C', M', δ, hC', hM', hδ, hb⟩ := cusp_bound_of_slash (Work.Kernels.KMinus ℓ d) d hd
    hC1pos.le hslash (fun τ hτ => hjM τ hτ)
    hYpos hdiv
  exact ⟨C', M', δ, hC', hM', hδ, fun τ t ht hτ htδ => hb τ t ht (hKR τ hτ) htδ⟩

/-! ## 5. `t^{-M} e^{-π/t}` is `O(t^N)` at `0⁺` -/

/-- For every `M`, `t ↦ t^{-M} exp (-π/t)` is `O (t^N)` as `t → 0⁺`, uniformly on `0 < t ≤ 1`. -/
lemma rpow_neg_mul_exp_le (M N : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      t ^ (-M) * Real.exp (-(Real.pi / t)) ≤ K * t ^ N := by
  obtain ⟨K, hK, hb⟩ := exp_neg_div_le_mul_rpow Real.pi (N + M) Real.pi_pos
  refine ⟨K, hK, fun t ht ht1 => ?_⟩
  have h1 : t ^ (-M) * Real.exp (-(Real.pi / t)) ≤ t ^ (-M) * (K * t ^ (N + M)) :=
    mul_le_mul_of_nonneg_left (hb t ht ht1) (Real.rpow_pos_of_pos ht _).le
  have h2 : t ^ (-M) * (K * t ^ (N + M)) = K * t ^ N := by
    have h3 : t ^ (-M) * (K * t ^ (N + M)) = K * (t ^ (-M) * t ^ (N + M)) := by ring
    rw [h3, ← Real.rpow_add ht, show -M + (N + M) = N from by ring]
  calc t ^ (-M) * Real.exp (-(Real.pi / t)) ≤ t ^ (-M) * (K * t ^ (N + M)) := h1
    _ = K * t ^ N := h2

/-! ## 6. The local flatness theorem -/

/-- **Flatness of the CKMRV kernel along the contour on a compact subset of `𝒟`.**

This is the *corrected* local form of `Work.Asymptotics.Kaxis_cusp_flat`, which is FALSE globally:
for `τ ∈ 𝒟` approaching the boundary `Re τ = ±1` the pole `z = τ ∓ 1` of `z ↦ K(τ,z)` (whose
residue is `∓1/(2π) ≠ 0`, CKMRV Theorem 4.9(3)) approaches the contour and `‖K(τ, it)‖` grows like
`1/‖τ ∓ 1‖`, which no bound with `(scale τ)`-constants can absorb.  On a *compact* `K ⊆ 𝒟` the
poles stay a positive distance away (the genuine poles `τ = γz` with `φ(γ) ≠ 0` lie on or outside
`∂𝒟`, while the interior coincidences `τ = it` (`γ = 1`) and `τ = i/t` (`γ = S`) have vanishing
residue and are removable), and the cusp `t → 0⁺` gives uniform exponential decay, hence
`t^N` for every `N`. -/
theorem Kaxis_local_flat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N := by
  intro N hN
  obtain ⟨C₁, M₁, δ₁, hC₁, hM₁, hδ₁, hb₁⟩ := KPlus_cusp_bound d hd hK hsub
  obtain ⟨C₂, M₂, δ₂, hC₂, hM₂, hδ₂, hb₂⟩ := KMinus_cusp_bound ℓ d hd hK hsub
  have hδpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  obtain ⟨C₃, hC₃, hb₃⟩ := Work.Asymptotics.KaxisMid.Kaxis_local_middle ℓ d hd hK hsub hδpos
  obtain ⟨K₀, hK₀, hbK⟩ := exp_neg_div_le_mul_rpow Real.pi (N + max M₁ M₂) Real.pi_pos
  refine ⟨max ((C₁ + C₂) * K₀) (C₃ * (min δ₁ δ₂) ^ (-N)), ?_, ?_⟩
  · exact lt_of_lt_of_le (mul_pos (by linarith) hK₀) (le_max_left _ _)
  · intro τ t hτ ht ht1
    rw [Work.Kernels.Kaxis, dif_pos ht]
    by_cases htδ : t ≤ min δ₁ δ₂
    · -- cusp regime `t ≤ min δ₁ δ₂`
      have hA := hb₁ τ t ht hτ (le_trans htδ (min_le_left δ₁ δ₂))
      have hB := hb₂ τ t ht hτ (le_trans htδ (min_le_right δ₁ δ₂))
      have hM : max M₁ M₂ = max M₁ M₂ := rfl
      have hsplit : ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤
          (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ +
            ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖) / 2 := by
        rw [Work.Kernels.Kfun, norm_div, show ‖((2 : ℂ))‖ = 2 from by norm_num]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      have hnum : (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ +
            ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖) / 2 ≤
          (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) := by
        have h1 : C₁ * t ^ (-M₁) * Real.exp (-(Real.pi / t)) ≤
            C₁ * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith [le_max_left M₁ M₂])) hC₁.le
        have h2 : C₂ * t ^ (-M₂) * Real.exp (-(Real.pi / t)) ≤
            C₂ * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith [le_max_right M₁ M₂])) hC₂.le
        have hsum : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ +
              ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤
            (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) := by
          have hdist : (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) =
              C₁ * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) +
                C₂ * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) := by ring
          linarith [hA, hB, h1, h2, hdist.le, hdist.ge]
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), show
          (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) * 2 =
            (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) +
              (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) from by ring]
        have hXn : (0 : ℝ) ≤ (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) :=
          mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.le _)) (Real.exp_nonneg _)
        linarith [hsum, hXn]
      have hfin : (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t)) ≤
          (C₁ + C₂) * K₀ * t ^ N := by
        have he : Real.exp (-(Real.pi / t)) ≤ K₀ * t ^ (N + max M₁ M₂) := hbK t ht ht1
        have h0 : 0 ≤ (C₁ + C₂) * t ^ (-(max M₁ M₂)) :=
          mul_nonneg (by linarith) (Real.rpow_nonneg ht.le _)
        calc (C₁ + C₂) * t ^ (-(max M₁ M₂)) * Real.exp (-(Real.pi / t))
            ≤ (C₁ + C₂) * t ^ (-(max M₁ M₂)) * (K₀ * t ^ (N + max M₁ M₂)) :=
              mul_le_mul_of_nonneg_left he h0
          _ = (C₁ + C₂) * K₀ * t ^ N := by
              rw [show (C₁ + C₂) * t ^ (-(max M₁ M₂)) * (K₀ * t ^ (N + max M₁ M₂)) =
                  (C₁ + C₂) * K₀ * (t ^ (-(max M₁ M₂)) * t ^ (N + max M₁ M₂)) from by ring,
                ← Real.rpow_add ht,
                show -(max M₁ M₂) + (N + max M₁ M₂) = N from by ring]
      have hfin2 : (C₁ + C₂) * K₀ * t ^ N ≤
          max ((C₁ + C₂) * K₀) (C₃ * (min δ₁ δ₂) ^ (-N)) * t ^ N :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le N)
      linarith [hsplit, hnum, hfin, hfin2]
    · -- middle regime `min δ₁ δ₂ < t ≤ 1`
      rw [not_le] at htδ
      have h1 : ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤ C₃ := by
        have h := hb₃ τ t hτ (le_of_lt htδ) ht1
        rwa [Work.Kernels.Kaxis, dif_pos ht] at h
      have hdt : (min δ₁ δ₂) ^ N ≤ t ^ N :=
        Real.rpow_le_rpow hδpos.le (le_of_lt htδ) hN
      have h2 : C₃ ≤ C₃ * (min δ₁ δ₂) ^ (-N) * t ^ N := by
        have h3 : C₃ * (min δ₁ δ₂) ^ (-N) * (min δ₁ δ₂) ^ N ≤
            C₃ * (min δ₁ δ₂) ^ (-N) * t ^ N :=
          mul_le_mul_of_nonneg_left hdt (mul_nonneg hC₃.le (Real.rpow_nonneg hδpos.le _))
        have h4 : C₃ * (min δ₁ δ₂) ^ (-N) * (min δ₁ δ₂) ^ N = C₃ := by
          rw [mul_assoc, ← Real.rpow_add hδpos, neg_add_cancel, Real.rpow_zero, mul_one]
        linarith [h3, h4.le, h4.ge]
      have h5 : C₃ * (min δ₁ δ₂) ^ (-N) * t ^ N ≤
          max ((C₁ + C₂) * K₀) (C₃ * (min δ₁ δ₂) ^ (-N)) * t ^ N :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le N)
      linarith [h1, h2, h5]

end

end Work.Asymptotics
