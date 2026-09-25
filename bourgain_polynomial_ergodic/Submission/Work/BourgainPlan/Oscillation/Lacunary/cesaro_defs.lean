import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le

/-!
# The Cesàro profile, its weight, and the elementary facts

The Cesàro (i.e. `P = X`) multiplier at the scale `N` is the *closed form*

  `m_N(θ) = N⁻¹ (e^{2πiNθ} - 1) / (e^{2πiθ} - 1)`,

and it factors exactly as

  `m_N(θ) = h(N θ) · r(θ)`,   `h(u) = (e^{2πiu} - 1)/(2πiu)`,  `r(θ) = 2πiθ/(e^{2πiθ} - 1)`.

The *profile* `h` is the dilation factor (a fixed function evaluated at the dilated argument
`u = N θ`) and the *weight* `r` is the correction factor (a fixed function of `θ`, smooth on the
circle except for the pole at `θ = 1`).

This file provides the vocabulary and the elementary facts:

* `cesH`, `cesR`, `cesM` — the profile, the weight, the multiplier, and the identity
  `cesM N θ = cesH (N θ) * cesR θ` on `(0,1]`;
* `cesRT` — the weight truncated to `(0,1/2]`, where it is bounded by `π/2` (so that the pole
  at `1` is avoided);
* `cesM_conj_symm` — the half-circle symmetry `m_N(1-ε) = conj (m_N ε)`;
* `cesH1`/`cesH2` — the split of the profile into its `u ≤ 1` part (carried by the one-sided
  frequency cuts `1_{θ ≤ t/N}`) and its oscillating tail `u > 1`;
* `cesHd` — the Stieltjes density of `cesH1`, in the *integral* form
  `h'(u) = ∫_0^1 2πis e^{2πius} ds`, which has the advantage of being bounded by `π` on `(0,1]`.

The remaining facts (the Stieltjes representation of `cesH1` and the square-summability of the
tail `cesH2` along the lacunary scales) are proved separately.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- **The Cesàro profile** `h(u) = (e^{2πiu} - 1)/(2πiu)`. -/
noncomputable def cesH (u : ℝ) : ℂ :=
  (Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) - 1) / (2 * Real.pi * Complex.I * (u : ℂ))

/-- **The Stieltjes density of the profile**, in the integral form
`h'(u) = ∫_0^1 2πis · e^{2πius} ds`.  This is the derivative of the profile and is bounded by
`π` on all of `(0,1]`, which is what the superposition argument needs. -/
noncomputable def cesHd (u : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..1, 2 * Real.pi * Complex.I * (s : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) * (s : ℂ))

/-- The part of the profile carried by the one-sided cuts: `h(u)` for `u ≤ 1`, `0` beyond. -/
noncomputable def cesH1 (u : ℝ) : ℂ := if u ≤ 1 then cesH u else 0

/-- The oscillating tail of the profile: `h(u)` for `u > 1`, `0` below. -/
noncomputable def cesH2 (u : ℝ) : ℂ := if 1 < u then cesH u else 0

/-- **The Cesàro weight** `r(θ) = 2πiθ/(e^{2πiθ} - 1)`. -/
noncomputable def cesR (θ : ℝ) : ℂ :=
  2 * Real.pi * Complex.I * (θ : ℂ) / (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1)

/-- The weight truncated to the first half of the circle, where it is bounded by `π/2` and avoids
the pole of `cesR` at `θ = 1`. -/
noncomputable def cesRT (θ : ℝ) : ℂ := if 0 < θ ∧ θ ≤ 1 / 2 then cesR θ else 0

/-- **The Cesàro multiplier** `m_N(θ) = N⁻¹(e^{2πiNθ} - 1)/(e^{2πiθ} - 1)`. -/
noncomputable def cesM (N : ℕ) (θ : ℝ) : ℂ :=
  ((N : ℂ))⁻¹ * ((Complex.exp (2 * Real.pi * Complex.I * ((N : ℝ) * θ)) - 1) /
    (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1))

/-! ## Elementary identities -/

lemma exp_int_mul_two_pi_I (n : ℤ) : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by ring⟩

lemma two_pi_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Complex.I_ne_zero, Real.pi_ne_zero]

lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

lemma exp_two_pi_I_mul_ne_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) ≠ 1 := by
  intro hc
  rw [Complex.exp_eq_one_iff] at hc
  obtain ⟨n, hn⟩ := hc
  have h2 : (θ : ℂ) = (n : ℂ) := by
    have h3 : (2 * Real.pi * Complex.I) * (θ : ℂ) = (2 * Real.pi * Complex.I) * (n : ℂ) := by
      rw [hn]; ring
    exact mul_left_cancel₀ two_pi_I_ne_zero h3
  have hθn : θ = (n : ℝ) := by exact_mod_cast h2
  have hn0 : n = 0 := by
    have hlt : (n : ℝ) < 1 := by rw [← hθn]; exact h1
    have hgt : (0:ℝ) < n := by rw [← hθn]; exact h0
    have hlt' : n < 1 := by exact_mod_cast hlt
    have hgt' : 0 < n := by exact_mod_cast hgt
    omega
  rw [hn0] at hθn
  simp at hθn
  exact absurd hθn (ne_of_gt h0)

lemma cesH_one : cesH 1 = 0 := by
  have h : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
    have h' : (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ))
        = ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [h', exp_int_mul_two_pi_I]
  rw [cesH, h]
  simp

lemma cesH_split (u : ℝ) : cesH u = cesH1 u + cesH2 u := by
  rw [cesH1, cesH2]
  by_cases h : u ≤ 1
  · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
  · rw [if_neg h, if_pos (not_le.mp h)]; ring

/-- The fundamental factorisation `m_N(θ) = h(Nθ)·r(θ)` on `(0,1]`.  (The endpoints `θ = 0` and
`θ = 1` are the two places where numerator and denominator of the closed form both vanish; there
both sides are `0`, and only `θ = 1` belongs to `(0,1]`.) -/
lemma cesM_eq_cesH_cesR (N : ℕ) (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0:ℝ) 1) :
    cesM N θ = cesH ((N : ℝ) * θ) * cesR θ := by
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1
    have hE : Complex.exp (2 * Real.pi * Complex.I * ((N : ℝ) * 1 : ℝ)) = 1 := by
      have : (2 * Real.pi * Complex.I * ((N : ℝ) * 1 : ℝ) : ℂ)
          = ((N : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [this, exp_int_mul_two_pi_I]
    have hE1 : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      have : (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ) : ℂ)
          = ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [this, exp_int_mul_two_pi_I]
    simp [cesM, cesH, cesR, hE, hE1]
  · have hθ0 : (θ : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hθ.1)
    have hN0 : (N : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
    have hNθ : ((N : ℝ) * θ : ℂ) ≠ 0 := by
      have hpos : (0:ℝ) < (N : ℝ) * θ := by
        have : (0:ℝ) < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN))
        exact mul_pos this hθ.1
      exact_mod_cast ne_of_gt hpos
    have hF : Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1 ≠ 0 :=
      sub_ne_zero.mpr (exp_two_pi_I_mul_ne_one hθ.1 h1)
    rw [cesM, cesH, cesR]
    push_cast
    field_simp

/-- **The half-circle symmetry** `m_N(1-ε) = conj (m_N ε)`. -/
lemma cesM_conj_symm (N : ℕ) {ε : ℝ} (hε : ε ∈ Set.Ioc (0:ℝ) 1) :
    cesM N (1 - ε) = (starRingEnd ℂ) (cesM N ε) := by
  have hc1 : (starRingEnd ℂ)
        (Complex.exp (2 * Real.pi * Complex.I * (((N : ℝ) : ℂ) * ((ε : ℝ) : ℂ))))
      = Complex.exp (-(2 * Real.pi * Complex.I * (((N : ℝ) : ℂ) * ((ε : ℝ) : ℂ)))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hc2 : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * ((ε : ℝ) : ℂ)))
      = Complex.exp (-(2 * Real.pi * Complex.I * ((ε : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hexp1 : Complex.exp (2 * Real.pi * Complex.I * (((N : ℝ) : ℂ) * ((1 - ε : ℝ) : ℂ)))
      = Complex.exp (-(2 * Real.pi * Complex.I * (((N : ℝ) : ℂ) * ((ε : ℝ) : ℂ)))) := by
    have hdiff : (2 * Real.pi * Complex.I * (((N : ℝ) : ℂ) * ((1 - ε : ℝ) : ℂ)))
        = -(2 * Real.pi * Complex.I * (((N : ℝ) : ℂ) * ((ε : ℝ) : ℂ)))
          + ((N : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [hdiff, Complex.exp_add, exp_int_mul_two_pi_I, mul_one]
  have hexp2 : Complex.exp (2 * Real.pi * Complex.I * ((1 - ε : ℝ) : ℂ))
      = Complex.exp (-(2 * Real.pi * Complex.I * ((ε : ℝ) : ℂ))) := by
    have hdiff : (2 * Real.pi * Complex.I * ((1 - ε : ℝ) : ℂ))
        = -(2 * Real.pi * Complex.I * ((ε : ℝ) : ℂ))
          + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [hdiff, Complex.exp_add, exp_int_mul_two_pi_I, mul_one]
  rw [cesM, cesM, hexp1, hexp2]
  simp only [map_mul, map_inv₀, map_div₀, map_sub, map_one, map_natCast, hc1, hc2]

/-- The weight bound on the first half-circle: `|r| ≤ π/2` there (the pole of `r` sits at `θ = 1`,
so the truncation is bounded). -/
lemma cesRT_norm_le (θ : ℝ) : ‖cesRT θ‖ ≤ Real.pi / 2 := by
  rw [cesRT]
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    have hpos : 0 < 2 * Real.pi * θ := by positivity
    have hsin : 2 * θ ≤ Real.sin (Real.pi * θ) := by
      have hle : Real.pi * θ ≤ Real.pi / 2 := by
        have h := mul_le_mul_of_nonneg_left h1 (le_of_lt Real.pi_pos)
        linarith
      have := Real.mul_le_sin (show (0:ℝ) ≤ Real.pi * θ by positivity) hle
      have h2 : (2 / Real.pi) * (Real.pi * θ) = 2 * θ := by field_simp
      rwa [h2] at this
    have hden : ‖Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1‖
        = 2 * Real.sin (Real.pi * θ) := by
      have harg : (2:ℂ) * (Real.pi:ℂ) * Complex.I * (θ : ℂ)
          = Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ) := by push_cast; ring
      rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one,
        show (2 * Real.pi * θ : ℝ) / 2 = Real.pi * θ by ring, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by
          exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
            (by nlinarith [Real.pi_pos, h1]))]
    have hnum : ‖(2:ℂ) * (Real.pi:ℂ) * Complex.I * (θ : ℂ)‖ = 2 * Real.pi * θ := by
      rw [show (2:ℂ) * (Real.pi:ℂ) * Complex.I * (θ : ℂ)
            = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex,
        abs_of_nonneg (by positivity)]
    rw [cesR, norm_div, hden, hnum, div_le_iff₀ (by nlinarith [hsin, h0, Real.pi_pos])]
    nlinarith [Real.pi_pos]
  · rw [norm_zero]; positivity

/-- The profile bound far from the origin: `|h(u)| ≤ 1/(πu)` for `u > 0`. -/
lemma cesH_norm_le (u : ℝ) (hu : 0 < u) : ‖cesH u‖ ≤ 1 / (Real.pi * u) := by
  rw [cesH, norm_div]
  have hnum : ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) - 1‖ ≤ 2 := by
    have harg : (2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)
        = Complex.I * ((2 * Real.pi * u : ℝ) : ℂ) := by push_cast; ring
    rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * u : ℝ) / 2 = Real.pi * u by ring, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [Real.abs_sin_le_one (Real.pi * u)]
  have hden : ‖(2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)‖ = 2 * Real.pi * u := by
    rw [show (2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)
          = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex,
      abs_of_nonneg (by positivity)]
  rw [hden, div_le_iff₀ (by positivity)]
  rw [show 1 / (Real.pi * u) * (2 * Real.pi * u) = 2 by field_simp]
  exact hnum

/-- The profile is bounded by `1` everywhere. -/
lemma cesH_norm_le_one (u : ℝ) : ‖cesH u‖ ≤ 1 := by
  by_cases hu : u = 0
  · subst hu; simp [cesH]
  · rw [cesH, norm_div]
    have hnum : ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) - 1‖
        ≤ ‖(2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)‖ := by
      have harg : (2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)
          = Complex.I * ((2 * Real.pi * u : ℝ) : ℂ) := by push_cast; ring
      rw [harg]
      simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * u)
    have hprod : (2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hu
    have hden : 0 < ‖(2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)‖ :=
      norm_pos_iff.mpr hprod
    calc ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) - 1‖
          / ‖(2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)‖
        ≤ ‖(2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)‖
          / ‖(2:ℂ) * (Real.pi:ℂ) * Complex.I * (u : ℂ)‖ := by
          exact div_le_div_of_nonneg_right hnum hden.le
      _ = 1 := div_self (ne_of_gt hden)

/-- The Cesàro multiplier is bounded by `1` on `(0,1]` (the geometric-sum form of the closed
expression).  This is what makes the integrands of the Cesàro integrals integrable. -/
lemma cesM_norm_le_one (N : ℕ) (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0:ℝ) 1) :
    ‖cesM N θ‖ ≤ 1 := by
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1; simp [cesM]
  · set F : ℂ := Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) with hF
    have hF1 : F ≠ 1 := hF ▸ exp_two_pi_I_mul_ne_one hθ.1 h1
    have hgs : ∑ i ∈ Finset.range N, F ^ i = (F ^ N - 1) / (F - 1) := geom_sum_eq hF1 N
    have hpow : Complex.exp (2 * Real.pi * Complex.I * ((N:ℝ) * θ)) = F ^ N := by
      rw [hF, ← Complex.exp_nat_mul]
      congr 1
      push_cast; ring
    have hFn : ∀ i : ℕ, ‖F ^ i‖ = 1 := by
      intro i
      rw [Complex.norm_pow]
      have h1' : ‖F‖ = 1 := by
        rw [hF, Complex.norm_exp]
        have : (2 * Real.pi * Complex.I * (θ : ℂ)).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [this, Real.exp_zero]
      rw [h1', one_pow]
    rw [cesM, norm_mul, hpow, ← hgs]
    have hsum : ‖∑ i ∈ Finset.range N, F ^ i‖ ≤ (N : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_congr rfl (fun i _ => hFn i)]
      simp
    have hNinv : ‖((N : ℂ))⁻¹‖ = (N : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    rw [hNinv]
    have hNpos : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    calc (N:ℝ)⁻¹ * ‖∑ i ∈ Finset.range N, F ^ i‖ ≤ (N:ℝ)⁻¹ * N :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := by field_simp

/-- `cesRT` is measurable. -/
lemma measurable_cesRT : Measurable cesRT := by
  have hcesR : Measurable cesR := by
    unfold cesR
    exact (measurable_const.mul Complex.measurable_ofReal).div
      ((Complex.measurable_exp.comp (by fun_prop)).sub measurable_const)
  unfold cesRT
  exact Measurable.ite measurableSet_Ioc hcesR measurable_const

lemma measurable_cesH : Measurable cesH := by
  unfold cesH
  exact ((Complex.measurable_exp.comp (by fun_prop)).sub measurable_const).div
    (measurable_const.mul Complex.measurable_ofReal)

lemma measurable_cesH1 : Measurable cesH1 := by
  unfold cesH1
  exact Measurable.ite measurableSet_Iic measurable_cesH measurable_const

lemma measurable_cesH2 : Measurable cesH2 := by
  unfold cesH2
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_cesH
    measurable_const

lemma continuous_cesHd : Continuous cesHd := by
  unfold cesHd
  fun_prop

lemma measurable_cesHd : Measurable cesHd := continuous_cesHd.measurable

/-- The Stieltjes density is bounded by `π`. -/
lemma cesHd_norm_le (u : ℝ) : ‖cesHd u‖ ≤ Real.pi := by
  rw [cesHd]
  refine (intervalIntegral.norm_integral_le_integral_norm (show (0:ℝ) ≤ 1 by norm_num)).trans ?_
  have hpt : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      ‖2 * Real.pi * Complex.I * (s : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) * (s : ℂ))‖ = 2 * Real.pi * s := by
    intro s hs
    rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hs
    have h1 : ‖2 * Real.pi * Complex.I * (s : ℂ)‖ = 2 * Real.pi * |s| := by
      rw [show 2 * Real.pi * Complex.I * (s : ℂ) = ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I by
            push_cast; ring,
        Complex.norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex, abs_mul,
        abs_of_nonneg (by positivity)]
    have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) * (s : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (2 * Real.pi * Complex.I * (u : ℂ) * (s : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_zero]
    rw [norm_mul, h1, h2, mul_one, abs_of_nonneg hs.1]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, integral_id,
    show 2 * Real.pi * ((1 ^ 2 - 0 ^ 2) / 2) = Real.pi by ring]

end

end Work.BourgainPlan.Oscillation.Lacunary
