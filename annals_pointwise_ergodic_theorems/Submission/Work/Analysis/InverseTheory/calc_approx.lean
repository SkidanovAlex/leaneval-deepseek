import Mathlib
import Submission.Work.Analysis.InverseTheory.SchwartzConst
import Submission.Work.Analysis.InverseTheory.calc_of_decay

set_option autoImplicit false

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.Analysis.InverseTheory

/-!
# Lemma `calc` of Krause–Mirek–Tao: from Schwartz seminorms to the explicit bound

The companion module `calc_of_decay` proves the analytic content of Lemma `calc`: for a continuous
`ψ : ℝ → ℂ` with `∫ψ = 1` decaying like `⟨t⟩^{-12}` together with its Fourier transform `𝓕ψ`
(constant `C ≥ 1`), the Riemann sum `∑_{y ∈ [a,b]∩ℤ} ε ψ(ε(x-y))` approximates the indicator of
`[a,b]` up to `2^60 C² (ε^10 + ⟨ε(x-a)⟩^{-10} + ⟨ε(x-b)⟩^{-10})`.

This module supplies the other half: the decay hypotheses for a Schwartz function `ψ : 𝓢(ℝ, ℂ)`,
obtained from the Schwartz seminorms of order `12` (with the explicit constant
`C = 2^12 (schwartzSeminormSum ψ + 1)`), together with the final (purely arithmetic) comparison
`2^60 C² ≤ calcConst ψ = (schwartzSeminormSum ψ + 2)^100`.

Since `𝓕ψ(0) = ∫ψ = 1` and `‖𝓕ψ(0)‖ ≤ seminorm 0 0 (𝓕ψ) ≤ schwartzSeminormSum ψ`, the seminorm
sum is at least `1`; this is what makes the constant `(S + 2)^100` dominate `2^84 (S+1)^2`.
-/

/-! ## Decay from the Schwartz seminorms -/

/-- `⟨t⟩ ≤ 2|t|` for `|t| ≥ 1`. -/
lemma jb_le_two_mul_abs {t : ℝ} (h : 1 ≤ |t|) : jb t ≤ 2 * |t| := by
  have h2 := jb_le_two_mul_max_one_abs t
  rwa [max_eq_right h] at h2

/-- `⟨t⟩ ≤ 2` for `|t| ≤ 1`. -/
lemma jb_le_two {t : ℝ} (h : |t| ≤ 1) : jb t ≤ 2 := by
  have h1 := jb_le_one_add_abs t
  linarith

/-- For `|t| ≥ 1`, `|t|^{-12} ≤ 2^12 ⟨t⟩^{-12}`. -/
lemma inv_abs_pow_le_mul_jbDecay {t : ℝ} (h : 1 ≤ |t|) :
    (|t|⁻¹) ^ 12 ≤ (2 : ℝ) ^ 12 * jbDecay 12 t := by
  have hjb : jb t ≤ 2 * |t| := jb_le_two_mul_abs h
  have h1 : (2 * |t|)⁻¹ ≤ (jb t)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (jb_pos t)]
    exact hjb
  have h2 : ((2 * |t|)⁻¹) ^ 12 ≤ jbDecay 12 t := by
    rw [jbDecay]
    exact pow_le_pow_left₀ (by positivity) h1 12
  have h3 : ((2 * |t|)⁻¹) ^ 12 = ((2 : ℝ) ^ 12)⁻¹ * (|t|⁻¹) ^ 12 := by
    rw [mul_inv, mul_pow, inv_pow]
  rw [h3] at h2
  calc (|t|⁻¹) ^ 12 = 2 ^ 12 * (((2 : ℝ) ^ 12)⁻¹ * (|t|⁻¹) ^ 12) := by
        rw [← mul_assoc, mul_inv_cancel₀ (by norm_num : ((2 : ℝ) ^ 12) ≠ 0), one_mul]
    _ ≤ 2 ^ 12 * jbDecay 12 t := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- For `|t| ≤ 1`, `2^{-12} ≤ ⟨t⟩^{-12}`. -/
lemma inv_two_pow_le_jbDecay {t : ℝ} (h : |t| ≤ 1) : ((2 : ℝ)⁻¹) ^ 12 ≤ jbDecay 12 t := by
  have hjb : jb t ≤ 2 := jb_le_two h
  have h1 : ((2 : ℝ))⁻¹ ≤ (jb t)⁻¹ := by
    rw [inv_le_inv₀ (by norm_num) (jb_pos t)]
    exact hjb
  calc ((2 : ℝ)⁻¹) ^ 12 ≤ ((jb t)⁻¹) ^ 12 := pow_le_pow_left₀ (by positivity) h1 12
    _ = jbDecay 12 t := rfl

/-- **Pointwise decay from two Schwartz seminorm bounds.**  If `‖·‖^{0} φ` and `‖·‖^{12} φ` are
bounded by `D ≥ 0` in the sense of the Schwartz seminorms `seminorm ℝ 0 0` and `seminorm ℝ 12 0`,
then `‖φ t‖ ≤ 2^12 (D+1) ⟨t⟩^{-12}`. -/
lemma norm_apply_le_of_seminorm_le (φ : SchwartzR) {D : ℝ} (hD0 : 0 ≤ D)
    (h0 : SchwartzMap.seminorm ℝ 0 0 φ ≤ D) (h12 : SchwartzMap.seminorm ℝ 12 0 φ ≤ D) (t : ℝ) :
    ‖φ t‖ ≤ (2 : ℝ) ^ 12 * (D + 1) * jbDecay 12 t := by
  rcases le_or_gt 1 |t| with h | h
  · -- large `|t|`: use the order-`12` seminorm
    have hpow : (0 : ℝ) < |t| ^ 12 := by positivity
    have hA : |t| ^ 12 * ‖φ t‖ ≤ SchwartzMap.seminorm ℝ 12 0 φ := by
      simpa only [Real.norm_eq_abs] using SchwartzMap.norm_pow_mul_le_seminorm ℝ φ 12 t
    have h1 : ‖φ t‖ ≤ (SchwartzMap.seminorm ℝ 12 0 φ) * (|t|⁻¹) ^ 12 := by
      have h2 : ‖φ t‖ ≤ SchwartzMap.seminorm ℝ 12 0 φ / |t| ^ 12 :=
        (le_div_iff₀ hpow).mpr (by rw [mul_comm]; exact hA)
      rwa [div_eq_mul_inv, ← inv_pow] at h2
    have h3 := inv_abs_pow_le_mul_jbDecay h
    calc ‖φ t‖ ≤ (SchwartzMap.seminorm ℝ 12 0 φ) * (|t|⁻¹) ^ 12 := h1
      _ ≤ D * (2 ^ 12 * jbDecay 12 t) :=
          mul_le_mul h12 h3 (by positivity) hD0
      _ ≤ 2 ^ 12 * (D + 1) * jbDecay 12 t := by
          have hj := jbDecay_nonneg 12 t
          have hD1 : D ≤ D + 1 := by linarith
          calc D * (2 ^ 12 * jbDecay 12 t) = 2 ^ 12 * D * jbDecay 12 t := by ring
            _ ≤ 2 ^ 12 * (D + 1) * jbDecay 12 t :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hD1 (by norm_num)) hj
  · -- small `|t|`: use the order-`0` seminorm and `⟨t⟩ ≤ 2`
    have habs : |t| ≤ 1 := le_of_lt h
    have h1 : ‖φ t‖ ≤ SchwartzMap.seminorm ℝ 0 0 φ := SchwartzMap.norm_le_seminorm ℝ φ t
    have h3 := inv_two_pow_le_jbDecay habs
    have hpow : (2 : ℝ) ^ 12 * ((2 : ℝ)⁻¹) ^ 12 = 1 := by
      rw [inv_pow]
      field_simp
    have h4 : 2 ^ 12 * (D + 1) * ((2 : ℝ)⁻¹) ^ 12 = D + 1 := by
      calc 2 ^ 12 * (D + 1) * ((2 : ℝ)⁻¹) ^ 12
          = (2 ^ 12 * ((2 : ℝ)⁻¹) ^ 12) * (D + 1) := by ring
        _ = D + 1 := by rw [hpow, one_mul]
    calc ‖φ t‖ ≤ D := h1.trans h0
      _ ≤ D + 1 := by linarith
      _ = 2 ^ 12 * (D + 1) * ((2 : ℝ)⁻¹) ^ 12 := h4.symm
      _ ≤ 2 ^ 12 * (D + 1) * jbDecay 12 t :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) (by linarith))

/-- The seminorm `seminorm ℝ k 0 ψ` is at most `schwartzSeminormSum ψ` for `k ∈ {0, 12}`. -/
lemma seminorm_le_schwartzSeminormSum_zero (ψ : SchwartzR) :
    SchwartzMap.seminorm ℝ 0 0 ψ ≤ schwartzSeminormSum ψ := by
  rw [schwartzSeminormSum]
  linarith [le_abs_self (SchwartzMap.seminorm ℝ 0 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 12 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ)),
    abs_nonneg (SchwartzMap.seminorm ℝ 12 0 (𝓕 ψ))]

lemma seminorm_le_schwartzSeminormSum_twelve (ψ : SchwartzR) :
    SchwartzMap.seminorm ℝ 12 0 ψ ≤ schwartzSeminormSum ψ := by
  rw [schwartzSeminormSum]
  linarith [le_abs_self (SchwartzMap.seminorm ℝ 12 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 0 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ)),
    abs_nonneg (SchwartzMap.seminorm ℝ 12 0 (𝓕 ψ))]

lemma seminorm_fourier_le_schwartzSeminormSum_zero (ψ : SchwartzR) :
    SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ) ≤ schwartzSeminormSum ψ := by
  rw [schwartzSeminormSum]
  linarith [le_abs_self (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ)),
    abs_nonneg (SchwartzMap.seminorm ℝ 0 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 12 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 12 0 (𝓕 ψ))]

lemma seminorm_fourier_le_schwartzSeminormSum_twelve (ψ : SchwartzR) :
    SchwartzMap.seminorm ℝ 12 0 (𝓕 ψ) ≤ schwartzSeminormSum ψ := by
  rw [schwartzSeminormSum]
  linarith [le_abs_self (SchwartzMap.seminorm ℝ 12 0 (𝓕 ψ)),
    abs_nonneg (SchwartzMap.seminorm ℝ 0 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 12 0 ψ),
    abs_nonneg (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ))]

/-- **Decay of `ψ` itself.** -/
theorem schwartz_decay (ψ : SchwartzR) (t : ℝ) :
    ‖ψ t‖ ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1) * jbDecay 12 t :=
  norm_apply_le_of_seminorm_le ψ (schwartzSeminormSum_nonneg ψ)
    (seminorm_le_schwartzSeminormSum_zero ψ) (seminorm_le_schwartzSeminormSum_twelve ψ) t

/-- **Decay of `𝓕ψ`.** -/
theorem schwartz_fourier_decay (ψ : SchwartzR) (t : ℝ) :
    ‖realFourier (ψ : ℝ → ℂ) t‖ ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1) * jbDecay 12 t := by
  rw [realFourier_coe]
  exact norm_apply_le_of_seminorm_le (𝓕 ψ) (schwartzSeminormSum_nonneg ψ)
    (seminorm_fourier_le_schwartzSeminormSum_zero ψ)
    (seminorm_fourier_le_schwartzSeminormSum_twelve ψ) t

/-- **The seminorm sum is at least `1`**: `𝓕ψ(0) = ∫ψ = 1`. -/
theorem one_le_schwartzSeminormSum (ψ : SchwartzR) (hψ : ∫ x, ψ x = 1) :
    1 ≤ schwartzSeminormSum ψ := by
  have hzero : (𝓕 ψ) 0 = ∫ x, ψ x := by
    rw [← realFourier_coe ψ 0, realFourier_zero]
  calc (1 : ℝ) = ‖(𝓕 ψ) 0‖ := by rw [hzero, hψ, norm_one]
    _ ≤ |SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ)| :=
        (SchwartzMap.norm_le_seminorm ℝ (𝓕 ψ) 0).trans (le_abs_self _)
    _ ≤ schwartzSeminormSum ψ := by
        rw [schwartzSeminormSum]
        linarith [abs_nonneg (SchwartzMap.seminorm ℝ 0 0 ψ),
          abs_nonneg (SchwartzMap.seminorm ℝ 12 0 ψ),
          abs_nonneg (SchwartzMap.seminorm ℝ 12 0 (𝓕 ψ))]

/-! ## The constant is large enough -/

/-- `2^84 ≤ 3^98`: the numerical comparison behind `2^60 C² ≤ calcConst ψ`. -/
theorem pow_two_84_le_pow_three_98 : (2 : ℝ) ^ 84 ≤ 3 ^ 98 :=
  (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (84 : ℕ) ≤ 98)).trans
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3) 98)

/-- `2^60 (2^12 (S+1))^2 ≤ (S+2)^100` for `S ≥ 1`. -/
theorem const_le_calcConst {S : ℝ} (hS : 1 ≤ S) :
    (2 : ℝ) ^ 60 * ((2 : ℝ) ^ 12 * (S + 1)) ^ 2 ≤ (S + 2) ^ 100 := by
  have h3 : (3 : ℝ) ≤ S + 2 := by linarith
  calc (2 : ℝ) ^ 60 * ((2 : ℝ) ^ 12 * (S + 1)) ^ 2
      = 2 ^ 84 * (S + 1) ^ 2 := by ring
    _ ≤ 3 ^ 98 * (S + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right pow_two_84_le_pow_three_98 (sq_nonneg _)
    _ ≤ 3 ^ 98 * (S + 2) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    _ ≤ (S + 2) ^ 98 * (S + 2) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) h3 98
    _ = (S + 2) ^ 100 := by rw [← pow_add]

/-! ## Lemma `calc` -/

/-- **Lemma `calc` (smooth approximation to `1_{[a,b]}`)** — Krause–Mirek–Tao, §6 (named
`calc_approx` because `calc` is a Lean keyword): for `ψ ∈ 𝓢(ℝ, ℂ)` with `∫ψ = 1`, every interval
`[a,b] ⊆ ℝ`, every `0 < ε ≤ 1` and every `x ∈ ℤ`,

`|∑_{y ∈ [a,b]∩ℤ} ε ψ(ε(x-y)) - 1_{[a,b]}(x)| ≤ calcConst ψ (ε^10 + ⟨ε(x-a)⟩^{-10} + ⟨ε(x-b)⟩^{-10})`,

where `calcConst ψ = (schwartzSeminormSum ψ + 2)^100` is an explicit constant depending only on
`ψ`.  Route: derive the decay hypotheses `‖ψ t‖ ≤ C jbDecay 12 t` and
`‖𝓕ψ t‖ ≤ C jbDecay 12 t` with `C = 2^12 (schwartzSeminormSum ψ + 1)` from the Schwartz
seminorms, apply `calc_of_decay` (constant `2^60 C^2`), and check `2^60 C^2 ≤ calcConst ψ`; the
latter uses `schwartzSeminormSum ψ ≥ 1`, which is forced by `𝓕ψ(0) = ∫ψ = 1`. -/
theorem calc_approx (ψ : SchwartzR) (hψ : ∫ x, ψ x = 1) (a b : ℝ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (x : ℤ) :
    ‖(∑ y ∈ Finset.Icc ⌈a⌉ ⌊b⌋, (ε : ℂ) * ψ (ε * ((x : ℝ) - y)))
        - (if a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b then (1 : ℂ) else 0)‖
      ≤ calcConst ψ * (ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a))
          + jbDecay 10 (ε * ((x : ℝ) - b))) := by
  have hS1 : (1 : ℝ) ≤ schwartzSeminormSum ψ := one_le_schwartzSeminormSum ψ hψ
  have hC1 : (1 : ℝ) ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1) := by
    have h2 : (1 : ℝ) ≤ 2 ^ 12 := by norm_num
    nlinarith [hS1, h2]
  have hdecay : ∀ t : ℝ,
      ‖(ψ : ℝ → ℂ) t‖ ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1) * jbDecay 12 t :=
    fun t => schwartz_decay ψ t
  have hFdecay : ∀ t : ℝ,
      ‖realFourier (ψ : ℝ → ℂ) t‖
        ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1) * jbDecay 12 t :=
    fun t => schwartz_fourier_decay ψ t
  have hmain := calc_of_decay (ψ : ℝ → ℂ) ψ.continuous ((2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1))
    hC1 hψ hdecay hFdecay a b hε0 hε1 x
  have hnn : 0 ≤ ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a)) + jbDecay 10 (ε * ((x : ℝ) - b)) := by
    have h1 := jbDecay_nonneg 10 (ε * ((x : ℝ) - a))
    have h2 := jbDecay_nonneg 10 (ε * ((x : ℝ) - b))
    positivity
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hnn)
  rw [calcConst]
  exact const_le_calcConst hS1

end Work.Analysis.InverseTheory
