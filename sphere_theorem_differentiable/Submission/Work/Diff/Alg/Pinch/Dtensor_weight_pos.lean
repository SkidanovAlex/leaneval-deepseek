import Mathlib
import Submission.Work.Diff.Alg.Pinch.DiagDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict positivity of the Böhm–Wilking pair weight (Böhm–Wilking Corollary 2.3)

With `a = ccA n b`, `p = ccP n b` the Böhm–Wilking parameters
(`ccA n b = (2b + (n-2)b²)/(2(1+(n-2)b²))`, `ccP n b = 1 - 1/(1+(n-2)b²))` and `mᵢ, mⱼ` the
eigenvalues of the traceless Ricci tensor of a diagonal-Ricci curvature tensor `S` (so that
`λᵢ = λ̄ + mᵢ`, `λ̄ = scal S / n`, and the pinching `Ric ≥ π·scal/n` reads
`(1-p) λ̄ + mᵢ ≥ 0`), the `(i,j)`-th Böhm–Wilking pair weight is

`Wt n b S i j = c₀ mᵢ mⱼ + 2a (λ̄+mᵢ)(λ̄+mⱼ) + b²(mᵢ²+mⱼ²) + bwC n b · ∑ₖ mₖ²`

with `c₀ = (n-2)b² - 2(a-b)`.  This file proves that `Wt n b S i j > 0` throughout the
Böhm–Wilking range `2 ≤ n`, `0 < b ≤ 1/2` — the eigenvalue computation in the first step of
Böhm–Wilking's proof of transversality (Corollary 2.3 / Lemma 3.4), in the form used by
Brendle–Schoen (Prop. 13).

## Proof

Everything rests on the two elementary consequences of the definitions (`Q := 1 + (n-2)b²`)

* `1 - p = 1/Q`, `p = (Q-1)/Q`, `2a Q = 2b + (n-2)b²`, hence `(1-p) c₀ = 2ap`:

  `(1-p)c₀ = (2b + (n-2)b² - 2a)/Q = (2aQ - 2a)/Q = 2a p`;

* consequently, with `Aᵢ := (1-p)λ̄ + mᵢ ≥ 0`,

  `(1-p)(c₀ mᵢ mⱼ + 2a(λ̄+mᵢ)(λ̄+mⱼ)) = 2a Aᵢ Aⱼ + 2ap(1-p)λ̄²`.

  (The difference of the two sides is `mᵢmⱼ((1-p)c₀ - 2ap)`.)

Multiplying `Wt` by `1 - p > 0` therefore leaves a sum of four nonnegative terms,
`2a AᵢAⱼ + 2ap(1-p)λ̄² + (1-p)b²(mᵢ²+mⱼ²) + (1-p) bwC · ∑mₖ²`, which is strictly positive:
if `mᵢ` and `mⱼ` do not both vanish, the `b²(mᵢ²+mⱼ²)` term is positive, and if they do, then
`2aAᵢAⱼ = 2a(1-p)²λ̄² > 0`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- The Böhm–Wilking parameter identity `(1 - p) c₀ = 2 a p` for `p = ccP n b`,
`a = ccA n b`, `c₀ = (n-2)b² - 2(a-b)`. -/
theorem one_sub_ccP_mul_coeff {n : ℕ} (hn2 : 2 ≤ n) (b : ℝ) :
    (1 - ccP n b) * (((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b))
      = 2 * ccA n b * ccP n b := by
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hb2 : (0 : ℝ) ≤ ((n : ℝ) - 2) * b ^ 2 := mul_nonneg (by linarith) (sq_nonneg b)
  have hQ : (1 : ℝ) + ((n : ℝ) - 2) * b ^ 2 ≠ 0 := by linarith
  have hQn : (1 : ℝ) - b ^ 2 * 2 + b ^ 2 * (n : ℝ) ≠ 0 := by linarith
  rw [ccP, ccA]
  field_simp
  ring

/-- The Böhm–Wilking pair weight is strictly positive in the range `2 ≤ n`, `0 < b ≤ 1/2`,
for eigenvalues satisfying the Ricci pinching `λᵢ = λ̄ + mᵢ ≥ p λ̄`. -/
theorem Dtensor_weight_pos (n : ℕ) (hn2 : 2 ≤ n) {b lbar Sterm mi mj : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1 / 2) (hlbar : 0 < lbar) (hSterm : 0 ≤ Sterm)
    (hi : 0 ≤ (1 - ccP n b) * lbar + mi) (hj : 0 ≤ (1 - ccP n b) * lbar + mj) :
    0 < (((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b)) * mi * mj
      + 2 * ccA n b * (lbar + mi) * (lbar + mj)
      + b ^ 2 * (mi ^ 2 + mj ^ 2)
      + bwC n b * Sterm := by
  have ha : 0 < ccA n b := ccA_pos (by omega) hb hb'
  have hp0 : 0 ≤ ccP n b := ccP_nonneg_diag hn2 b
  have hp1 : 0 < 1 - ccP n b := one_sub_ccP_pos hn2 hb hb'
  have hbw : 0 ≤ bwC n b := bwC_nonneg hn2 hb hb'
  have hc0 : (1 - ccP n b) * (((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b))
      = 2 * ccA n b * ccP n b := one_sub_ccP_mul_coeff hn2 b
  -- the expansion of `(1-p) * W`
  have hkey2 :
      (1 - ccP n b) * ((((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b)) * mi * mj)
        + (1 - ccP n b) * (2 * ccA n b * (lbar + mi) * (lbar + mj))
      = 2 * ccA n b * ((1 - ccP n b) * lbar + mi) * ((1 - ccP n b) * lbar + mj)
        + 2 * ccA n b * ccP n b * (1 - ccP n b) * lbar ^ 2 := by
    linear_combination (mi * mj) * hc0
  have hfull : (1 - ccP n b) *
        ((((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b)) * mi * mj
          + 2 * ccA n b * (lbar + mi) * (lbar + mj)
          + b ^ 2 * (mi ^ 2 + mj ^ 2) + bwC n b * Sterm)
      = 2 * ccA n b * ((1 - ccP n b) * lbar + mi) * ((1 - ccP n b) * lbar + mj)
        + 2 * ccA n b * ccP n b * (1 - ccP n b) * lbar ^ 2
        + (1 - ccP n b) * (b ^ 2 * (mi ^ 2 + mj ^ 2))
        + (1 - ccP n b) * (bwC n b * Sterm) := by
    rw [mul_add, mul_add, mul_add, hkey2]
  have hT1 : 0 ≤ 2 * ccA n b * ((1 - ccP n b) * lbar + mi) * ((1 - ccP n b) * lbar + mj) := by
    have h2a : (0 : ℝ) ≤ 2 * ccA n b := by linarith
    exact mul_nonneg (mul_nonneg h2a hi) hj
  have hT2 : 0 ≤ 2 * ccA n b * ccP n b * (1 - ccP n b) * lbar ^ 2 := by
    have h4 : (0 : ℝ) ≤ lbar ^ 2 := sq_nonneg lbar
    positivity
  have hT3 : 0 ≤ (1 - ccP n b) * (b ^ 2 * (mi ^ 2 + mj ^ 2)) :=
    mul_nonneg (le_of_lt hp1) (mul_nonneg (sq_nonneg b)
      (add_nonneg (sq_nonneg mi) (sq_nonneg mj)))
  have hT4 : 0 ≤ (1 - ccP n b) * (bwC n b * Sterm) :=
    mul_nonneg (le_of_lt hp1) (mul_nonneg hbw hSterm)
  have hpos : 0 < 2 * ccA n b * ((1 - ccP n b) * lbar + mi) * ((1 - ccP n b) * lbar + mj)
      + 2 * ccA n b * ccP n b * (1 - ccP n b) * lbar ^ 2
      + (1 - ccP n b) * (b ^ 2 * (mi ^ 2 + mj ^ 2))
      + (1 - ccP n b) * (bwC n b * Sterm) := by
    rcases eq_or_ne mi 0 with hmi | hmi
    · rcases eq_or_ne mj 0 with hmj | hmj
      · subst hmi; subst hmj
        have hAi : 0 < (1 - ccP n b) * lbar := mul_pos hp1 hlbar
        have h1 : 0 < 2 * ccA n b * ((1 - ccP n b) * lbar + 0) * ((1 - ccP n b) * lbar + 0) := by
          simpa using (mul_pos (mul_pos (mul_pos (by norm_num) ha) hAi) hAi :
            0 < 2 * ccA n b * ((1 - ccP n b) * lbar) * ((1 - ccP n b) * lbar))
        linarith [h1, hT1, hT2, hT3, hT4]
      · have h3 : 0 < (1 - ccP n b) * (b ^ 2 * (mi ^ 2 + mj ^ 2)) := by
          have hmj2 : 0 < mj ^ 2 := sq_pos_of_ne_zero hmj
          have hb2 : 0 < b ^ 2 := by positivity
          have h4 : 0 < b ^ 2 * (mi ^ 2 + mj ^ 2) := by nlinarith [mul_pos hb2 hmj2]
          exact mul_pos hp1 h4
        linarith [h3, hT1, hT2, hT4]
    · have h3 : 0 < (1 - ccP n b) * (b ^ 2 * (mi ^ 2 + mj ^ 2)) := by
        have hmi2 : 0 < mi ^ 2 := sq_pos_of_ne_zero hmi
        have hb2 : 0 < b ^ 2 := by positivity
        have h4 : 0 < b ^ 2 * (mi ^ 2 + mj ^ 2) := by nlinarith [mul_pos hb2 hmi2]
        exact mul_pos hp1 h4
      linarith [h3, hT1, hT2, hT4]
  have h1pW : 0 < (1 - ccP n b) *
      ((((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b)) * mi * mj
        + 2 * ccA n b * (lbar + mi) * (lbar + mj)
        + b ^ 2 * (mi ^ 2 + mj ^ 2)
        + bwC n b * Sterm) := by
    rw [hfull]
    exact hpos
  exact pos_of_mul_pos_right h1pW (le_of_lt hp1)

end Work.Diff.Alg.Pinch
