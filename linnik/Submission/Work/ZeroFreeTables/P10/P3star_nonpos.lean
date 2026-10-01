/-
# ZeroFreeTables — P10/P3star_nonpos

The residual step of the `P₃` engine of HB §10, i.e. "the analysis leading to
Lemma 8.3": under the side condition `a⁻³ ≤ (a+λ₁)⁻³ + (a+λ₂)⁻³ + (a+λ₃)⁻³`
with `0 ≤ λ₁ ≤ λ₂ ≤ λ₃` and `a > 0`, the signed combination

  `Re[ P₃(α/(a+it)) − P₃(α/((a+λ₁)+it)) − P₃(α/((a+λ₂)+it)) − P₃(α/((a+λ₃)+it)) ] ≤ 0`,
  `α = a + λ₁`,

of HB's polynomial `P₃(X) = X + X² + (2/3)X³`.

## Why it is true

`P3Pos.lean` records the identity `(P₃ w).re = (8/3)(Re w)³ + (1 + 2 Re w)(Re w − |w|²)`
(HB (4.11) sharp).  At `w = B/(A+it)` (`A,B > 0`) one has
`Re w = Bᴀ/(A²+t²) ≥ 0` and `Re w − |w|² = B(A−B)/(A²+t²)`, so the second
factor of the identity has exactly the *sign of `A − B`*:

* for `A ≥ B` (the three points `A = a+λ_j`, `j ≥ 1`) one gets
  `(P₃ w).re ≥ (8/3)(B A/(A²+t²))³`;
* for `A = a ≤ B` (the point `λ₀ = 0`) one gets `(P₃ w).re ≤ (8/3)(B a/(a²+t²))³`.

Subtracting, only the "boundary" values `(8/3)(B A_j/(A_j²+t²))³` survive, and
after factoring `(8/3)B³` the inequality to prove becomes
`(a/(a²+t²))³ ≤ Σ_j (A_j/(A_j²+t²))³`.  Now

  `(A_j/(A_j²+t²))³ = (1/A_j³)·(A_j²/(A_j²+t²))³ ≥ (1/A_j³)·(a²/(a²+t²))³`

because `A_j ≥ a` makes `A ↦ A²/(A²+t²)` increasing, and summing gives
`(a²/(a²+t²))³·Σ_j A_j⁻³ ≥ (a²/(a²+t²))³·a⁻³ = (a/(a²+t²))³`
by the side condition.  This is exactly the "isoperimetric" content of the
statement: the `t`-dependence is entirely harmless, since the same monotonicity
`(1+t²/A²)^{-3} ≥ (1+t²/a²)^{-3}` holds for every `A ≥ a`.

The development below is the formalisation of that argument: the pointwise
evaluation of `Re P₃` (`P3_re_at`) with its two sign consequences
(`P3_re_le`, `P3_re_ge`), and the weight comparison (`weight_one`, `weight_sum`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P3Pos

open Complex

namespace Work.ZeroFreeTables.P10

/-! ## 1. `Re P₃` at the points `B/(A+it)` -/

/-- The value of `Re P₃` at `B/(A+it)`, `A > 0`: `P3_re_eq` with the explicit
`Re w = B A/(A²+t²)` and `normSq w = B²/(A²+t²)`.  The second summand carries the
sign of `A - B`. -/
lemma P3_re_at (A B t : ℝ) (hA : 0 < A) :
    (Work.ZeroFreeTables.P3 (B / ((A : ℂ) + (t : ℂ) * Complex.I))).re
      = (8/3) * (B * A / (A ^ 2 + t ^ 2)) ^ 3
        + (1 + 2 * (B * A / (A ^ 2 + t ^ 2))) * (B * (A - B) / (A ^ 2 + t ^ 2)) := by
  rw [Work.ZeroFreeTables.P3_re_eq]
  have hre : (B / ((A : ℂ) + (t : ℂ) * Complex.I)).re = B * A / (A ^ 2 + t ^ 2) := by
    rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.normSq_add_mul_I]
    simp
    ring
  have hns : Complex.normSq (B / ((A : ℂ) + (t : ℂ) * Complex.I)) = B ^ 2 / (A ^ 2 + t ^ 2) := by
    rw [div_eq_mul_inv, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_add_mul_I]
    simp
    ring
  rw [hre, hns]
  have hD : (0 : ℝ) < A ^ 2 + t ^ 2 := by positivity
  field_simp

/-- For `A ≤ B` (the point `λ₀ = 0`) the value of `Re P₃` at `B/(A+it)` is at most
its "leading" term `(8/3)(B A/(A²+t²))³`. -/
lemma P3_re_le (A B t : ℝ) (hA : 0 < A) (hB : 0 < B) (h : A ≤ B) :
    (Work.ZeroFreeTables.P3 (B / ((A : ℂ) + (t : ℂ) * Complex.I))).re
      ≤ (8/3) * (B * A / (A ^ 2 + t ^ 2)) ^ 3 := by
  rw [P3_re_at A B t hA]
  have hD : (0 : ℝ) < A ^ 2 + t ^ 2 := by positivity
  have hx : 0 ≤ B * A / (A ^ 2 + t ^ 2) := by positivity
  have h1 : 0 ≤ 1 + 2 * (B * A / (A ^ 2 + t ^ 2)) := by linarith
  have h2 : B * (A - B) / (A ^ 2 + t ^ 2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hD)
    nlinarith
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 h2]

/-- For `A ≥ B` (the points `λ_j`, `j ≥ 1`) the value of `Re P₃` at `B/(A+it)` is at
least its "leading" term `(8/3)(B A/(A²+t²))³`. -/
lemma P3_re_ge (A B t : ℝ) (hA : 0 < A) (hB : 0 < B) (h : B ≤ A) :
    (8/3) * (B * A / (A ^ 2 + t ^ 2)) ^ 3
      ≤ (Work.ZeroFreeTables.P3 (B / ((A : ℂ) + (t : ℂ) * Complex.I))).re := by
  rw [P3_re_at A B t hA]
  have hD : (0 : ℝ) < A ^ 2 + t ^ 2 := by positivity
  have hx : 0 ≤ B * A / (A ^ 2 + t ^ 2) := by positivity
  have h1 : 0 ≤ 1 + 2 * (B * A / (A ^ 2 + t ^ 2)) := by linarith
  have h2 : 0 ≤ B * (A - B) / (A ^ 2 + t ^ 2) := by
    apply div_nonneg _ (le_of_lt hD)
    nlinarith
  nlinarith [mul_nonneg h1 h2]

/-! ## 2. The weight comparison -/

/-- One-term weight comparison: for `A ≥ a > 0`,
`(A/(A²+t²))³ ≥ (1/A³)(a²/(a²+t²))³`, i.e.
`(A²/(A²+t²))³ ≥ (a²/(a²+t²))³` (multiplied by `A³ > 0`), the monotonicity of
`A ↦ A²/(A²+t²)`. -/
lemma weight_one (a A t : ℝ) (ha : 0 < a) (hA : a ≤ A) :
    (1/A^3) * (a^2/(a^2+t^2))^3 ≤ (A/(A^2+t^2))^3 := by
  have hApos : 0 < A := lt_of_lt_of_le ha hA
  have hD0 : (0 : ℝ) < a^2+t^2 := by positivity
  have hD1 : (0 : ℝ) < A^2+t^2 := by positivity
  have hsq : a^2 ≤ A^2 := by nlinarith
  have hq : a^2/(a^2+t^2) ≤ A^2/(A^2+t^2) := by
    rw [div_le_div_iff₀ hD0 hD1]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg t)]
  have hqq : (a^2/(a^2+t^2))^3 ≤ (A^2/(A^2+t^2))^3 := pow_le_pow_left₀ (by positivity) hq 3
  have hsplit : (A/(A^2+t^2))^3 = (1/A^3) * (A^2/(A^2+t^2))^3 := by field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hqq (by positivity)

/-- **The weight inequality.**  For `a > 0`, `A_j ≥ a` and `a⁻³ ≤ Σ_j A_j⁻³`,

`(a/(a²+t²))³ ≤ Σ_j (A_j/(A_j²+t²))³`

— this is where the side condition is consumed. -/
lemma weight_sum (a t A₁ A₂ A₃ : ℝ) (ha : 0 < a) (h1 : a ≤ A₁) (h2 : a ≤ A₂) (h3 : a ≤ A₃)
    (h : 1/a^3 ≤ 1/A₁^3 + 1/A₂^3 + 1/A₃^3) :
    (a/(a^2+t^2))^3 ≤ (A₁/(A₁^2+t^2))^3 + (A₂/(A₂^2+t^2))^3 + (A₃/(A₃^2+t^2))^3 := by
  have w1 := weight_one a A₁ t ha h1
  have w2 := weight_one a A₂ t ha h2
  have w3 := weight_one a A₃ t ha h3
  have hpos : (0 : ℝ) ≤ (a^2/(a^2+t^2))^3 := by positivity
  have hh := mul_le_mul_of_nonneg_left h hpos
  have e1 : (a/(a^2+t^2))^3 = (a^2/(a^2+t^2))^3 * (1/a^3) := by field_simp
  have e2 : (1/A₁^3)*(a^2/(a^2+t^2))^3 + (1/A₂^3)*(a^2/(a^2+t^2))^3 + (1/A₃^3)*(a^2/(a^2+t^2))^3
      = (a^2/(a^2+t^2))^3 * (1/A₁^3 + 1/A₂^3 + 1/A₃^3) := by ring
  linarith

/-! ## 3. The residual step -/

/-- **The residual step of HB §10** ("the analysis leading to Lemma 8.3"): with
`α = a + λ₁` and `0 ≤ λ₁ ≤ λ₂ ≤ λ₃`, the side condition `a⁻³ ≤ Σ_j (a+λ_j)⁻³`
makes the signed `P₃`-combination non-positive. -/
theorem P3star_nonpos {a lam₁ lam₂ lam₃ t : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (h₂₁ : lam₁ ≤ lam₂) (h₃₂ : lam₂ ≤ lam₃)
    (hcond : 1 / a ^ 3 ≤ 1 / (a + lam₁) ^ 3 + 1 / (a + lam₂) ^ 3 + 1 / (a + lam₃) ^ 3) :
    (Work.ZeroFreeTables.P3 ((a + lam₁) / ((a : ℂ) + (t : ℂ) * Complex.I))
      - Work.ZeroFreeTables.P3 ((a + lam₁) / ((a + lam₁ : ℝ) + (t : ℂ) * Complex.I))
      - Work.ZeroFreeTables.P3 ((a + lam₁) / ((a + lam₂ : ℝ) + (t : ℂ) * Complex.I))
      - Work.ZeroFreeTables.P3 ((a + lam₁) / ((a + lam₃ : ℝ) + (t : ℂ) * Complex.I))).re ≤ 0 := by
  have hB : (0 : ℝ) < a + lam₁ := by linarith
  have hA2 : (0 : ℝ) < a + lam₂ := by linarith
  have hA3 : (0 : ℝ) < a + lam₃ := by linarith
  -- the pointwise bounds
  have b0 := P3_re_le a (a + lam₁) t ha hB (by linarith)
  have b1 := P3_re_ge (a + lam₁) (a + lam₁) t hB hB le_rfl
  have b2 := P3_re_ge (a + lam₂) (a + lam₁) t hA2 hB (by linarith)
  have b3 := P3_re_ge (a + lam₃) (a + lam₁) t hA3 hB (by linarith)
  -- the weight comparison, multiplied by the positive factor `(8/3)(a+λ₁)³`
  have hw := weight_sum a t (a + lam₁) (a + lam₂) (a + lam₃) ha
    (by linarith) (by linarith) (by linarith) hcond
  have hw3 := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ (8/3) * (a + lam₁) ^ 3)
  have key0 : (8/3) * (a + lam₁) ^ 3 * (a / (a ^ 2 + t ^ 2)) ^ 3
      = (8/3) * ((a + lam₁) * a / (a ^ 2 + t ^ 2)) ^ 3 := by ring
  have key1 : (8/3) * (a + lam₁) ^ 3 * ((a + lam₁) / ((a + lam₁) ^ 2 + t ^ 2)) ^ 3
      = (8/3) * ((a + lam₁) * (a + lam₁) / ((a + lam₁) ^ 2 + t ^ 2)) ^ 3 := by ring
  have key2 : (8/3) * (a + lam₁) ^ 3 * ((a + lam₂) / ((a + lam₂) ^ 2 + t ^ 2)) ^ 3
      = (8/3) * ((a + lam₁) * (a + lam₂) / ((a + lam₂) ^ 2 + t ^ 2)) ^ 3 := by ring
  have key3 : (8/3) * (a + lam₁) ^ 3 * ((a + lam₃) / ((a + lam₃) ^ 2 + t ^ 2)) ^ 3
      = (8/3) * ((a + lam₁) * (a + lam₃) / ((a + lam₃) ^ 2 + t ^ 2)) ^ 3 := by ring
  push_cast at *
  simp only [Complex.sub_re] at *
  linarith

end Work.ZeroFreeTables.P10
