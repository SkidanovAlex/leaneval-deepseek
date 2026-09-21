import Mathlib
import Submission.Work.OddCurve.LowSlope.second_deriv_core

/-!
# The numeric second-derivative bound for the low-slope odd reconstruction

Let `k₁ = 2n+1`, `k₂ = 2n+2`, `a = R ^ k₂`, `b = r ^ k₂`, `u = R ^ k₁`, `v = r ^ k₁`, and

`τ₁ = |a + b - 2|`, `τ₂ = |u - v|`,  `s₁ = √(σ - τ₁)`, `s₂ = √(σ - τ₂)`.

The target statement asserts

`(1 + r·k₂/k₁)·R²/(a·(R+r)) + 2k₁(k₁s₁ + k₂rs₂)²R³/(k₂k₁²R^{2k₂}(R+r)²)
   + 2(k₁s₁ + k₂Rs₂)²/(k₂k₁²(Rr)^{k₁-1}(R+r)³) ≤ 4`

under the hypotheses `a, b ∈ [3/8, 15/8]`, `τ₁ ≤ σ`, `τ₂ ≤ σ`, `σ ≤ 1/2`.

The proof has three steps.

1. Each `sᵢ²` is at most `pᵢ/2`, where `p₁ = 1 - 2τ₁`, `p₂ = 1 - 2τ₂`, because `σ ≤ 1/2`.
2. The Cauchy–Schwarz inequality in the form `(x + y)² ≤ (α + β)(x²/α + y²/β)` turns the two
   squared terms into expressions linear in `p₁, p₂` (and it is exactly as strong as needed:
   it is an equality when `s₁ = s₂`).
3. The resulting explicit algebraic inequality is the statement of
   `Work.OddCurve.LowSlope.second_deriv_core`, proved in the sibling file
   `Submission/Work/OddCurve/LowSlope/second_deriv_core.lean`.
-/

namespace Work.OddCurve.LowSlope

/-- For `0 < σ` and `|E| ≤ σ`, `√(σ - |E|) ≤ √(1/2 - |E|)` when `σ ≤ 1/2`. -/
lemma sqrt_sub_abs_le_half {σ E : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2) (hE : |E| ≤ σ) :
    Real.sqrt (σ - |E|) ≤ Real.sqrt (1 / 2 - |E|) :=
  Real.sqrt_le_sqrt (by linarith)

/-- Cauchy–Schwarz in the "Titu" form: `(x + y)^2 ≤ (α + β)(x^2/α + y^2/β)` for `α, β > 0`. -/
lemma sq_add_le_mul_div (x y α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (x + y) ^ 2 ≤ (α + β) * (x ^ 2 / α + y ^ 2 / β) := by
  have hxy : (0 : ℝ) < α * β := by positivity
  have key : (α + β) * (x ^ 2 / α + y ^ 2 / β) - (x + y) ^ 2
      = (x * β - y * α) ^ 2 / (α * β) := by
    field_simp
    ring
  have hnn : 0 ≤ (x * β - y * α) ^ 2 / (α * β) := div_nonneg (sq_nonneg _) hxy.le
  linarith [key ▸ hnn]

/-- The weighted Cauchy–Schwarz inequality: `(a s₁ + b s₂)² ≤ (a + b)(a s₁² + b s₂²)`. -/
lemma weighted_sq (s1 s2 a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a * s1 + b * s2) ^ 2 ≤ (a + b) * (a * s1 ^ 2 + b * s2 ^ 2) := by
  have h := sq_add_le_mul_div (a * s1) (b * s2) a b ha hb
  have e1 : (a * s1) ^ 2 / a = a * s1 ^ 2 := by field_simp
  have e2 : (b * s2) ^ 2 / b = b * s2 ^ 2 := by field_simp
  rwa [e1, e2] at h

/-- Monotonicity of the square of a weighted sum of two nonnegative numbers. -/
lemma sq_weighted_mono {a a' b b' c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (ha' : a ≤ a') (hb : 0 ≤ b) (hb' : b ≤ b') :
    (c * a + d * b) ^ 2 ≤ (c * a' + d * b') ^ 2 := by
  have h2 : c * a + d * b ≤ c * a' + d * b' := by
    have h3 : c * a ≤ c * a' := mul_le_mul_of_nonneg_left ha' hc
    have h4 : d * b ≤ d * b' := mul_le_mul_of_nonneg_left hb' hd
    linarith
  exact pow_le_pow_left₀ (by positivity) h2 2

/-- `R ^ (4n+4) = R ^ 3 * R ^ (4n+1)`. -/
lemma pow_fourn_four (n : ℕ) (R : ℝ) : R ^ (4 * n + 4) = R ^ 3 * R ^ (4 * n + 1) := by
  rw [← pow_add]; congr 1; omega

/-- The second term of the target, with its `R ^ 3 / R ^ (4n+4)` rewritten as `1 / R ^ (4n+1)`. -/
lemma term2_rewrite (n : ℕ) {R r X k1 k2 : ℝ} (hR : R ≠ 0) (hRr : R + r ≠ 0)
    (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) :
    2 * k1 * X ^ 2 * R ^ 3 / (k2 * k1 ^ 2 * R ^ (4 * n + 4) * (R + r) ^ 2)
      = 2 * X ^ 2 / (k2 * k1 * R ^ (4 * n + 1) * (R + r) ^ 2) := by
  rw [pow_fourn_four n R]
  have hRp : R ^ (4 * n + 1) ≠ 0 := pow_ne_zero _ hR
  have hk1' : k1 ^ 2 ≠ 0 := pow_ne_zero _ hk1
  have hRr2 : (R + r) ^ 2 ≠ 0 := pow_ne_zero _ hRr
  have hR3 : R ^ 3 ≠ 0 := pow_ne_zero _ hR
  field_simp

/-- The key inequality for one of the two squared terms: if `s₁² ≤ p/2` and `s₂² ≤ q/2`, then
`2(k₁s₁ + k₂xs₂)² ≤ (k₁ + k₂x)(k₁p + k₂xq)`.  This is Cauchy–Schwarz followed by the two
elementary bounds. -/
lemma key_ineq {s1 s2 p q k1 k2 x : ℝ} (hk1 : 0 < k1) (hkx : 0 < k2 * x)
    (h1 : s1 ^ 2 ≤ p / 2) (h2 : s2 ^ 2 ≤ q / 2) :
    2 * (k1 * s1 + k2 * x * s2) ^ 2 ≤ (k1 + k2 * x) * (k1 * p + k2 * x * q) := by
  have ht := weighted_sq s1 s2 k1 (k2 * x) hk1 hkx
  have hw : k1 * s1 ^ 2 + (k2 * x) * s2 ^ 2 ≤ (k1 * p + (k2 * x) * q) / 2 := by
    nlinarith [h1, h2, hk1, hkx]
  nlinarith [ht, hw, hk1, hkx]

/-- Generic version of the second term comparison. -/
lemma term2_generic {n : ℕ} {R r X Y k1 k2 : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hk1 : 0 < k1) (hk2 : 0 < k2) (hkey : 2 * X ^ 2 ≤ (k1 + k2 * r) * Y) :
    2 * k1 * X ^ 2 * R ^ 3 / (k2 * k1 ^ 2 * R ^ (4 * n + 4) * (R + r) ^ 2)
      ≤ (k1 + k2 * r) * Y / (k2 * k1 * R ^ (4 * n + 1) * (R + r) ^ 2) := by
  rw [term2_rewrite n (ne_of_gt hR) (by positivity) (ne_of_gt hk1) (ne_of_gt hk2)]
  exact div_le_div_of_nonneg_right hkey (by positivity)

/-- Generic version of the third term comparison. -/
lemma term3_generic {n : ℕ} {R r X Y k1 k2 : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hk1 : 0 < k1) (hk2 : 0 < k2) (hkey : 2 * X ^ 2 ≤ (k1 + k2 * R) * Y) :
    2 * X ^ 2 / (k2 * k1 ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3)
      ≤ (k1 + k2 * R) * Y / (k2 * k1 ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3) :=
  div_le_div_of_nonneg_right hkey (by positivity)

set_option maxHeartbeats 2000000 in
/-- The numeric second-derivative bound. -/
theorem second_deriv_numeric (n : ℕ) (hn : 1 ≤ n) {σ R r : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2)
    (hR : 0 < R) (hr : 0 < r)
    (ha1 : 3 / 8 ≤ R ^ (2 * n + 2)) (ha2 : R ^ (2 * n + 2) ≤ 15 / 8)
    (hb1 : 3 / 8 ≤ r ^ (2 * n + 2)) (hb2 : r ^ (2 * n + 2) ≤ 15 / 8)
    (hm : |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| ≤ σ)
    (hv : |R ^ (2 * n + 1) - r ^ (2 * n + 1)| ≤ σ) :
    (1 + r * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R ^ 2 / (R ^ (2 * n + 2) * (R + r))
      + 2 * ((2 * n + 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
            + ((2 * n + 2 : ℕ) : ℝ) * r * Real.sqrt (σ - |R ^ (2 * n + 1) - r ^ (2 * n + 1)|)) ^ 2
          * R ^ 3 /
          (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R ^ (4 * n + 4) * (R + r) ^ 2)
      + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
            + ((2 * n + 2 : ℕ) : ℝ) * R * Real.sqrt (σ - |R ^ (2 * n + 1) - r ^ (2 * n + 1)|)) ^ 2
          / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3)
      ≤ 4 := by
  set S1 : ℝ := Real.sqrt (σ - |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|) with hS1
  set S2 : ℝ := Real.sqrt (σ - |R ^ (2 * n + 1) - r ^ (2 * n + 1)|) with hS2
  have hEabs : |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| ≤ 1 / 2 := by linarith [hm, hσ']
  have hFabs : |R ^ (2 * n + 1) - r ^ (2 * n + 1)| ≤ 1 / 2 := by linarith [hv, hσ']
  have hS1le : S1 ^ 2 ≤ (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|) / 2 := by
    have h : S1 ^ 2 = σ - |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| := by
      rw [hS1]; exact Real.sq_sqrt (sub_nonneg.mpr (by linarith [hm]))
    rw [h]; linarith
  have hS2le : S2 ^ 2 ≤ (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|) / 2 := by
    have h : S2 ^ 2 = σ - |R ^ (2 * n + 1) - r ^ (2 * n + 1)| := by
      rw [hS2]; exact Real.sq_sqrt (sub_nonneg.mpr (by linarith [hv]))
    rw [h]; linarith
  have hk1 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hk2 : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := by positivity
  have hBkey := key_ineq (s1 := S1) (s2 := S2)
    (p := 1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
    (q := 1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|)
    (k1 := ((2 * n + 1 : ℕ) : ℝ)) (k2 := ((2 * n + 2 : ℕ) : ℝ)) (x := r) hk1 (mul_pos hk2 hr)
    hS1le hS2le
  have hCkey := key_ineq (s1 := S1) (s2 := S2)
    (p := 1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
    (q := 1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|)
    (k1 := ((2 * n + 1 : ℕ) : ℝ)) (k2 := ((2 * n + 2 : ℕ) : ℝ)) (x := R) hk1 (mul_pos hk2 hR)
    hS1le hS2le
  have h2 := term2_generic (n := n) (R := R) (r := r)
    (X := ((2 * n + 1 : ℕ) : ℝ) * S1 + ((2 * n + 2 : ℕ) : ℝ) * r * S2)
    (Y := ((2 * n + 1 : ℕ) : ℝ) * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
      + ((2 * n + 2 : ℕ) : ℝ) * r * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|))
    hR hr hk1 hk2 hBkey
  have h3 := term3_generic (n := n) (R := R) (r := r)
    (X := ((2 * n + 1 : ℕ) : ℝ) * S1 + ((2 * n + 2 : ℕ) : ℝ) * R * S2)
    (Y := ((2 * n + 1 : ℕ) : ℝ) * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
      + ((2 * n + 2 : ℕ) : ℝ) * R * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|))
    hR hr hk1 hk2 hCkey
  have hcore : (1 + r * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R ^ 2
          / (R ^ (2 * n + 2) * (R + r))
        + (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r)
            * (((2 * n + 1 : ℕ) : ℝ) * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
              + ((2 * n + 2 : ℕ) : ℝ) * r * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|))
          / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R ^ (4 * n + 1) * (R + r) ^ 2)
        + (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * R)
            * (((2 * n + 1 : ℕ) : ℝ) * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
              + ((2 * n + 2 : ℕ) : ℝ) * R * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|))
          / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3)
      ≤ 4 :=
    second_deriv_core n hn hR hr ha1 ha2 hb1 hb2 hEabs hFabs
  linarith [h2, h3, hcore]

end Work.OddCurve.LowSlope
