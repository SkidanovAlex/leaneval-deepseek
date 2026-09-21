import Mathlib

set_option maxHeartbeats 800000

/-!
# Bounds on the first two radial coefficients (`radial_core`)

Given `u ∈ [0, 1/√2]`, `S = √(1-u²)`, `R ∈ [1-1/1000, 1+1/1000]`, `x₀ = R u` and
`b₁, b₂` the approximate values `-x₀/√(1-x₀²)`, `-1/(√(1-x₀²))³` (up to `1/1000`),
the solution `(p,q)` of the linearised radial system

  `p (S² - b₁ u S) = R (u + b₁ S)`,
  `q (S - b₁ u) = b₂ (p u + R)² + 2 b₁ p + 2 p u / S + R / S³`

satisfies `|p| ≤ 3` and `|q| ≤ 30`.  The actual bounds are far smaller (`|p| ≲ 0.003`,
`|q| ≲ 0.01`); the point is that the *cancellation* in the first equation forces `p` to be
tiny, which is what makes the second equation's right-hand side bounded.

All constants below are deliberately crude; the only sharp ingredient is the identity

  `u - x₀ S/A = u (1 - R²) / (A (A + R S))`   with `A = √(1-x₀²)`,

which exhibits the cancellation and uses `A² - R²S² = 1 - R²`.
-/

namespace Work.OddCurve.LowSlope

theorem radial_core {u R S x₀ b₁ b₂ p q : ℝ}
    (hu0 : 0 ≤ u) (hu2 : u ^ 2 ≤ 1 / 2)
    (hRpos : 0 < R) (hR1 : |R - 1| ≤ 1 / 1000)
    (hS : S ^ 2 = 1 - u ^ 2) (hSpos : 0 < S)
    (hx₀ : x₀ = R * u)
    (hb₁ : |b₁ + x₀ / Real.sqrt (1 - x₀ ^ 2)| ≤ 1 / 1000)
    (hb₂ : |b₂ + 1 / (Real.sqrt (1 - x₀ ^ 2)) ^ 3| ≤ 1 / 1000)
    (hlin : p * (S ^ 2 - b₁ * u * S) = R * (u + b₁ * S))
    (hquad : q * (S - b₁ * u) =
      b₂ * (p * u + R) ^ 2 + 2 * b₁ * p + 2 * p * u / S + R / S ^ 3) :
    |p| ≤ 3 ∧ |q| ≤ 30 := by
  -- ## Step 0: numerical bounds on `R`, `u`, `S`, `x₀`
  have hRlo : (999 : ℝ) / 1000 ≤ R := by
    have h := (abs_le.mp hR1).1; linarith
  have hRhi : R ≤ (1001 : ℝ) / 1000 := by
    have h := (abs_le.mp hR1).2; linarith
  have hu1 : u ≤ 1 := by nlinarith [sq_nonneg (u - 1), hu2]
  have hS2ge : (1 : ℝ) / 2 ≤ S ^ 2 := by rw [hS]; linarith
  have hS2le : S ^ 2 ≤ 1 := by rw [hS]; nlinarith [sq_nonneg u]
  have hSge : (7 : ℝ) / 10 ≤ S := by nlinarith [sq_nonneg (S - 7 / 10), hS2ge]
  have hSle : S ≤ 1 := by nlinarith [sq_nonneg (S - 1), hS2le]
  have huS : u ≤ S := by
    have h : u ^ 2 ≤ S ^ 2 := by rw [hS]; linarith
    nlinarith [h, hu0, hSpos.le, sq_nonneg (u - S)]
  have hx₀nn : 0 ≤ x₀ := by rw [hx₀]; positivity
  have hx₀sq : x₀ ^ 2 = R ^ 2 * u ^ 2 := by rw [hx₀]; ring
  have hx₀2le : x₀ ^ 2 ≤ (51 : ℝ) / 100 := by rw [hx₀sq]; nlinarith [hu2, hRlo, hRhi]
  have hx₀le : x₀ ≤ (709 : ℝ) / 1000 := by rw [hx₀]; nlinarith [hu2, hRhi, hu0]
  -- ## Step 1: `A = √(1-x₀²) ∈ [7/10, 1]`
  set A : ℝ := Real.sqrt (1 - x₀ ^ 2) with hAdef
  have h1mx₀ : (0 : ℝ) ≤ 1 - x₀ ^ 2 := by linarith
  have hA2 : A ^ 2 = 1 - x₀ ^ 2 := by rw [hAdef]; exact Real.sq_sqrt h1mx₀
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Real.sqrt_nonneg _
  have hAge : (7 : ℝ) / 10 ≤ A := by nlinarith [hA2, hA0, hx₀2le, sq_nonneg (A - 7 / 10)]
  have hApos : 0 < A := by linarith
  -- ## Step 2: bounds on `b₁`, `b₂`
  have hb₁' : |b₁ + x₀ / A| ≤ 1 / 1000 := hb₁
  have hx0A_le : x₀ / A ≤ 3 / 2 := by
    rw [div_le_iff₀ hApos]; linarith [hx₀le, hAge]
  have hx0A_nn : 0 ≤ x₀ / A := by positivity
  have hb₁le : b₁ ≤ 1 / 1000 := by
    have h := (abs_le.mp hb₁').2; linarith
  have hb₁abs : |b₁| ≤ 2 := by
    have h := abs_le.mp hb₁'
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hb₂' : |b₂ + 1 / A ^ 3| ≤ 1 / 1000 := hb₂
  have hA3 : (343 : ℝ) / 1000 ≤ A ^ 3 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 7 / 10 by norm_num) hAge 3
    norm_num at h
    exact h
  have hb₂abs : |b₂| ≤ 3 := by
    have hinv : 1 / A ^ 3 ≤ 1000 / 343 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hA3]
    have h1A3 : 0 < 1 / A ^ 3 := by positivity
    have habs : |b₂| ≤ 1 / A ^ 3 + 1 / 1000 := by
      have h := abs_le.mp hb₂'
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    linarith
  -- ## Step 3: the cancellation identity
  have hRS : ((999 : ℝ) / 1000) * (7 / 10) ≤ R * S :=
    mul_le_mul hRlo hSge (by norm_num) hRpos.le
  have hARS : (1399 : ℝ) / 1000 ≤ A + R * S := by linarith
  have hAden : 0 < A * (A + R * S) := mul_pos hApos (by linarith)
  have hker : u - x₀ * S / A = u * (1 - R ^ 2) / (A * (A + R * S)) := by
    rw [eq_div_iff (ne_of_gt hAden)]
    have key : (u - x₀ * S / A) * (A * (A + R * S)) = u * (1 - R ^ 2) := by
      have hAne : A ≠ 0 := ne_of_gt hApos
      field_simp
      ring_nf
      rw [hA2, hx₀, hS]
      ring
    exact key
  have hkerabs : |u - x₀ * S / A| ≤ 1 / 400 := by
    rw [hker, abs_div, abs_of_pos hAden, div_le_iff₀ hAden]
    have ha1 : |u| ≤ 1 := abs_le.mpr ⟨by linarith, hu1⟩
    have ha2 : |1 - R ^ 2| ≤ (2001 : ℝ) / 1000000 := by
      rw [abs_le]; constructor <;> nlinarith [hRlo, hRhi]
    have h1 : |u * (1 - R ^ 2)| ≤ (2001 : ℝ) / 1000000 := by
      rw [abs_mul]
      have hmm : |u| * |1 - R ^ 2| ≤ 1 * ((2001 : ℝ) / 1000000) :=
        mul_le_mul ha1 ha2 (abs_nonneg _) (by norm_num)
      linarith
    have h2 : (2001 : ℝ) / 1000000 ≤ (1 / 400) * (A * (A + R * S)) := by
      nlinarith [hAge, hARS, hApos]
    linarith
  -- ## Step 4: `|u + b₁ S|` is tiny
  have hbu : |u + b₁ * S| ≤ 7 / 2000 := by
    have hsplit : u + b₁ * S = (u - x₀ * S / A) + S * (b₁ + x₀ / A) := by
      have hAne : A ≠ 0 := ne_of_gt hApos
      field_simp
      ring
    rw [hsplit]
    have hS1 : |S| ≤ 1 := abs_le.mpr ⟨by linarith, hSle⟩
    have h2 : |S| * |b₁ + x₀ / A| ≤ 1 * (1 / 1000) :=
      mul_le_mul hS1 hb₁' (abs_nonneg _) (by norm_num)
    calc |(u - x₀ * S / A) + S * (b₁ + x₀ / A)|
        ≤ |u - x₀ * S / A| + |S * (b₁ + x₀ / A)| := abs_add_le _ _
      _ = |u - x₀ * S / A| + |S| * |b₁ + x₀ / A| := by rw [abs_mul]
      _ ≤ 1 / 400 + 1 * (1 / 1000) := by linarith
      _ = 7 / 2000 := by norm_num
  -- ## Step 5: solve the linear equation for `p`
  have hD1 : (999 : ℝ) / 2000 ≤ S ^ 2 - b₁ * u * S := by
    have h2 : u * S ≤ S * S := mul_le_mul_of_nonneg_right huS hSpos.le
    have h1 : b₁ * (u * S) ≤ (1 / 1000 : ℝ) * (S * S) :=
      mul_le_mul hb₁le h2 (mul_nonneg hu0 hSpos.le) (by norm_num)
    nlinarith only [h1, hS2ge]
  have hD1pos : 0 < S ^ 2 - b₁ * u * S := by linarith only [hD1]
  have hEq : |p| * (S ^ 2 - b₁ * u * S) = R * |u + b₁ * S| := by
    have h := congrArg abs hlin
    rw [abs_mul, abs_of_pos hD1pos, abs_mul, abs_of_pos hRpos] at h
    exact h
  have hp : |p| ≤ 1 / 100 := by
    have h1 : |p| * ((999 : ℝ) / 2000) ≤ |p| * (S ^ 2 - b₁ * u * S) :=
      mul_le_mul_of_nonneg_left hD1 (abs_nonneg p)
    have h2 : R * |u + b₁ * S| ≤ ((1001 : ℝ) / 1000) * (7 / 2000) :=
      mul_le_mul hRhi hbu (abs_nonneg _) (by norm_num)
    have h3 : |p| * ((999 : ℝ) / 2000) ≤ 7007 / 2000000 := by linarith only [h1, h2, hEq]
    nlinarith only [h3]
  -- ## Step 6: the quadratic equation
  have hD2 : (69 : ℝ) / 100 ≤ S - b₁ * u := by
    have h1 : b₁ * u ≤ (1 / 1000 : ℝ) * S := by
      calc b₁ * u ≤ (1 / 1000 : ℝ) * u := mul_le_mul_of_nonneg_right hb₁le hu0
        _ ≤ (1 / 1000 : ℝ) * S := mul_le_mul_of_nonneg_left huS (by norm_num)
    linarith only [h1, hSge]
  have hD2pos : 0 < S - b₁ * u := by linarith only [hD2]
  have hEq2 : |q| * (S - b₁ * u) =
      |b₂ * (p * u + R) ^ 2 + 2 * b₁ * p + 2 * p * u / S + R / S ^ 3| := by
    have h := congrArg abs hquad
    rw [abs_mul, abs_of_pos hD2pos] at h
    exact h
  have hnum : |b₂ * (p * u + R) ^ 2 + 2 * b₁ * p + 2 * p * u / S + R / S ^ 3| ≤ 756 / 100 := by
    have hpu : |p * u| ≤ 1 / 100 := by
      rw [abs_mul]
      have ha : |u| ≤ 1 := abs_le.mpr ⟨by linarith only [hu0], hu1⟩
      have hmm : |p| * |u| ≤ (1 / 100) * 1 := mul_le_mul hp ha (abs_nonneg _) (by norm_num)
      linarith only [hmm]
    have hpuR : |p * u + R| ≤ (1011 : ℝ) / 1000 := by
      have h := abs_add_le (p * u) R
      have hRabs : |R| = R := abs_of_pos hRpos
      linarith only [h, hpu, hRabs, hRhi]
    have hsq : (p * u + R) ^ 2 ≤ 3 / 2 := by
      have h1 : (p * u + R) ^ 2 ≤ ((1011 : ℝ) / 1000) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hpuR 2
      nlinarith only [h1]
    have hb2sq : |b₂ * (p * u + R) ^ 2| ≤ 3 * (3 / 2) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (p * u + R))]
      exact mul_le_mul hb₂abs hsq (by positivity) (by norm_num)
    have hbp : |2 * b₁ * p| ≤ 1 / 25 := by
      rw [abs_mul, abs_mul]
      have h1 : |2| * |b₁| ≤ 2 * 2 := by
        have h2 : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
        rw [h2]
        have h3 := mul_le_mul_of_nonneg_left hb₁abs (by norm_num : (0 : ℝ) ≤ 2)
        linarith only [h3]
      have hmm := mul_le_mul h1 hp (abs_nonneg _) (by norm_num)
      linarith only [hmm]
    have hpuS : |2 * p * u / S| ≤ 1 / 50 := by
      rw [abs_div, abs_of_pos hSpos, div_le_iff₀ hSpos]
      have h1 : |2 * p * u| = 2 * |p| * u := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hu0]
      rw [h1]
      have h2 : 2 * |p| ≤ 2 * (1 / 100) := by linarith only [hp]
      have h4 : 2 * |p| * u ≤ (2 * (1 / 100)) * u := mul_le_mul_of_nonneg_right h2 hu0
      have h5 : (2 * (1 / 100)) * u ≤ (2 * (1 / 100)) * S :=
        mul_le_mul_of_nonneg_left huS (by norm_num)
      have h6 : (2 * (1 / 100)) * S = (1 / 50) * S := by norm_num
      linarith only [h4, h5, h6]
    have hRS3 : |R / S ^ 3| ≤ 3 := by
      have hSpos3 : (0 : ℝ) < S ^ 3 := by positivity
      rw [abs_of_pos (by positivity), div_le_iff₀ hSpos3]
      have h3 : (343 : ℝ) / 1000 ≤ S ^ 3 := by
        have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 7 / 10 by norm_num) hSge 3
        norm_num at h
        exact h
      nlinarith only [hRhi, h3]
    calc |b₂ * (p * u + R) ^ 2 + 2 * b₁ * p + 2 * p * u / S + R / S ^ 3|
        ≤ |b₂ * (p * u + R) ^ 2 + 2 * b₁ * p + 2 * p * u / S| + |R / S ^ 3| :=
          abs_add_le _ _
      _ ≤ (|b₂ * (p * u + R) ^ 2 + 2 * b₁ * p| + |2 * p * u / S|) + |R / S ^ 3| := by
          have h := abs_add_le (b₂ * (p * u + R) ^ 2 + 2 * b₁ * p) (2 * p * u / S)
          linarith only [h]
      _ ≤ ((|b₂ * (p * u + R) ^ 2| + |2 * b₁ * p|) + |2 * p * u / S|) + |R / S ^ 3| := by
          have h := abs_add_le (b₂ * (p * u + R) ^ 2) (2 * b₁ * p)
          linarith only [h]
      _ ≤ ((3 * (3 / 2) + 1 / 25) + 1 / 50) + 3 := by
          linarith only [hb2sq, hbp, hpuS, hRS3]
      _ = 756 / 100 := by norm_num
  have hq : |q| ≤ 30 := by
    have h1 : |q| * ((69 : ℝ) / 100) ≤ |q| * (S - b₁ * u) :=
      mul_le_mul_of_nonneg_left hD2 (abs_nonneg q)
    have h2 : |q| * ((69 : ℝ) / 100) ≤ 756 / 100 := by linarith only [h1, hEq2, hnum]
    nlinarith only [h2]
  exact ⟨by linarith only [hp], hq⟩

end Work.OddCurve.LowSlope
