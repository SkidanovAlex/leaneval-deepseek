import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

namespace Commons.NumberTheory.Chebyshev

/-- Under RH, `|ψ(y) − y| = O(√y (log y)^10)`. -/
lemma psi_abs_sub_id_rh_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      |Chebyshev.psi y - y| ≤ C * Real.sqrt y * (Real.log y) ^ 10 := by
  obtain ⟨Cθ, hCθ0, x₀θ, hθ⟩ :=
    Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound h
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨Cθ + max C₀ 0, by positivity, max x₀θ (Real.exp 1), ?_⟩
  intro y hy
  have hyθ : x₀θ ≤ y := le_trans (le_max_left _ _) hy
  have hye : Real.exp 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy1 : (1 : ℝ) ≤ y := by
    have h := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos 1) hye
    rwa [Real.log_exp] at h
  have hpow1 : (1 : ℝ) ≤ (Real.log y) ^ 10 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog1 10
    simpa using hp
  have hsqrt : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hdiff_nonneg : 0 ≤ Chebyshev.psi y - Chebyshev.theta y :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi y)
  have hdiff_le : Chebyshev.psi y - Chebyshev.theta y ≤ max C₀ 0 * Real.sqrt y := by
    calc Chebyshev.psi y - Chebyshev.theta y ≤ C₀ * Real.sqrt y := hC₀ y
      _ ≤ max C₀ 0 * Real.sqrt y := mul_le_mul_of_nonneg_right (le_max_left C₀ 0) hsqrt
  have htri : |Chebyshev.psi y - y| ≤
      (Chebyshev.psi y - Chebyshev.theta y) + |Chebyshev.theta y - y| := by
    have h1 : Chebyshev.psi y - y =
        (Chebyshev.psi y - Chebyshev.theta y) + (Chebyshev.theta y - y) := by ring
    rw [h1]
    calc |(Chebyshev.psi y - Chebyshev.theta y) + (Chebyshev.theta y - y)|
        ≤ |Chebyshev.psi y - Chebyshev.theta y| + |Chebyshev.theta y - y| := abs_add_le _ _
      _ = (Chebyshev.psi y - Chebyshev.theta y) + |Chebyshev.theta y - y| := by
          rw [abs_of_nonneg hdiff_nonneg]
  have hθy := hθ y hyθ
  have hm : max C₀ 0 * Real.sqrt y ≤ max C₀ 0 * Real.sqrt y * (Real.log y) ^ 10 :=
    le_mul_of_one_le_right (mul_nonneg (le_max_right C₀ 0) hsqrt) hpow1
  calc |Chebyshev.psi y - y|
      ≤ (Chebyshev.psi y - Chebyshev.theta y) + |Chebyshev.theta y - y| := htri
    _ ≤ max C₀ 0 * Real.sqrt y * (Real.log y) ^ 10 +
        Cθ * Real.sqrt y * (Real.log y) ^ 10 := add_le_add (le_trans hdiff_le hm) hθy
    _ = (Cθ + max C₀ 0) * Real.sqrt y * (Real.log y) ^ 10 := by ring

/-- `(x^a)^n = x^(a n)` for `x ≥ 0`, with the natural-number power converted to `rpow`. -/
private lemma rpow_pow_eq_mul {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    (x ^ a) ^ n = x ^ (a * n) := by
  have h1 : (x ^ a) ^ n = (x ^ a) ^ (n : ℝ) := by simp
  rw [h1, ← Real.rpow_mul hx a (n : ℝ)]

/-- For `1 ≤ x` and `2 ≤ n`, the square root of `x^(1/n)` is at most `x^(1/4)`. -/
private lemma sqrt_rpow_inv_le_quarter {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (x ^ ((n : ℝ)⁻¹)) ≤ x ^ ((4 : ℝ)⁻¹) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnin : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) hnR
    simpa [one_div] using h
  have hle : x ^ ((n : ℝ)⁻¹) ≤ x ^ ((2 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hx hnin
  calc Real.sqrt (x ^ ((n : ℝ)⁻¹)) ≤ Real.sqrt (x ^ ((2 : ℝ)⁻¹)) := Real.sqrt_le_sqrt hle
    _ = x ^ ((4 : ℝ)⁻¹) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
        congr 1
        norm_num

/-- For `1 ≤ x` and `2 ≤ n`, the error term `C √y (log y)^10` at `y = x^(1/n)` is bounded
by the same expression with `√y` replaced by `x^(1/4)`. -/
private lemma log_error_le {C : ℝ} (hC : 0 ≤ C) {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 2 ≤ n) :
    C * Real.sqrt (x ^ ((n : ℝ)⁻¹)) * (Real.log (x ^ ((n : ℝ)⁻¹))) ^ 10 ≤
      C * x ^ ((4 : ℝ)⁻¹) * (Real.log x) ^ 10 := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hnin1 : (n : ℝ)⁻¹ ≤ 1 := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hnR
    simpa [one_div] using h
  have hy1 : 1 ≤ x ^ ((n : ℝ)⁻¹) := Real.one_le_rpow hx (by positivity)
  have hyx : x ^ ((n : ℝ)⁻¹) ≤ x := by
    calc x ^ ((n : ℝ)⁻¹) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hnin1
      _ = x := Real.rpow_one x
  have hlogy0 : 0 ≤ Real.log (x ^ ((n : ℝ)⁻¹)) := Real.log_nonneg hy1
  have hlogyx : Real.log (x ^ ((n : ℝ)⁻¹)) ≤ Real.log x :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hy1) hyx
  have hsqrt : Real.sqrt (x ^ ((n : ℝ)⁻¹)) ≤ x ^ ((4 : ℝ)⁻¹) :=
    sqrt_rpow_inv_le_quarter hx hn
  have hx4 : 0 ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0 _
  have hpow : (Real.log (x ^ ((n : ℝ)⁻¹))) ^ 10 ≤ (Real.log x) ^ 10 :=
    pow_le_pow_left₀ hlogy0 hlogyx 10
  have h1 : Real.sqrt (x ^ ((n : ℝ)⁻¹)) * (Real.log (x ^ ((n : ℝ)⁻¹))) ^ 10 ≤
      x ^ ((4 : ℝ)⁻¹) * (Real.log x) ^ 10 :=
    mul_le_mul hsqrt hpow (pow_nonneg hlogy0 10) hx4
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h1 hC

/-- Assembly step: given an RH-type bound `|ψ(y) − y| ≤ C √y (log y)^10`, deduce the
Lagarias-type two-sided bound for `ψ − θ`. -/
lemma psi_sub_theta_rh_of_bound (C : ℝ) (hC : 0 < C) (y₀ : ℝ)
    (hψ : ∀ y : ℝ, y₀ ≤ y → |Chebyshev.psi y - y| ≤ C * Real.sqrt y * (Real.log y) ^ 10) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      Real.sqrt x ≤ Chebyshev.psi x - Chebyshev.theta x ∧
      Chebyshev.psi x - Chebyshev.theta x - Real.sqrt x ≤ C' * x ^ (1 / 3 : ℝ) := by
  have hC0 : 0 ≤ C := le_of_lt hC
  have h6C : 0 < 6 * C := by linarith
  set y₁ : ℝ := max y₀ 1 with hy₁
  have hy₁1 : 1 ≤ y₁ := le_max_right _ _
  have hy₁0 : 0 < y₁ := lt_of_lt_of_le zero_lt_one hy₁1
  have hy₁y₀ : y₀ ≤ y₁ := le_max_left _ _
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      1 ≤ x ∧ y₁ ^ 7 ≤ x ∧ (6 * C) ^ 24 ≤ x ∧
        6 * C * (Real.log x) ^ 10 ≤ x ^ ((12 : ℝ)⁻¹) := by
    have h1 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, y₁ ^ 7 ≤ x := Filter.eventually_ge_atTop _
    have h4 : ∀ᶠ x : ℝ in Filter.atTop, (6 * C) ^ 24 ≤ x := Filter.eventually_ge_atTop _
    have h5 : ∀ᶠ x : ℝ in Filter.atTop,
        6 * C * (Real.log x) ^ 10 ≤ x ^ ((12 : ℝ)⁻¹) := by
      obtain ⟨X, _, hX⟩ :=
        Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
          (K := 6 * C) (le_of_lt h6C) (n := 10) (r := ((12 : ℝ)⁻¹)) (by norm_num)
      exact Filter.eventually_atTop.mpr ⟨X, fun x hx => hX x hx⟩
    filter_upwards [h1, h2, h4, h5] with x h1x h2x h4x h5x
    exact ⟨h1x, h2x, h4x, h5x⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨3, by norm_num, x₁, ?_⟩
  intro x hx
  obtain ⟨hx1, hxy1, _, hxkey⟩ := hx₁ x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hsx : Real.sqrt x = x ^ ((2 : ℝ)⁻¹) := by
    rw [Real.sqrt_eq_rpow, one_div]
  have h13 : x ^ (1 / 3 : ℝ) = x ^ ((3 : ℝ)⁻¹) := by rw [one_div]
  have hy₁x : y₁ ≤ x := by
    have h : y₁ ≤ y₁ ^ 7 := le_self_pow₀ hy₁1 (by norm_num : (7 : ℕ) ≠ 0)
    linarith
  have hry : y₁ ≤ x ^ ((7 : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ y₁ ^ 7) hxy1
      (by norm_num : (0 : ℝ) ≤ ((7 : ℝ))⁻¹)
    have h2 : (y₁ ^ 7 : ℝ) ^ ((7 : ℝ)⁻¹) = y₁ :=
      Real.pow_rpow_inv_natCast (le_of_lt hy₁0) (n := 7) (by norm_num)
    rwa [h2] at h
  have hge2 : y₁ ≤ x ^ ((2 : ℝ)⁻¹) :=
    le_trans hry (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hge3 : y₁ ≤ x ^ ((3 : ℝ)⁻¹) :=
    le_trans hry (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hge5 : y₁ ≤ x ^ ((5 : ℝ)⁻¹) :=
    le_trans hry (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hub : ∀ y : ℝ, y₁ ≤ y →
      Chebyshev.psi y ≤ y + C * Real.sqrt y * (Real.log y) ^ 10 := by
    intro y hy
    have h := le_trans (le_abs_self (Chebyshev.psi y - y)) (hψ y (le_trans hy₁y₀ hy))
    linarith
  have hlb : ∀ y : ℝ, y₁ ≤ y →
      y - C * Real.sqrt y * (Real.log y) ^ 10 ≤ Chebyshev.psi y := by
    intro y hy
    have h := le_trans (neg_le_abs (Chebyshev.psi y - y)) (hψ y (le_trans hy₁y₀ hy))
    linarith
  have hQ : 3 * (C * x ^ ((4 : ℝ)⁻¹) * (Real.log x) ^ 10) ≤ x ^ ((3 : ℝ)⁻¹) / 2 := by
    have hx4 : 0 ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
    have h := mul_le_mul_of_nonneg_right hxkey hx4
    have hmul : x ^ ((12 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) = x ^ ((3 : ℝ)⁻¹) := by
      rw [← Real.rpow_add hx0]
      congr 1
      norm_num
    have hlhs : 6 * C * (Real.log x) ^ 10 * x ^ ((4 : ℝ)⁻¹) =
        6 * (C * x ^ ((4 : ℝ)⁻¹) * (Real.log x) ^ 10) := by ring
    rw [hmul, hlhs] at h
    linarith
  have hE2 := log_error_le hC0 hx1 (n := 2) (by norm_num)
  have hE3 := log_error_le hC0 hx1 (n := 3) (by norm_num)
  have hE5 := log_error_le hC0 hx1 (n := 5) (by norm_num)
  have hE7 := log_error_le hC0 hx1 (n := 7) (by norm_num)
  have h5le : x ^ ((5 : ℝ)⁻¹) ≤ x ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hup : Chebyshev.psi x - Chebyshev.theta x - x ^ ((2 : ℝ)⁻¹) ≤
      3 * x ^ ((3 : ℝ)⁻¹) := by
    have hcosta := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    have hsum : Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) + Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) +
        Chebyshev.psi (x ^ ((5 : ℝ)⁻¹))
        ≤ (x ^ ((2 : ℝ)⁻¹) + C * Real.sqrt (x ^ ((2 : ℝ)⁻¹)) *
              (Real.log (x ^ ((2 : ℝ)⁻¹))) ^ 10)
          + (x ^ ((3 : ℝ)⁻¹) + C * Real.sqrt (x ^ ((3 : ℝ)⁻¹)) *
              (Real.log (x ^ ((3 : ℝ)⁻¹))) ^ 10)
          + (x ^ ((5 : ℝ)⁻¹) + C * Real.sqrt (x ^ ((5 : ℝ)⁻¹)) *
              (Real.log (x ^ ((5 : ℝ)⁻¹))) ^ 10) :=
      add_le_add (add_le_add (hub _ hge2) (hub _ hge3)) (hub _ hge5)
    have herr : C * Real.sqrt (x ^ ((2 : ℝ)⁻¹)) * (Real.log (x ^ ((2 : ℝ)⁻¹))) ^ 10 +
          C * Real.sqrt (x ^ ((3 : ℝ)⁻¹)) * (Real.log (x ^ ((3 : ℝ)⁻¹))) ^ 10 +
          C * Real.sqrt (x ^ ((5 : ℝ)⁻¹)) * (Real.log (x ^ ((5 : ℝ)⁻¹))) ^ 10
        ≤ x ^ ((3 : ℝ)⁻¹) / 2 := by
      linarith [hE2, hE3, hE5, hQ]
    linarith
  have hlow : x ^ ((2 : ℝ)⁻¹) ≤ Chebyshev.psi x - Chebyshev.theta x := by
    have hcosta := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx0.le
    have h1 := hlb _ hge2
    have h2 := hlb _ hge3
    have h3 := hlb _ hry
    have hB0 : 0 ≤ x ^ ((3 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
    have hD0 : 0 ≤ x ^ ((7 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
    linarith [hcosta, h1, h2, h3, hE2, hE3, hE7, hQ, hB0, hD0]
  refine ⟨?_, ?_⟩
  · rw [hsx]; exact hlow
  · rw [hsx, h13]; exact hup

theorem psi_sub_theta_rh (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      Real.sqrt x ≤ Chebyshev.psi x - Chebyshev.theta x ∧
      Chebyshev.psi x - Chebyshev.theta x - Real.sqrt x ≤ C * x ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, y₀, hψ⟩ := psi_abs_sub_id_rh_bound h
  exact psi_sub_theta_rh_of_bound C hC y₀ hψ

end Commons.NumberTheory.Chebyshev
