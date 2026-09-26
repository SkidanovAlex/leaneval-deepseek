import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ModerateGrowth

/-!
# `E₂ ∈ 𝒫`

The weight-two Eisenstein series `E₂` (Mathlib's `EisensteinSeries.E2`, the normalized
series `1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ`) has moderate growth on `ℍ`: from the `q`-expansion one
gets `‖E₂ τ‖ ≤ C ((im τ)⁻¹)³`.  Hence `E₂ ∈ 𝒫 = Work.Kernels.InP`.

The proof is elementary: bounding the `q`-expansion termwise by the Lambert series
`∑ σ₁(n) xⁿ = ∑ n xⁿ/(1 - xⁿ)` (with `x = |q|`) and majorizing the latter by a geometric
series gives `∑ σ₁(n) xⁿ ≤ x/(1-x)³`, and `1 - x = 1 - e^{-2π im τ}` is bounded below by
`min (2π im τ) 1 / 2` via `1 - e^{-u} ≥ u/(1+u)`.
-/

noncomputable section

open UpperHalfPlane

namespace Work.Kernels.ClassicalFacts

/-- The `q`-parameter `q = e^{2πiτ}` has modulus `e^{-2π im τ}`. -/
lemma e2_norm_qExp (τ : ℍ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ))‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  have h := Function.Periodic.norm_qParam (h := 1) (z := (τ : ℂ))
  simp only [Function.Periodic.qParam, div_one, Complex.ofReal_one, UpperHalfPlane.coe_im] at h
  rw [h]
  ring_nf

/-- `E₂` is dominated by the (real) divisor-sum series `1 + 24 ∑ σ₁(n) xⁿ`, `x = |q|`. -/
lemma e2_norm_le_tsum (τ : ℍ) :
    ‖Work.Kernels.E2Fun τ‖ ≤ 1 + 24 * ∑' n : ℕ+,
      (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) ^ (n : ℕ) := by
  have hsum : Summable fun n : ℕ+ =>
      ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℂ) *
        Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℕ) := by
    refine (summable_pnat_iff_summable_nat (f := fun n : ℕ =>
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℂ) *
        Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ n)).mpr ?_
    simpa using EisensteinSeries.summable_sigma_mul_cexp_pow (k := 2) (by norm_num) τ
  have hnorm : ∀ n : ℕ+, ‖((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℕ)‖
      = (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
        Real.exp (-(2 * Real.pi * τ.im)) ^ (n : ℕ) := by
    intro n
    rw [norm_mul, norm_pow, e2_norm_qExp τ, Complex.norm_natCast]
  have hE : Work.Kernels.E2Fun τ = 1 - 24 * ∑' n : ℕ+,
      ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℂ) *
        Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℕ) :=
    EisensteinSeries.E2_eq_tsum_cexp τ
  rw [hE]
  calc ‖1 - 24 * ∑' n : ℕ+, ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℂ) *
          Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℕ)‖
      ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * ∑' n : ℕ+, ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℂ) *
          Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℕ)‖ := norm_sub_le _ _
    _ = 1 + 24 * ‖∑' n : ℕ+, ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℂ) *
          Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℕ)‖ := by
          rw [norm_one, norm_mul]; norm_num
    _ ≤ 1 + 24 * ∑' n : ℕ+, ‖((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℂ) *
          Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℕ)‖ := by
          have := norm_tsum_le_tsum_norm (hsum.norm)
          linarith
    _ = 1 + 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
          Real.exp (-(2 * Real.pi * τ.im)) ^ (n : ℕ) := by
          rw [tsum_congr hnorm]

/-- The divisor-sum (Lambert) series is bounded by a geometric series:
`∑_{n ≥ 1} σ₁(n) xⁿ ≤ x/(1-x)³`. -/
lemma e2_tsum_sigma_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * r ^ (n : ℕ)
      ≤ r / (1 - r) ^ 3 := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hpos : (0 : ℝ) < 1 - r := by linarith
  rw [← tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) hnorm 1]
  have hpt : ∀ n : ℕ+, (n : ℝ) ^ 1 * r ^ (n : ℕ) / (1 - r ^ (n : ℕ))
      ≤ (n : ℝ) * r ^ (n : ℕ) / (1 - r) := by
    intro n
    have hn1 : 1 ≤ (n : ℕ) := n.2
    have hrn : r ^ (n : ℕ) ≤ r := by
      simpa using pow_le_pow_of_le_one hr0 hr1.le hn1
    have hx : (0 : ℝ) ≤ (n : ℝ) * r ^ (n : ℕ) := by positivity
    have := div_le_div_of_nonneg_left hx hpos (by linarith : 1 - r ≤ 1 - r ^ (n : ℕ))
    simpa using this
  have hsumL : Summable fun n : ℕ+ =>
      (n : ℝ) ^ 1 * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) :=
    (summable_pnat_iff_summable_nat (f := fun n : ℕ =>
      (n : ℝ) ^ 1 * r ^ n / (1 - r ^ n))).mpr
      (summable_norm_pow_mul_geometric_div_one_sub 1 hnorm)
  have hsumR : Summable fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ) / (1 - r) := by
    refine (summable_pnat_iff_summable_nat (f := fun n : ℕ =>
      (n : ℝ) * r ^ n / (1 - r))).mpr ?_
    have hb : Summable fun n : ℕ => (n : ℝ) ^ 1 * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    simpa [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using hb.mul_left ((1 - r)⁻¹)
  have hgeom : ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) = r / (1 - r) ^ 2 := by
    have hsum : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    have h0 := tsum_zero_pnat_eq_tsum_nat hsum
    simp only [Nat.cast_zero, zero_mul, zero_add] at h0
    rw [h0, tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  calc ∑' n : ℕ+, (n : ℝ) ^ 1 * r ^ (n : ℕ) / (1 - r ^ (n : ℕ))
      ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
        Summable.tsum_le_tsum hpt hsumL hsumR
    _ = (1 - r)⁻¹ * ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by rw [div_eq_mul_inv]; ring
    _ = (1 - r)⁻¹ * (r / (1 - r) ^ 2) := by rw [hgeom]
    _ = r / (1 - r) ^ 3 := by
        rw [div_eq_mul_inv]
        field_simp

/-- The elementary lower bound `u/(1+u) ≤ 1 - e^{-u}` for `u ≥ 0`. -/
lemma e2_div_le_one_sub_exp_neg (u : ℝ) (hu : 0 ≤ u) :
    u / (1 + u) ≤ 1 - Real.exp (-u) := by
  have h : (1 : ℝ) + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hexp : Real.exp (-u) * (1 + u) ≤ 1 := by
    have h2 : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-u) * (1 + u) ≤ Real.exp (-u) * Real.exp u :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = 1 := h2
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + u)]
  linarith

/-- The cube of the reciprocal of `1 - e^{-u}` is at most `8 + 8/u³`. -/
lemma e2_one_sub_exp_neg_cube_le (u : ℝ) (hu : 0 < u) :
    (1 - Real.exp (-u))⁻¹ ^ 3 ≤ 8 + 8 * (u⁻¹) ^ 3 := by
  have hmain : u / (1 + u) ≤ 1 - Real.exp (-u) := e2_div_le_one_sub_exp_neg u hu.le
  have hpos : (0 : ℝ) < 1 - Real.exp (-u) := by
    have h1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rcases lt_or_ge u 1 with h | h
  · have hu1 : u ≤ 1 := le_of_lt h
    have h2 : u / 2 ≤ 1 - Real.exp (-u) := by
      have h3 : u / 2 ≤ u / (1 + u) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by linarith : (0 : ℝ) < 1 + u)]
        nlinarith [hu, hu1]
      linarith
    have h4 : (1 - Real.exp (-u))⁻¹ ≤ 2 * u⁻¹ := by
      rw [inv_le_comm₀ hpos (by positivity : (0 : ℝ) < 2 * u⁻¹)]
      have hh : (2 * u⁻¹)⁻¹ = u / 2 := by rw [mul_inv_rev, inv_inv]; ring
      rw [hh]
      exact h2
    have h5 : (1 - Real.exp (-u))⁻¹ ^ 3 ≤ 8 * (u⁻¹) ^ 3 := by
      calc (1 - Real.exp (-u))⁻¹ ^ 3 ≤ (2 * u⁻¹) ^ 3 :=
            pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) h4 3
        _ = 8 * (u⁻¹) ^ 3 := by rw [mul_pow]; norm_num
    linarith
  · have h2 : (1 : ℝ) / 2 ≤ 1 - Real.exp (-u) := by
      have h3 : (1 : ℝ) / 2 ≤ u / (1 + u) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + u)]
        linarith
      linarith
    have h4 : (1 - Real.exp (-u))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have h5 : (1 - Real.exp (-u))⁻¹ ^ 3 ≤ 8 := by
      calc (1 - Real.exp (-u))⁻¹ ^ 3 ≤ (2 : ℝ) ^ 3 :=
            pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) h4 3
        _ = 8 := by norm_num
    have h6 : (0 : ℝ) ≤ 8 * (u⁻¹) ^ 3 := by positivity
    linarith

/-- Specialization to `u = 2πy`, `y > 0`: `(1 - e^{-2πy})⁻³ ≤ 8 + y⁻³`. -/
lemma e2_one_sub_exp_neg_cube_le' (y : ℝ) (hy : 0 < y) :
    (1 - Real.exp (-(2 * Real.pi * y)))⁻¹ ^ 3 ≤ 8 + (y⁻¹) ^ 3 := by
  have hu : 0 < 2 * Real.pi * y := by positivity
  have h := e2_one_sub_exp_neg_cube_le (2 * Real.pi * y) hu
  have hcoef : 8 * ((2 * Real.pi)⁻¹ : ℝ) ^ 3 ≤ 1 := by
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    have h1 : (1 : ℝ) ≤ Real.pi ^ 3 :=
      one_le_pow₀ (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
    have h2 : ((2 * Real.pi)⁻¹ : ℝ) ^ 3 = 1 / (2 * Real.pi) ^ 3 := by
      rw [inv_pow, one_div]
    rw [h2, mul_one_div, div_le_one (by positivity)]
    nlinarith [h1, hp, sq_nonneg Real.pi]
  have hsplit : 8 * ((2 * Real.pi * y)⁻¹) ^ 3
      = (8 * ((2 * Real.pi)⁻¹ : ℝ) ^ 3) * (y⁻¹) ^ 3 := by
    rw [mul_inv, mul_pow]
    ring
  calc (1 - Real.exp (-(2 * Real.pi * y)))⁻¹ ^ 3
      ≤ 8 + 8 * ((2 * Real.pi * y)⁻¹) ^ 3 := h
    _ = 8 + (8 * ((2 * Real.pi)⁻¹ : ℝ) ^ 3) * (y⁻¹) ^ 3 := by rw [hsplit]
    _ ≤ 8 + 1 * (y⁻¹) ^ 3 := by
        have hyi : (0 : ℝ) ≤ (y⁻¹) ^ 3 := by positivity
        have := mul_le_mul_of_nonneg_right hcoef hyi
        linarith
    _ = 8 + (y⁻¹) ^ 3 := by ring

lemma E2Fun_mem_InP : Work.Kernels.InP Work.Kernels.E2Fun := by
  refine ⟨E2_mdifferentiable, ?_⟩
  refine ⟨193, 3, 0, by norm_num, by norm_num, by norm_num, fun τ _ => ?_⟩
  have h1 := e2_norm_le_tsum τ
  have hr0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * Real.pi * τ.im)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, τ.im_pos]
  have h2 := e2_tsum_sigma_le (Real.exp (-(2 * Real.pi * τ.im))) hr0 hr1
  have h3 := e2_one_sub_exp_neg_cube_le' τ.im τ.im_pos
  have hkey : ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
        Real.exp (-(2 * Real.pi * τ.im)) ^ (n : ℕ)
      ≤ 8 + (τ.im⁻¹) ^ 3 := by
    calc ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
            Real.exp (-(2 * Real.pi * τ.im)) ^ (n : ℕ)
        ≤ Real.exp (-(2 * Real.pi * τ.im)) /
            (1 - Real.exp (-(2 * Real.pi * τ.im))) ^ 3 := h2
      _ = Real.exp (-(2 * Real.pi * τ.im)) *
            ((1 - Real.exp (-(2 * Real.pi * τ.im)))⁻¹) ^ 3 := by
          rw [div_eq_mul_inv, inv_pow]
      _ ≤ 1 * ((1 - Real.exp (-(2 * Real.pi * τ.im)))⁻¹) ^ 3 := by
          refine mul_le_mul_of_nonneg_right hr1.le ?_
          positivity
      _ = ((1 - Real.exp (-(2 * Real.pi * τ.im)))⁻¹) ^ 3 := one_mul _
      _ ≤ 8 + (τ.im⁻¹) ^ 3 := h3
  have hbound : ‖Work.Kernels.E2Fun τ‖ ≤ 193 * (1 + (τ.im⁻¹) ^ 3) := by
    have hx : (0 : ℝ) ≤ (τ.im⁻¹) ^ 3 := by positivity
    linarith
  have hfinal : 193 * ((τ.im)⁻¹ ^ (3 : ℝ) + ‖(τ : ℂ)‖ ^ (0 : ℝ))
      = 193 * (1 + (τ.im⁻¹) ^ 3) := by
    rw [Real.rpow_ofNat, Real.rpow_zero]
    ring
  rw [hfinal]
  exact hbound

end Work.Kernels.ClassicalFacts
