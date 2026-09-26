/-
# Boundedness of the modular lambda function at the cusp `i∞`

The modular lambda function `λ = θ₁₀⁴/θ₀₀⁴` tends to `0` at the cusp `i∞`.  In terms of
`q = e^{π i τ}` one has `λ(τ) = lambdaSeries q` with
`lambdaSeries z = 16 z (aSeries z)⁴ / (bSeries z)⁴`, a function analytic at `z = 0` with
`lambdaSeries 0 = 0`; hence `λ` is bounded at `i∞`.

The proof here is completely explicit, avoiding all analyticity input: for `‖z‖ ≤ 1/5`
one has `‖aSeries z‖ ≤ 2` (every monomial `z ^ (m (m+1))` is dominated by `z ^ m`) and
`‖bSeries z‖ ≥ 1/2` (the terms of `bCore` are dominated by `‖z‖ ^ (m+1)`, whose sum is
`‖z‖ / (1 - ‖z‖) ≤ 1/4`).  Consequently

  `‖lambdaSeries z‖ ≤ 16 · ‖z‖ · 2⁴ / (1/2)⁴ = 4096 ‖z‖`   for `‖z‖ ≤ 1/5`,

and since `‖e^{π i τ}‖ = e^{-π Im τ}`, the single bound `‖λ τ‖ ≤ 1` holds whenever
`Im τ ≥ log 4096 / π`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Rigidity.lambdaFun_eq_lambdaSeries

noncomputable section

open UpperHalfPlane Filter Topology
open scoped Topology UpperHalfPlane

namespace Work.Rigidity

/-! ## Elementary bounds on the `q`-series `aSeries`, `bCore`, `bSeries` -/

/-- `aSeries z = ∑ z^{m(m+1)}` is absolutely convergent for `‖z‖ < 1`. -/
private lemma summable_pow_mul_succ (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun m : ℕ => z ^ (m * (m + 1))) := by
  apply Summable.of_norm_bounded (g := fun m : ℕ => ‖z‖ ^ m)
  · exact summable_geometric_of_lt_one (norm_nonneg z) hz
  · intro m
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg z) hz.le
      (Nat.le_mul_of_pos_right (m := m + 1) m (Nat.succ_pos m))

/-- `bCore z = ∑ z^{(m+1)²}` is absolutely convergent for `‖z‖ < 1`. -/
private lemma summable_pow_succ_sq (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun m : ℕ => z ^ ((m + 1) * (m + 1))) := by
  apply Summable.of_norm_bounded (g := fun m : ℕ => ‖z‖ ^ (m + 1))
  · exact (summable_nat_add_iff (f := fun m : ℕ => ‖z‖ ^ m) 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg z) hz)
  · intro m
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg z) hz.le
      (Nat.le_mul_of_pos_right (m := m + 1) (m + 1) (Nat.succ_pos m))

/-- `∑_{m ≥ 0} ‖z‖^{m+1} = ‖z‖ (1 - ‖z‖)⁻¹`. -/
private lemma tsum_pow_succ (z : ℂ) (hz : ‖z‖ < 1) :
    ∑' m : ℕ, ‖z‖ ^ (m + 1) = ‖z‖ * (1 - ‖z‖)⁻¹ := by
  rw [show (fun m : ℕ => ‖z‖ ^ (m + 1)) = (fun m : ℕ => ‖z‖ * ‖z‖ ^ m) by
    funext m; rw [pow_succ']]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg z) hz]

/-- For `‖z‖ ≤ 1/2` the series `aSeries z` is bounded by `2`. -/
private lemma norm_aSeries_le (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : ‖aSeries z‖ ≤ 2 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hs : Summable (fun m : ℕ => z ^ (m * (m + 1))) := summable_pow_mul_succ z hz1
  have hgeom : Summable (fun m : ℕ => ‖z‖ ^ m) := summable_geometric_of_lt_one (norm_nonneg z) hz1
  have hterm : ∀ m : ℕ, ‖z‖ ^ (m * (m + 1)) ≤ ‖z‖ ^ m := fun m =>
    pow_le_pow_of_le_one (norm_nonneg z) hz1.le
      (Nat.le_mul_of_pos_right (m := m + 1) m (Nat.succ_pos m))
  have hreal : Summable (fun m : ℕ => ‖z‖ ^ (m * (m + 1))) :=
    Summable.of_nonneg_of_le (fun m => pow_nonneg (norm_nonneg z) _) hterm hgeom
  calc ‖aSeries z‖ = ‖∑' m : ℕ, z ^ (m * (m + 1))‖ := by rw [aSeries_apply]
    _ ≤ ∑' m : ℕ, ‖z ^ (m * (m + 1))‖ := norm_tsum_le_tsum_norm hs.norm
    _ = ∑' m : ℕ, ‖z‖ ^ (m * (m + 1)) := by simp only [norm_pow]
    _ ≤ ∑' m : ℕ, ‖z‖ ^ m := Summable.tsum_le_tsum hterm hreal hgeom
    _ = (1 - ‖z‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg z) hz1
    _ ≤ 2 := by
        have hle : (1 / 2 : ℝ) ≤ 1 - ‖z‖ := by linarith
        calc (1 - ‖z‖)⁻¹ = 1 / (1 - ‖z‖) := by rw [one_div]
          _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hle
          _ = 2 := by norm_num

/-- For `‖z‖ ≤ 1/5` the series `bCore z` is bounded by `1/4`. -/
private lemma norm_bCore_le (z : ℂ) (hz : ‖z‖ ≤ 1 / 5) : ‖bCore z‖ ≤ 1 / 4 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hs : Summable (fun m : ℕ => z ^ ((m + 1) * (m + 1))) := summable_pow_succ_sq z hz1
  have hgeom : Summable (fun m : ℕ => ‖z‖ ^ (m + 1)) :=
    (summable_nat_add_iff (f := fun m : ℕ => ‖z‖ ^ m) 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg z) hz1)
  have hterm : ∀ m : ℕ, ‖z‖ ^ ((m + 1) * (m + 1)) ≤ ‖z‖ ^ (m + 1) := fun m =>
    pow_le_pow_of_le_one (norm_nonneg z) hz1.le
      (Nat.le_mul_of_pos_right (m := m + 1) (m + 1) (Nat.succ_pos m))
  have hreal : Summable (fun m : ℕ => ‖z‖ ^ ((m + 1) * (m + 1))) :=
    Summable.of_nonneg_of_le (fun m => pow_nonneg (norm_nonneg z) _) hterm hgeom
  have hval := tsum_pow_succ z hz1
  calc ‖bCore z‖ = ‖∑' m : ℕ, z ^ ((m + 1) * (m + 1))‖ := by rw [bCore_apply]
    _ ≤ ∑' m : ℕ, ‖z ^ ((m + 1) * (m + 1))‖ := norm_tsum_le_tsum_norm hs.norm
    _ = ∑' m : ℕ, ‖z‖ ^ ((m + 1) * (m + 1)) := by simp only [norm_pow]
    _ ≤ ∑' m : ℕ, ‖z‖ ^ (m + 1) := Summable.tsum_le_tsum hterm hreal hgeom
    _ = ‖z‖ * (1 - ‖z‖)⁻¹ := hval
    _ ≤ 1 / 4 := by
        have hb : (1 - ‖z‖)⁻¹ ≤ 5 / 4 := by
          have hle : (4 / 5 : ℝ) ≤ 1 - ‖z‖ := by linarith
          calc (1 - ‖z‖)⁻¹ = 1 / (1 - ‖z‖) := by rw [one_div]
            _ ≤ 1 / (4 / 5 : ℝ) := one_div_le_one_div_of_le (by norm_num) hle
            _ = 5 / 4 := by norm_num
        have h1 : ‖z‖ * (1 - ‖z‖)⁻¹ ≤ (1 / 5) * (5 / 4) :=
          mul_le_mul hz hb (inv_nonneg.mpr (by linarith)) (by norm_num)
        linarith

/-- For `‖z‖ ≤ 1/5` the series `bSeries z` is bounded below by `1/2`. -/
private lemma norm_bSeries_ge (z : ℂ) (hz : ‖z‖ ≤ 1 / 5) : (1 / 2 : ℝ) ≤ ‖bSeries z‖ := by
  have hb := norm_bCore_le z hz
  have h2 : ‖2 * bCore z‖ ≤ 1 / 2 := by
    rw [norm_mul]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    linarith
  have h := abs_norm_sub_norm_le (1 : ℂ) (-(2 * bCore z))
  rw [norm_neg, norm_one] at h
  have hmain : |(1 : ℝ) - ‖2 * bCore z‖| ≤ ‖1 + 2 * bCore z‖ := by
    simpa using h
  have hval : (1 / 2 : ℝ) ≤ |(1 : ℝ) - ‖2 * bCore z‖| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [bSeries_apply]
  linarith

/-! ## The bound on the `q`-expansion of `λ` -/

/-- For `‖z‖ ≤ 1/5` the `q`-expansion of `λ` is bounded by `4096 ‖z‖`. -/
private lemma norm_lambdaSeries_le (z : ℂ) (hz : ‖z‖ ≤ 1 / 5) :
    ‖lambdaSeries z‖ ≤ 4096 * ‖z‖ := by
  have ha : ‖aSeries z‖ ≤ 2 := norm_aSeries_le z (by linarith)
  have hb : (1 / 2 : ℝ) ≤ ‖bSeries z‖ := norm_bSeries_ge z hz
  have hA4 : ‖aSeries z‖ ^ 4 ≤ 16 := by
    calc ‖aSeries z‖ ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (norm_nonneg _) ha 4
      _ = 16 := by norm_num
  have hB4 : (‖bSeries z‖ ^ 4)⁻¹ ≤ 16 := by
    have hb4 : (1 / 16 : ℝ) ≤ ‖bSeries z‖ ^ 4 := by
      calc (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ 4 := by norm_num
        _ ≤ ‖bSeries z‖ ^ 4 := pow_le_pow_left₀ (by norm_num) hb 4
    calc (‖bSeries z‖ ^ 4)⁻¹ = 1 / ‖bSeries z‖ ^ 4 := by rw [one_div]
      _ ≤ 1 / (1 / 16 : ℝ) := one_div_le_one_div_of_le (by norm_num) hb4
      _ = 16 := by norm_num
  have h1 : 16 * ‖z‖ * ‖aSeries z‖ ^ 4 ≤ 16 * ‖z‖ * 16 :=
    mul_le_mul_of_nonneg_left hA4 (by positivity)
  have h2 : (16 * ‖z‖ * ‖aSeries z‖ ^ 4) * (‖bSeries z‖ ^ 4)⁻¹
      ≤ (16 * ‖z‖ * 16) * 16 :=
    mul_le_mul h1 hB4 (by positivity) (by positivity)
  calc ‖lambdaSeries z‖
      = 16 * ‖z‖ * ‖aSeries z‖ ^ 4 * (‖bSeries z‖ ^ 4)⁻¹ := by
        rw [lambdaSeries_apply, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
          Complex.norm_ofNat, div_eq_mul_inv]
    _ ≤ 16 * ‖z‖ * 16 * 16 := h2
    _ = 4096 * ‖z‖ := by ring

/-! ## Boundedness at the cusp -/

/-- `‖e^{π i τ}‖ = e^{-π Im τ}`. -/
private lemma norm_exp_pi_I_mul (τ : ℍ) :
    ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ = Real.exp (-(Real.pi * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
  ring

theorem isBoundedAtImInfty_lambdaFun :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => Work.Kernels.lambdaFun τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨1, Real.log 4096 / Real.pi, fun τ hτ => ?_⟩
  have hq : ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ≤ 1 / 4096 := by
    rw [norm_exp_pi_I_mul]
    have hlog : Real.log 4096 ≤ Real.pi * τ.im := by
      have h := mul_le_mul_of_nonneg_left hτ Real.pi_pos.le
      rwa [mul_div_cancel₀ (Real.log 4096) Real.pi_ne_zero] at h
    have hexp : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-(Real.log 4096)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(Real.log 4096)) = 1 / 4096 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
    rw [hval] at hexp
    linarith
  have hq5 : ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ≤ 1 / 5 := by linarith
  rw [lambdaFun_eq_lambdaSeries τ]
  calc ‖lambdaSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))‖
      ≤ 4096 * ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ := norm_lambdaSeries_le _ hq5
    _ ≤ 4096 * (1 / 4096) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = 1 := by norm_num

end Work.Rigidity
