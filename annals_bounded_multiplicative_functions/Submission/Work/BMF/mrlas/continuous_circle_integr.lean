import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the inverse power series on a circle of radius `ρ < 1/2`

Let `a : ℕ → ℂ` satisfy `a 0 = 1` and `‖a n‖ ≤ 1` for every `n`, and let `0 < ρ < 1/2`.
For the power series `F(z) = ∑_{e} a e * z^e` we consider the function of the angle `θ`

`G θ = (∑_{e} a e * (ρ * exp (θ * I))^e)⁻¹`

on the circle `‖z‖ = ρ`.  Two facts combine:

* `G` is continuous in `θ`: the series converges uniformly in `θ` by the Weierstrass
  `M`-test with majorant `ρ^e` (since `‖ρ * exp (θ I)‖ = ρ`), and each partial sum is
  continuous;
* `G` is everywhere non-zero on the circle: the sum differs from `1 = a 0` by at most
  `∑_{e ≥ 1} ρ^e = ρ / (1 - ρ) < 1`, so its modulus is at least `1 - ρ/(1 - ρ) > 0`.

The continuity of `G`, of `‖G‖`, and of `‖G‖²` follows.  This is the input to the `L²`
theory of `1 / F` on the circle used in the Halász–Montgomery argument.
-/

namespace Work.BMF.mrlas

open Complex Filter
open scoped Topology

/-- The power series `z ↦ ∑' e, a e * z ^ e` restricted to the circle of radius `ρ < 1/2`,
i.e. `θ ↦ ∑' e, a e * (ρ * exp (θ * I)) ^ e`, is continuous in `θ`.  The series converges
uniformly by the Weierstrass `M`-test with majorant `ρ ^ e`. -/
lemma continuous_circle_tsum (a : ℕ → ℂ) (hb : ∀ n, ‖a n‖ ≤ 1)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1 / 2) :
    Continuous (fun θ : ℝ => ∑' e : ℕ, a e * (ρ * Complex.exp (θ * Complex.I)) ^ e) := by
  have hρ1 : ρ < 1 := by linarith
  have hu : Summable (fun e : ℕ => ρ ^ e) := summable_geometric_of_lt_one hρ0.le hρ1
  have hz : ∀ θ : ℝ, ‖ρ * Complex.exp (θ * Complex.I)‖ = ρ := by
    intro θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ0]
  have hbound : ∀ (e : ℕ) (θ : ℝ), ‖a e * (ρ * Complex.exp (θ * Complex.I)) ^ e‖ ≤ ρ ^ e := by
    intro e θ
    rw [norm_mul, norm_pow, hz θ]
    calc ‖a e‖ * ρ ^ e ≤ 1 * ρ ^ e :=
          mul_le_mul_of_nonneg_right (hb e) (pow_nonneg hρ0.le e)
      _ = ρ ^ e := one_mul _
  have hc : ∀ e : ℕ,
      ContinuousOn (fun θ : ℝ => a e * (ρ * Complex.exp (θ * Complex.I)) ^ e) Set.univ :=
    fun e =>
      (by fun_prop : Continuous
        (fun θ : ℝ => a e * (ρ * Complex.exp (θ * Complex.I)) ^ e)).continuousOn
  have h := continuousOn_tsum hc hu (fun n x _ => hbound n x)
  rwa [continuousOn_univ] at h

/-- On the circle of radius `ρ < 1/2`, the power series `∑' e, a e * z ^ e` with `a 0 = 1`,
`‖a e‖ ≤ 1` never vanishes: it differs from `1` by at most `ρ / (1 - ρ) < 1`. -/
lemma circle_tsum_ne_zero (a : ℕ → ℂ) (ha0 : a 0 = 1) (hb : ∀ n, ‖a n‖ ≤ 1)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1 / 2) (θ : ℝ) :
    (∑' e : ℕ, a e * (ρ * Complex.exp (θ * Complex.I)) ^ e) ≠ 0 := by
  have hρ1 : ρ < 1 := by linarith
  have hu : Summable (fun e : ℕ => ρ ^ e) := summable_geometric_of_lt_one hρ0.le hρ1
  have hu' : Summable (fun e : ℕ => ρ ^ (e + 1)) := (summable_nat_add_iff 1).mpr hu
  have hz : ‖ρ * Complex.exp (θ * Complex.I)‖ = ρ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ0]
  set z : ℂ := ρ * Complex.exp (θ * Complex.I) with hzdef
  have hzρ : ‖z‖ = ρ := hz
  have hterm : ∀ e : ℕ, ‖a e * z ^ e‖ ≤ ρ ^ e := by
    intro e
    rw [norm_mul, norm_pow, hzρ]
    calc ‖a e‖ * ρ ^ e ≤ 1 * ρ ^ e :=
          mul_le_mul_of_nonneg_right (hb e) (pow_nonneg hρ0.le e)
      _ = ρ ^ e := one_mul _
  have hsum : Summable (fun e : ℕ => a e * z ^ e) :=
    Summable.of_norm (hu.of_nonneg_of_le (fun e => norm_nonneg _) hterm)
  have hshift : ∑' e : ℕ, a e * z ^ e = 1 + ∑' e : ℕ, a (e + 1) * z ^ (e + 1) := by
    rw [hsum.tsum_eq_zero_add]
    simp [ha0]
  have hT : ‖∑' e : ℕ, a (e + 1) * z ^ (e + 1)‖ ≤ ρ / (1 - ρ) := by
    have hsumT : Summable (fun e : ℕ => a (e + 1) * z ^ (e + 1)) :=
      Summable.of_norm (hu'.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => hterm (e + 1)))
    calc ‖∑' e : ℕ, a (e + 1) * z ^ (e + 1)‖
        ≤ ∑' e : ℕ, ‖a (e + 1) * z ^ (e + 1)‖ := norm_tsum_le_tsum_norm hsumT.norm
      _ ≤ ∑' e : ℕ, ρ ^ (e + 1) := by
          apply Summable.tsum_le_tsum (fun e => hterm (e + 1)) hsumT.norm hu'
      _ = ρ / (1 - ρ) := by
          rw [show (∑' e : ℕ, ρ ^ (e + 1)) = ρ * ∑' e : ℕ, ρ ^ e from ?_,
            tsum_geometric_of_lt_one hρ0.le hρ1, inv_eq_one_div, mul_one_div]
          rw [← tsum_mul_left]
          apply tsum_congr
          intro e
          rw [pow_succ]; ring
  have hge : 1 - ρ / (1 - ρ) ≤ ‖∑' e : ℕ, a e * z ^ e‖ := by
    rw [hshift]
    have h1 : ‖(1 : ℂ) + ∑' e : ℕ, a (e + 1) * z ^ (e + 1)‖
          + ‖∑' e : ℕ, a (e + 1) * z ^ (e + 1)‖ ≥ ‖(1 : ℂ)‖ := by
      have := norm_add_le ((1 : ℂ) + ∑' e : ℕ, a (e + 1) * z ^ (e + 1))
        (-(∑' e : ℕ, a (e + 1) * z ^ (e + 1)))
      simpa using this
    simp only [norm_one] at h1
    linarith
  have hc : 0 < 1 - ρ / (1 - ρ) := by
    rw [sub_pos, div_lt_one (by linarith : (0 : ℝ) < 1 - ρ)]
    linarith
  intro hzero
  rw [hzero, norm_zero] at hge
  linarith

lemma continuous_circle_integr (a : ℕ → ℂ) (ha0 : a 0 = 1) (hb : ∀ n, ‖a n‖ ≤ 1)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1/2) :
    Continuous (fun θ : ℝ => ‖(∑' e : ℕ, a e * (ρ * Complex.exp (θ * Complex.I)) ^ e)⁻¹‖^2) := by
  have hcont := continuous_circle_tsum a hb ρ hρ0 hρ
  have hne := circle_tsum_ne_zero a ha0 hb ρ hρ0 hρ
  exact (hcont.inv₀ hne).norm.pow 2

end Work.BMF.mrlas
