/-
# The `r`-seminorm of the low piece `tangLow` of the tangency layer

`tangLow ℓ d τ x = ∫_0^{1/2} K(τ,it) e^{-πxt} dt`, and the flatness
`Work.Asymptotics.HalfFunnel.tangKaxisFlatLow` gives `‖K(τ,it)‖ ≤ c t^n` for `t ≤ 1/2` with
*any* exponent `n ≥ 0`.  Choosing `n` larger than the requested decay exponent turns the
extra power of `t` inside the integral into the required decay in `x`:

  `‖∂_x^m tangLow τ x‖ ≤ c π^m ∫_0^{1/2} t^{n+m} e^{-πxt} dt ≤ c π^m (n+m)! / (πx)^{n+m+1}`.

For `x ≥ 1` this is at most `C (1+x)^{-N}` (because `πx ≥ 1+x` and `n + m + 1 ≥ N`), and for
`x ≤ 1` the crude bound `c π^m (1/2)^{n+m} / 2` is at most `C (1+x)^{-N}` because
`(1+x)^{-N} ≥ 2^{-N}` there.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.Asymptotics.HalfFunnel.tangKaxisFlatLow
import Submission.Work.HFN.HalfFunnel.lowBad_Phi12_deriv
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter UpperHalfPlane
open scoped Topology

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

theorem tangLowDeriv (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ m : ℕ, ∀ N : ℝ, 0 ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (x : ℝ),
      τ ∈ ctanRegion → 0 ≤ x →
      ‖iteratedDeriv m (tangLow ℓ d τ) x‖
        ≤ C * (1 + x) ^ (-N) := by
  intro m N hN
  set n : ℕ := Nat.ceil N + m + 1 with hn
  have hnN : N ≤ (n : ℝ) := by
    have h1 : N ≤ ((Nat.ceil N : ℕ) : ℝ) := Nat.le_ceil N
    have h2 : ((Nat.ceil N : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : Nat.ceil N ≤ n := by omega
      exact_mod_cast this
    linarith
  obtain ⟨c, hc0, hflat⟩ := tangKaxisFlatLow ℓ d hd (n : ℝ) (by positivity)
  set C₁ : ℝ := c * Real.pi ^ m * ((n + m).factorial : ℝ) with hC₁
  set C₂ : ℝ := c * Real.pi ^ m * (1 / 2 : ℝ) ^ (n + m) * (1 / 2) * 2 ^ N with hC₂
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  refine ⟨max C₁ C₂, le_trans hC₁0 (le_max_left _ _), fun τ x hτ hx => ?_⟩
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
  have hfuneq : tangLow ℓ d τ = fun y : ℝ => ∫ t in (0 : ℝ)..(1 / 2),
      Kaxis (Kfun ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
    funext y
    rw [tangLow]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    simp only
    congr 1
    rw [tangGauss, Complex.ofReal_exp]
    push_cast
    ring
  rw [hfuneq]
  -- the derivative formula
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc (0 : ℝ) (1 / 2))) :=
    (measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) (1 / 2))),
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ c * (1 / 2 : ℝ) ^ n := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    refine le_trans (hflat τ t hτcl ht.1 ht.2) ?_
    rw [Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2 n) hc0.le
  rw [iteratedDeriv_intervalIntegral_exp_of_bound (fun t : ℝ => Kaxis (Kfun ℓ d) τ t)
    (0 : ℝ) (1 / 2) (by norm_num) hmeas (by positivity) hbd m x]
  -- the pointwise bound on the integrand
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0 : ℝ) (1 / 2) →
      ‖Kaxis (Kfun ℓ d) τ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
          * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        ≤ c * Real.pi ^ m * (t ^ (n + m) * Real.exp (-(Real.pi * x * t))) := by
    filter_upwards with t ht
    have h1 : ‖Kaxis (Kfun ℓ d) τ t‖ ≤ c * t ^ n := by
      have := hflat τ t hτcl ht.1 ht.2
      rwa [Real.rpow_natCast] at this
    have h2 : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ m‖ = (Real.pi * t) ^ m := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
        abs_of_pos Real.pi_pos, abs_of_pos ht.1]
    have h3 : ‖(Real.exp (-(Real.pi * x * t)) : ℂ)‖ = Real.exp (-(Real.pi * x * t)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h4 : c * t ^ n * (Real.pi * t) ^ m = c * Real.pi ^ m * t ^ (n + m) := by
      rw [mul_pow, pow_add]; ring
    calc ‖Kaxis (Kfun ℓ d) τ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
          * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        = ‖Kaxis (Kfun ℓ d) τ t‖ * (Real.pi * t) ^ m
            * Real.exp (-(Real.pi * x * t)) := by rw [norm_mul, norm_mul, h2, h3]
      _ ≤ (c * t ^ n) * (Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1
              (pow_nonneg (mul_nonneg Real.pi_pos.le ht.1.le) m))
            (Real.exp_pos _).le
      _ = c * Real.pi ^ m * t ^ (n + m) * Real.exp (-(Real.pi * x * t)) := by rw [h4]
      _ = c * Real.pi ^ m * (t ^ (n + m) * Real.exp (-(Real.pi * x * t))) := by ring
  have hI₁ : ‖∫ t in (0 : ℝ)..(1 / 2), Kaxis (Kfun ℓ d) τ t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
        * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
      ≤ c * Real.pi ^ m * ∫ t in (0 : ℝ)..(1 / 2),
          t ^ (n + m) * Real.exp (-(Real.pi * x * t)) := by
    have hg : IntervalIntegrable (fun t : ℝ =>
        c * Real.pi ^ m * (t ^ (n + m) * Real.exp (-(Real.pi * x * t)))) volume 0 (1 / 2) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have hstep := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0 : ℝ))
      (b := 1 / 2) (by norm_num) hpt hg
    rw [intervalIntegral.integral_const_mul] at hstep
    exact hstep
  rcases le_or_gt 1 x with hx1 | hx1
  · -- large `x`: the Gamma bound
    have hpow := intervalIntegral_pow_mul_exp_neg_le (k := n + m) (M := (1 / 2 : ℝ))
      (c := Real.pi * x) (by norm_num) (by positivity)
    have hbase : (1 + x) ≤ Real.pi * x := by nlinarith [Real.pi_gt_three, hx1]
    have hnx : (0 : ℝ) < 1 + x := by linarith
    have hstep1 : (Real.pi * x) ^ (-(N)) ≤ (1 + x) ^ (-N) :=
      Real.rpow_le_rpow_of_nonpos hnx hbase (by linarith)
    have hstep2 : (Real.pi * x) ^ (-((n + m + 1 : ℕ) : ℝ)) ≤ (Real.pi * x) ^ (-(N)) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_pos, hx1])
        (by push_cast; linarith)
    have heq : (Real.pi * x) ^ (-(((n + m + 1 : ℕ)) : ℝ)) = ((Real.pi * x) ^ (n + m + 1))⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    have hfac : ∫ t in (0 : ℝ)..(1 / 2), t ^ (n + m) * Real.exp (-(Real.pi * x * t))
        ≤ ((n + m).factorial : ℝ) * (1 + x) ^ (-N) := by
      refine le_trans hpow ?_
      rw [div_eq_mul_inv, ← heq]
      exact mul_le_mul_of_nonneg_left (le_trans hstep2 hstep1)
        (show (0 : ℝ) ≤ ((n + m).factorial : ℝ) by positivity)
    have hfin : ‖∫ t in (0 : ℝ)..(1 / 2), Kaxis (Kfun ℓ d) τ t
          * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
          * (Real.exp (-(Real.pi * x * t)) : ℂ)‖ ≤ C₁ * (1 + x) ^ (-N) := by
      calc ‖∫ t in (0 : ℝ)..(1 / 2), Kaxis (Kfun ℓ d) τ t
            * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
          ≤ c * Real.pi ^ m * ∫ t in (0 : ℝ)..(1 / 2),
              t ^ (n + m) * Real.exp (-(Real.pi * x * t)) := hI₁
        _ ≤ c * Real.pi ^ m * (((n + m).factorial : ℝ) * (1 + x) ^ (-N)) :=
            mul_le_mul_of_nonneg_left hfac (show (0 : ℝ) ≤ c * Real.pi ^ m by positivity)
        _ = C₁ * (1 + x) ^ (-N) := by rw [hC₁]; ring
    exact le_trans hfin
      (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (Real.rpow_nonneg (by linarith) _))
  · -- small `x`: the crude constant bound
    have hcrude : ∫ t in (0 : ℝ)..(1 / 2), t ^ (n + m) * Real.exp (-(Real.pi * x * t))
        ≤ (1 / 2 : ℝ) ^ (n + m) * (1 / 2) := by
      have hle : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
          t ^ (n + m) * Real.exp (-(Real.pi * x * t)) ≤ (1 / 2 : ℝ) ^ (n + m) := by
        intro t ht
        have h1 : t ^ (n + m) ≤ (1 / 2 : ℝ) ^ (n + m) := pow_le_pow_left₀ ht.1 ht.2 _
        have h2 : Real.exp (-(Real.pi * x * t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ Real.pi * x * t :=
            mul_nonneg (mul_nonneg Real.pi_pos.le hx) ht.1
          linarith
        calc t ^ (n + m) * Real.exp (-(Real.pi * x * t)) ≤ (1 / 2 : ℝ) ^ (n + m) * 1 :=
              mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
          _ = (1 / 2 : ℝ) ^ (n + m) := mul_one _
      have h2 := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1 / 2)
        (by norm_num)
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop) hle
      rw [intervalIntegral.integral_const] at h2
      rw [smul_eq_mul] at h2
      refine le_trans h2 (le_of_eq ?_)
      ring
    have hsh : (2 : ℝ) ^ (-N) ≤ (1 + x) ^ (-N) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2N : (2 : ℝ) ^ (-N) * 2 ^ N = 1 := by
      rw [mul_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
    set D : ℝ := c * Real.pi ^ m * (1 / 2 : ℝ) ^ (n + m) * (1 / 2) with hD
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hone : (1 : ℝ) ≤ 2 ^ N * (1 + x) ^ (-N) := by
      calc (1 : ℝ) = 2 ^ N * 2 ^ (-N) := by
            rw [mul_comm, h2N]
        _ ≤ 2 ^ N * (1 + x) ^ (-N) := mul_le_mul_of_nonneg_left hsh (by positivity)
    have hfin : ‖∫ t in (0 : ℝ)..(1 / 2), Kaxis (Kfun ℓ d) τ t
          * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
          * (Real.exp (-(Real.pi * x * t)) : ℂ)‖ ≤ D := by
      have h2 : (0 : ℝ) ≤ c * Real.pi ^ m := by positivity
      calc ‖∫ t in (0 : ℝ)..(1 / 2), Kaxis (Kfun ℓ d) τ t
            * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
          ≤ c * Real.pi ^ m * ∫ t in (0 : ℝ)..(1 / 2),
              t ^ (n + m) * Real.exp (-(Real.pi * x * t)) := hI₁
        _ ≤ c * Real.pi ^ m * ((1 / 2 : ℝ) ^ (n + m) * (1 / 2)) :=
            mul_le_mul_of_nonneg_left hcrude h2
        _ = D := by rw [hD]; ring
    refine le_trans hfin (le_trans ?_
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (Real.rpow_nonneg (by linarith) _)))
    calc D = D * 1 := (mul_one D).symm
      _ ≤ D * (2 ^ N * (1 + x) ^ (-N)) := mul_le_mul_of_nonneg_left hone hD0
      _ = C₂ * (1 + x) ^ (-N) := by rw [hC₂, hD]; ring

end Work.HFN.HalfFunnel
