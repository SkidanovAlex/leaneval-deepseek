/-
# Commons: lower bound for the sum of prime reciprocals

Proves `Commons.NumberTheory.Mertens.mertens_lower`: eventually
`c · log (log X) ≤ ∑_{p ≤ X} 1/p`.

The proof is elementary via Chebyshev's linear lower bound for `θ`
(`theta_linear_lower`, from `Chebyshev.theta_ge'`), two Abel summation
identities for `∑_{p ≤ x} log p / p` and `∑_{p ≤ x} 1/p`, and exact
evaluations of the auxiliary `∫`-integrals `t⁻¹ / log t` and
`t⁻¹ / (log t)²` from Mathlib.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Finset Real Filter Asymptotics MeasureTheory
open scoped ComplexConjugate Chebyshev Topology

namespace Commons.NumberTheory.Mertens



/-- Eventually, `log t ≤ ε * √t` for any fixed `ε > 0` (as `t → ∞`). -/
lemma eventually_log_le_sqrt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, log t ≤ ε * √t := by
  have hlog : log =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    simpa using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num : 0 < (1 / 2 : ℝ)))
  have hle : ∀ᶠ t : ℝ in atTop, ‖log t‖ ≤ ε * ‖t ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_iff.mp hlog) hε
  filter_upwards [hle, eventually_ge_atTop (1 : ℝ)] with t htle ht1
  have ht0 : 0 ≤ t := by linarith
  rw [Real.norm_of_nonneg (Real.log_nonneg ht1),
    Real.norm_of_nonneg (Real.rpow_nonneg ht0 (1 / 2 : ℝ))] at htle
  simpa [Real.sqrt_eq_rpow] using htle

/-- For `t ≥ 2`, `log (t + 2) ≤ 2 * log t`. -/
lemma log_add_two_le_two_log {t : ℝ} (ht : 2 ≤ t) : log (t + 2) ≤ 2 * log t := by
  have hpos : 0 < t + 2 := by linarith
  have hsq : t + 2 ≤ t ^ 2 := by
    have hm : 0 ≤ (t - 2) * (t + 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  calc
    log (t + 2) ≤ log (t ^ 2) := Real.log_le_log hpos hsq
    _ = 2 * log t := by
      rw [Real.log_pow]
      norm_num

/-- For `t ≥ 1`, `√t ≤ t`. -/
lemma sqrt_le_self {t : ℝ} (ht : 1 ≤ t) : √t ≤ t := by
  have ht0 : 0 ≤ t := by linarith
  have hsqrt1 : 1 ≤ √t := by
    simpa using (Real.sqrt_le_sqrt ht : √(1 : ℝ) ≤ √t)
  calc
    √t = √t * 1 := by ring
    _ ≤ √t * √t := mul_le_mul_of_nonneg_left hsqrt1 (Real.sqrt_nonneg t)
    _ = (√t) ^ 2 := by ring
    _ = t := Real.sq_sqrt ht0

/-- Chebyshev's `θ` grows at least linearly, eventually: there is `0 < cθ` and
a threshold `A ≥ 2` such that `cθ * t ≤ θ t` for all `t ≥ A`. -/
lemma theta_linear_lower :
    ∃ cθ : ℝ, 0 < cθ ∧ ∃ A : ℝ, 2 ≤ A ∧
      ∀ ⦃t : ℝ⦄, A ≤ t → cθ * t ≤ Chebyshev.theta t := by
  let L : ℝ := log 2
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hev : ∀ᶠ t : ℝ in atTop, (L / 4) * t ≤ Chebyshev.theta t := by
    have hlog : ∀ᶠ t : ℝ in atTop, log t ≤ (L / 32) * √t :=
      eventually_log_le_sqrt (L / 32) (div_pos hLpos (by norm_num))
    filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with t htlog ht2
    have ht1 : 1 ≤ t := by linarith
    have hθ := Chebyshev.theta_ge' ht1
    have hb1 : log (t + 2) ≤ (L / 16) * √t := by
      calc
        log (t + 2) ≤ 2 * log t := log_add_two_le_two_log ht2
        _ ≤ 2 * ((L / 32) * √t) :=
          mul_le_mul_of_nonneg_left htlog (by norm_num : (0 : ℝ) ≤ 2)
        _ = (L / 16) * √t := by ring
    have ht0 : 0 ≤ t := by linarith
    have hb2 : 2 * √t * log t ≤ (L / 16) * t := by
      calc
        2 * √t * log t ≤ 2 * √t * ((L / 32) * √t) := by
          exact mul_le_mul_of_nonneg_left htlog (by nlinarith [Real.sqrt_nonneg t])
        _ = (L / 16) * (√t ^ 2) := by ring
        _ = (L / 16) * t := by rw [Real.sq_sqrt ht0]
    have hsum : log (t + 2) + 2 * √t * log t + L ≤
        (L / 16) * √t + (L / 16) * t + L := by
      nlinarith [hb1, hb2]
    have hsle : √t ≤ t := sqrt_le_self ht1
    have hmult : (L / 16) * √t ≤ (L / 16) * t :=
      mul_le_mul_of_nonneg_left hsle (div_nonneg hLpos.le (by norm_num))
    have hsum2 : (L / 16) * √t + (L / 16) * t + L ≤
        (L / 16) * t + (L / 16) * t + L := by
      nlinarith [hmult]
    have hfrac : 0 ≤ (5 / 8 : ℝ) * t - 1 := by nlinarith
    have hprod : 0 ≤ L * ((5 / 8 : ℝ) * t - 1) := mul_nonneg hLpos.le hfrac
    have hpoly : (L / 16) * t + (L / 16) * t + L ≤ (3 / 4 : ℝ) * L * t := by
      nlinarith
    have hErr : log (t + 2) + 2 * √t * log t + L ≤ (3 / 4 : ℝ) * L * t := by
      exact le_trans hsum (le_trans hsum2 hpoly)
    have hlin : (L / 4) * t ≤ (t - 1) * L - log (t + 2) - 2 * √t * log t := by
      nlinarith [hErr]
    exact le_trans hlin hθ
  rcases eventually_atTop.mp hev with ⟨A0, hA0⟩
  refine ⟨L / 4, div_pos hLpos (by norm_num), max 2 A0, le_max_left 2 A0, ?_⟩
  intro t ht
  exact hA0 t (le_trans (le_max_right 2 A0) ht)



/-! ## Pointwise algebraic decompositions of the integrands

Both integrands are sums/splits of `t⁻¹ / log t` and `t⁻¹ / log t ^ 2`
whenever `t ≠ 0` and `log t ≠ 0`. -/

lemma decomp_one_add {t : ℝ} (ht : t ≠ 0) (hlog : Real.log t ≠ 0) :
    (1 + Real.log t) / (t * (Real.log t) ^ 2) =
      t⁻¹ / Real.log t ^ 2 + t⁻¹ / Real.log t := by
  field_simp [ht, hlog]

lemma decomp_sub {t A : ℝ} (ht : t ≠ 0) (hlog : Real.log t ≠ 0) :
    (Real.log t - Real.log A) / (t * (Real.log t) ^ 2) =
      t⁻¹ / Real.log t - Real.log A * (t⁻¹ / Real.log t ^ 2) := by
  field_simp [ht, hlog]

/-! ## Continuity on `Icc 2 x` (for arbitrary `x`), used for `IntervalIntegrable`
certificates.  On `Icc 2 x` we have `2 ≤ t`, hence `t ≠ 0`, `1 < t`, and
`log t ≠ 0` (`log t > 0`). -/

lemma contOn_inv {x : ℝ} : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 2 x) := by
  apply continuousOn_inv₀.mono
  intro t ht
  exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)

lemma contOn_log {x : ℝ} : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc 2 x) := by
  apply continuousOn_log.mono
  intro t ht
  exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)

lemma log_ne_zero_on_Icc {x t : ℝ} (ht : t ∈ Set.Icc 2 x) : Real.log t ≠ 0 := by
  have : 1 < t := by linarith [ht.1]
  exact ne_of_gt (Real.log_pos this)

lemma contOn_log_sq {x : ℝ} : ContinuousOn (fun t : ℝ => Real.log t ^ 2) (Set.Icc 2 x) := by
  have hcmul : ContinuousOn (fun t : ℝ => Real.log t * Real.log t) (Set.Icc 2 x) :=
    (contOn_log (x := x)).mul (contOn_log (x := x))
  convert hcmul using 1
  ext t
  rw [pow_two]

lemma contOn_inv_log {x : ℝ} :
    ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.Icc 2 x) := by
  refine ContinuousOn.div₀ (contOn_inv (x := x)) (contOn_log (x := x)) ?_
  intro t ht
  exact log_ne_zero_on_Icc ht

lemma contOn_inv_log_sq {x : ℝ} :
    ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.Icc 2 x) := by
  refine ContinuousOn.div₀ (contOn_inv (x := x)) (contOn_log_sq (x := x)) ?_
  intro t ht
  exact pow_ne_zero 2 (log_ne_zero_on_Icc ht)

/-- `∫ t in 2..x, (1 + log t) / (t * (log t) ^ 2) =
     (1/log 2 − 1/log x) + (log (log x) − log (log 2))` for `2 ≤ x`. -/
lemma integral_one_add_log_div_id_log_sq {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in 2..x, (1 + Real.log t) / (t * (Real.log t) ^ 2)) =
      (1 / Real.log 2 - 1 / Real.log x) +
        (Real.log (Real.log x) - Real.log (Real.log 2)) := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hx1 : 1 < x := lt_of_lt_of_le h2 hx
  have hInt_sq : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) volume 2 x :=
    ContinuousOn.intervalIntegrable_of_Icc hx (contOn_inv_log_sq (x := x))
  have hInt_log : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume 2 x :=
    ContinuousOn.intervalIntegrable_of_Icc hx (contOn_inv_log (x := x))
  calc
    (∫ t in 2..x, (1 + Real.log t) / (t * (Real.log t) ^ 2))
        = ∫ t in 2..x, (t⁻¹ / Real.log t ^ 2 + t⁻¹ / Real.log t) := by
            refine intervalIntegral.integral_congr_Ioo_of_le hx ?_
            intro t ht
            have ht0 : t ≠ 0 := by
              have : (0 : ℝ) < t := lt_trans (by norm_num) (Set.mem_Ioo.mp ht).1
              exact ne_of_gt this
            have hlog : Real.log t ≠ 0 := by
              have : 1 < t := by linarith [Set.mem_Ioo.mp ht |>.1]
              exact ne_of_gt (Real.log_pos this)
            exact decomp_one_add ht0 hlog
    _ = (∫ t in 2..x, t⁻¹ / Real.log t ^ 2) + (∫ t in 2..x, t⁻¹ / Real.log t) := by
            rw [intervalIntegral.integral_add hInt_sq hInt_log]
    _ = (1 / Real.log 2 - 1 / Real.log x) +
          (Real.log (Real.log x) - Real.log (Real.log 2)) := by
            rw [integral_inv_div_log_sq h2 hx1, integral_inv_div_log h2 hx1]
            ring

/-- `∫ t in A..x, (log t − log A) / (t * (log t)^2) =
     (log(log x) − log(log A)) − log A * (1/log A − 1/log x)` for `2 ≤ A ≤ x`. -/
lemma integral_log_sub_logA_div_id_log_sq {x A : ℝ} (hA : 2 ≤ A) (hAx : A ≤ x) :
    (∫ t in A..x, (Real.log t - Real.log A) / (t * (Real.log t) ^ 2)) =
      (Real.log (Real.log x) - Real.log (Real.log A)) -
        Real.log A * (1 / Real.log A - 1 / Real.log x) := by
  have hA1 : (1 : ℝ) < A := lt_of_lt_of_le (by norm_num) hA
  have hx1 : 1 < x := lt_of_lt_of_le hA1 hAx
  have h2x : 2 ≤ x := le_trans hA hAx
  have hcontA_sq : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.Icc A x) := by
    apply (contOn_inv_log_sq (x := x)).mono
    intro t ht
    exact Set.mem_Icc.mpr ⟨by linarith [ht.1, hA], ht.2⟩
  have hcontA_log : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.Icc A x) := by
    apply (contOn_inv_log (x := x)).mono
    intro t ht
    exact Set.mem_Icc.mpr ⟨by linarith [ht.1, hA], ht.2⟩
  have hInt_sqA : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) volume A x :=
    ContinuousOn.intervalIntegrable_of_Icc hAx hcontA_sq
  have hInt_logA : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume A x :=
    ContinuousOn.intervalIntegrable_of_Icc hAx hcontA_log
  have hInt_mul : IntervalIntegrable (fun t : ℝ => Real.log A * (t⁻¹ / Real.log t ^ 2)) volume A x :=
    hInt_sqA.const_mul (Real.log A)
  calc
    (∫ t in A..x, (Real.log t - Real.log A) / (t * (Real.log t) ^ 2))
        = ∫ t in A..x, (t⁻¹ / Real.log t - Real.log A * (t⁻¹ / Real.log t ^ 2)) := by
            refine intervalIntegral.integral_congr_Ioo_of_le hAx ?_
            intro t ht
            have htA : A < t := (Set.mem_Ioo.mp ht).1
            have h1t : 1 < t := lt_of_lt_of_le hA1 (le_of_lt htA)
            have ht0 : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) h1t)
            have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos h1t)
            exact decomp_sub ht0 hlog
    _ = (∫ t in A..x, t⁻¹ / Real.log t) - (∫ t in A..x, Real.log A * (t⁻¹ / Real.log t ^ 2)) := by
            rw [intervalIntegral.integral_sub hInt_logA hInt_mul]
    _ = (Real.log (Real.log x) - Real.log (Real.log A)) -
          Real.log A * (1 / Real.log A - 1 / Real.log x) := by
            rw [intervalIntegral.integral_const_mul]
            rw [integral_inv_div_log hA1 hx1, integral_inv_div_log_sq hA1 hx1]
            ring



/-- The sum of prime reciprocals up to `X` (workspace convention). -/
noncomputable def primeRecips (X : ℝ) : ℝ :=
  ∑ p ∈ (⌊X⌋₊).primesLE, (1 : ℝ) / p

/-- `Σ_{p ≤ x} log p / p`. -/
noncomputable def logDiv (x : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, Real.log p / p

/-- `primeRecips` is monotone. -/
lemma primeRecips_mono : Monotone primeRecips := by
  intro x y hxy
  unfold primeRecips
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  have hfloor : (⌊x⌋₊ : ℕ) ≤ ⌊y⌋₊ := by
    exact_mod_cast (Nat.floor_mono hxy)
  exact ⟨le_trans hp.1 hfloor, hp.2⟩

lemma logDiv_nonneg (x : ℝ) : 0 ≤ logDiv x := by
  unfold logDiv
  exact sum_nonneg (fun p hp => div_nonneg (log_nonneg (by
    have hp' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2)
    linarith)) (Nat.cast_nonneg p))

/-- Cumulative sum of `indicator {p | p.Prime} (fun n ↦ log n)` equals `θ`. -/
lemma theta_eq_sum_cumulative (x : ℝ) :
    (∑ k ∈ Icc 0 ⌊x⌋₊,
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n) k) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc x]
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_filter]

/-- Cumulative sum of `indicator {p | p.Prime} (fun n ↦ log n / n)` equals `logDiv`. -/
lemma logDiv_eq_sum_cumulative (x : ℝ) :
    (∑ k ∈ Icc 0 ⌊x⌋₊,
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n / (n : ℝ)) k) = logDiv x := by
  unfold logDiv
  rw [Nat.primesLE_eq_filter_Icc_zero]
  rw [sum_filter]
  congr 1
  ext k
  by_cases h : k.Prime
  · simp [h]
  · simp [h]

/-- Rewriting `logDiv x` as a sum over `Icc 0 ⌊x⌋₊` with an indicator. -/
lemma logDiv_eq_sum_mul {x : ℝ} :
    logDiv x = ∑ n ∈ Icc 0 ⌊x⌋₊,
      (n : ℝ)⁻¹ * Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n) n := by
  unfold logDiv
  rw [Nat.primesLE_eq_filter_Icc_zero]
  rw [sum_filter]
  congr 1
  ext n
  by_cases h : n.Prime
  · simp [h, div_eq_mul_inv, mul_comm]
  · simp [h]

/-- Rewriting `primeRecips x` as a sum over `Icc 0 ⌊x⌋₊` with an indicator. -/
lemma primeRecips_eq_sum_mul {x : ℝ} :
    primeRecips x = ∑ n ∈ Icc 0 ⌊x⌋₊,
      (Real.log n)⁻¹ * Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n / (n : ℝ)) n := by
  unfold primeRecips
  rw [Nat.primesLE_eq_filter_Icc_zero]
  rw [sum_filter]
  congr 1
  ext n
  by_cases h : n.Prime
  · have hlog : Real.log (n : ℝ) ≠ 0 := by
      apply log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (Nat.Prime.pos h)
      · exact_mod_cast (Nat.Prime.ne_one h)
    simp [h]
    field_simp [hlog]
  · simp [h]

set_option backward.isDefEq.respectTransparency.types false in
/-- First Abel identity: `Σ_{p ≤ x} log p / p = θ(x)/x + ∫_2^x θ(t)/t² dt`. -/
theorem logDiv_eq_theta_div_add_integral {x : ℝ} (hx : 2 ≤ x) :
    logDiv x = Chebyshev.theta x / x + ∫ t in 2..x, Chebyshev.theta t / (t * t) := by
  let a : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (↑n)⁻¹ * a n
  · rw [logDiv_eq_sum_mul]
  · rw [sum_mul_eq_sub_integral_mul₁ a (f := fun t : ℝ ↦ t⁻¹) (by simp [a])
      (by simp [a]), ← intervalIntegral.integral_of_le hx]
    · have hcumu (u : ℝ) : (∑ k ∈ Icc 0 ⌊u⌋₊, a k) = Chebyshev.theta u := by
        simpa [a] using theta_eq_sum_cumulative u
      have int_deriv :
          ∫ u in 2..x, deriv (fun t : ℝ ↦ t⁻¹) u * (∑ k ∈ Icc 0 ⌊u⌋₊, a k) =
          ∫ u in 2..x, (∑ k ∈ Icc 0 ⌊u⌋₊, a k) * -((u : ℝ) ^ 2)⁻¹ :=
        intervalIntegral.integral_congr fun u _ ↦ by rw [deriv_inv]; ring
      rw [int_deriv]
      simp_rw [hcumu]
      have hid : ∫ u in 2..x, Chebyshev.theta u * -((u : ℝ) ^ 2)⁻¹ =
          -∫ u in 2..x, Chebyshev.theta u * ((u : ℝ) ^ 2)⁻¹ := by
        rw [← intervalIntegral.integral_neg]
        congr 1
        ext u
        ring
      rw [hid]
      rw [sub_neg_eq_add]
      congr 1
      · ring
      · apply intervalIntegral.integral_congr
        intro t ht
        have ht2 : 2 ≤ t := by
          rw [Set.uIcc_of_le hx] at ht
          exact ht.1
        have ht0 : t ≠ 0 := by linarith
        field_simp [ht0, mul_comm]
    · intro z hz
      have hz0 : z ≠ 0 := by linarith [hz.1]
      exact differentiableAt_inv hz0
    · refine ContinuousOn.integrableOn_Icc ?_
      intro z hz
      have hz0 : z ≠ 0 := by linarith [hz.1]
      simp only [deriv_inv']
      fun_prop (disch := positivity)

set_option backward.isDefEq.respectTransparency.types false in

set_option backward.isDefEq.respectTransparency.types false in
/-- Second Abel identity: `Σ_{p ≤ x} 1/p = logDiv(x)/log x + ∫_2^x logDiv(t)/(t log²t) dt`. -/
theorem primeRecips_eq_logDiv_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    primeRecips x = logDiv x / Real.log x + ∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2) := by
  let b : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n / (n : ℝ))
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * b n
  · rw [primeRecips_eq_sum_mul]
  · rw [sum_mul_eq_sub_integral_mul₁ b (f := fun t : ℝ ↦ (Real.log t)⁻¹) (by simp [b])
      (by simp [b]), ← intervalIntegral.integral_of_le hx]
    · have hcumu (u : ℝ) : (∑ k ∈ Icc 0 ⌊u⌋₊, b k) = logDiv u := by
        simpa [b] using logDiv_eq_sum_cumulative u
      have int_deriv :
          ∫ u in 2..x, deriv (fun t : ℝ ↦ (Real.log t)⁻¹) u * (∑ k ∈ Icc 0 ⌊u⌋₊, b k) =
          ∫ u in 2..x, (∑ k ∈ Icc 0 ⌊u⌋₊, b k) * -((u : ℝ) * (Real.log u) ^ 2)⁻¹ :=
        intervalIntegral.integral_congr fun u _ ↦ by rw [deriv_inv_log_apply]; simp [field]
      rw [int_deriv]
      simp_rw [hcumu]
      have hid : ∫ u in 2..x, logDiv u * -((u : ℝ) * (Real.log u) ^ 2)⁻¹ =
          -∫ u in 2..x, logDiv u * ((u : ℝ) * (Real.log u) ^ 2)⁻¹ := by
        rw [← intervalIntegral.integral_neg]
        congr 1
        ext u
        ring
      rw [hid]
      rw [sub_neg_eq_add]
      congr 1
      rw [div_eq_mul_inv]
      ring
    · intro z hz
      have hz0 : z ≠ 0 := by linarith [hz.1]
      have hz1 : z ≠ 1 := by linarith [hz.1]
      have hz_1 : z ≠ -1 := by linarith [hz.1]
      exact differentiableAt_inv_log hz0 hz1 hz_1
    · refine ContinuousOn.integrableOn_Icc fun z hz ↦ ContinuousWithinAt.congr ?_
        (fun _ _ ↦ deriv_inv_log_apply) deriv_inv_log_apply
      have hz0 : z ≠ 0 := by linarith [hz.1]
      have hz2 : (Real.log z) ^ 2 ≠ 0 := by
        refine pow_ne_zero 2 ?_
        apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
      exact ContinuousAt.continuousWithinAt <| by fun_prop


section MertensBounds

/-! ## Bounds from Chebyshev's two-sided θ estimates -/

/-- Integrability of `θ t / (t * t)` on `[2, x]`. -/
lemma integrableOn_theta_div_id_sq (x : ℝ) :
    IntegrableOn (fun t ↦ Chebyshev.theta t / (t * t)) (Set.Icc 2 x) volume := by
  let a : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n)
  have hfun : (fun t : ℝ ↦ Chebyshev.theta t / (t * t))
      = fun t : ℝ ↦ (t * t)⁻¹ * (∑ k ∈ Icc 0 ⌊t⌋₊, a k) := by
    funext t
    rw [← theta_eq_sum_cumulative t]
    simp [a, div_eq_mul_inv, mul_comm]
  rw [hfun]
  refine integrableOn_mul_sum_Icc (c := a) (a := 2) (b := x) (by norm_num)
    (g := fun t : ℝ ↦ (t * t)⁻¹) ?_
  refine ContinuousOn.integrableOn_Icc ?_
  intro z hz
  have hz0 : z ≠ 0 := by linarith [hz.1]
  fun_prop (disch := positivity)

/-- Integrability of `logDiv t / (t * log t ^ 2)` on `[2, x]`. -/
lemma integrableOn_logDiv_div_id_log_sq (x : ℝ) :
    IntegrableOn (fun t ↦ logDiv t / (t * (Real.log t) ^ 2)) (Set.Icc 2 x) volume := by
  let b : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n / (n : ℝ))
  have hfun : (fun t : ℝ ↦ logDiv t / (t * (Real.log t) ^ 2))
      = fun t : ℝ ↦ (t * (Real.log t) ^ 2)⁻¹ * (∑ k ∈ Icc 0 ⌊t⌋₊, b k) := by
    funext t
    rw [← logDiv_eq_sum_cumulative t]
    simp [b, div_eq_mul_inv, mul_comm, div_eq_mul_inv]
  rw [hfun]
  refine integrableOn_mul_sum_Icc (c := b) (a := 2) (b := x) (by norm_num)
    (g := fun t : ℝ ↦ (t * (Real.log t) ^ 2)⁻¹) ?_
  refine ContinuousOn.integrableOn_Icc ?_
  intro z hz
  have hz0 : z ≠ 0 := by linarith [hz.1]
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
  fun_prop (disch := positivity)

/-- `IntervalIntegrable` version for `logDiv t/(t log²t)` when `2 ≤ x`. -/
lemma intervalIntegrable_logDiv_div_id_log_sq {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ logDiv t / (t * (Real.log t) ^ 2)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact integrableOn_logDiv_div_id_log_sq x

/-- `IntervalIntegrable` version for `θ t/(t·t)` when `2 ≤ x`. -/
lemma intervalIntegrable_theta_div_id_sq {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * t)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact integrableOn_theta_div_id_sq x

/-- `1/t` is interval-integrable on `[2, x]`. -/
lemma intervalIntegrable_inv_id {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ (t : ℝ)⁻¹) volume 2 x := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := by
    rw [Set.uIcc_of_le hx] at hz
    exact hz.1
  have hz0 : z ≠ 0 := by linarith
  fun_prop (disch := positivity)

/-- `(1 + log t)/(t log²t)` is interval-integrable on `[2,x]`. -/
lemma intervalIntegrable_one_add_log_div_id_log_sq {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ (1 + Real.log t) / (t * (Real.log t) ^ 2)) volume 2 x := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := by
    rw [Set.uIcc_of_le hx] at hz
    exact hz.1
  have hz0 : z ≠ 0 := by linarith
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  fun_prop (disch := positivity)

/-- Upper bound for `logDiv` from Chebyshev's upper bound for `θ`: `logDiv x ≤ log 4·(1 + log x)`. -/
lemma logDiv_le_log4_mul_one_add_log {x : ℝ} (hx : 2 ≤ x) :
    logDiv x ≤ Real.log 4 * (1 + Real.log x) := by
  rw [logDiv_eq_theta_div_add_integral hx]
  have hx0 : 0 < x := by linarith
  have hb : Chebyshev.theta x / x ≤ Real.log 4 := by
    have hle := Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ x)
    rwa [div_le_iff₀ hx0]
  have hint : (∫ t in 2..x, Chebyshev.theta t / (t * t)) ≤ Real.log 4 * (Real.log x - Real.log 2) := by
    have hmono : (∫ t in 2..x, Chebyshev.theta t / (t * t)) ≤
        ∫ t in 2..x, Real.log 4 * (t : ℝ)⁻¹ := by
      refine intervalIntegral.integral_mono_on hx (intervalIntegrable_theta_div_id_sq hx)
        ((intervalIntegrable_inv_id hx).const_mul _) ?_
      intro t ht
      have ht2 : 2 ≤ t := ht.1
      have ht0 : 0 < t := by linarith
      have hle := Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ t)
      have hle' : Chebyshev.theta t * (t * t)⁻¹ ≤ Real.log 4 * t * (t * t)⁻¹ :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      calc
        Chebyshev.theta t / (t * t) = Chebyshev.theta t * (t * t)⁻¹ := by field_simp [ht0.ne']
        _ ≤ Real.log 4 * t * (t * t)⁻¹ := hle'
        _ = Real.log 4 * (t : ℝ)⁻¹ := by
          have ht0' : (t * t) ≠ 0 := by positivity
          field_simp [ht0.ne', ht0']
    calc
      (∫ t in 2..x, Chebyshev.theta t / (t * t)) ≤ ∫ t in 2..x, Real.log 4 * (t : ℝ)⁻¹ := hmono
      _ = Real.log 4 * (∫ t in 2..x, (t : ℝ)⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.log 4 * (Real.log x - Real.log 2) := by
        congr 1
        rw [integral_inv_of_pos (by norm_num) hx0]
        rw [Real.log_div (ne_of_gt hx0) (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    Chebyshev.theta x / x + (∫ t in 2..x, Chebyshev.theta t / (t * t))
        ≤ Real.log 4 + Real.log 4 * (Real.log x - Real.log 2) := by
      nlinarith [hb, hint]
    _ ≤ Real.log 4 * (1 + Real.log x) := by
      have hlog2 : 0 ≤ Real.log 2 := by exact log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have hlog4 : 0 ≤ Real.log 4 := by exact log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      have hprod : 0 ≤ Real.log 4 * Real.log 2 := mul_nonneg hlog4 hlog2
      nlinarith



/-- Generic interval-integrability for `θ t/(t·t)` over `[a,b]`, `2 ≤ a ≤ b`. -/
lemma intervalIntegrable_theta_div_id_sq_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * t)) volume a b := by
  have hfun : (fun t : ℝ ↦ Chebyshev.theta t / (t * t))
      = fun t : ℝ ↦ (t * t)⁻¹ * Chebyshev.theta t := by
    funext t
    field_simp [div_eq_mul_inv, mul_comm]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  rw [hfun]
  -- express θ via cumulative sums
  let aa : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n)
  have hfun2 : (fun t : ℝ ↦ (t * t)⁻¹ * Chebyshev.theta t)
      = fun t : ℝ ↦ (t * t)⁻¹ * (∑ k ∈ Icc 0 ⌊t⌋₊, aa k) := by
    funext t
    rw [← theta_eq_sum_cumulative t]
  rw [hfun2]
  refine integrableOn_mul_sum_Icc (c := aa) (a := a) (b := b) (by linarith : 0 ≤ a) ?_
  refine ContinuousOn.integrableOn_Icc ?_
  intro z hz
  have hz2 : 2 ≤ z := le_trans ha hz.1
  have hz0 : z ≠ 0 := by linarith
  fun_prop (disch := positivity)

/-- Generic interval-integrability for `logDiv t/(t·(logt)^2)` over `[a,b]`, `2 ≤ a ≤ b`. -/
lemma intervalIntegrable_logDiv_div_id_log_sq_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ logDiv t / (t * (Real.log t) ^ 2)) volume a b := by
  have hfun : (fun t : ℝ ↦ logDiv t / (t * (Real.log t) ^ 2))
      = fun t : ℝ ↦ (t * (Real.log t) ^ 2)⁻¹ * logDiv t := by
    funext t
    field_simp [div_eq_mul_inv, mul_comm]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  rw [hfun]
  let bb : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ Real.log n / (n : ℝ))
  have hfun2 : (fun t : ℝ ↦ (t * (Real.log t) ^ 2)⁻¹ * logDiv t)
      = fun t : ℝ ↦ (t * (Real.log t) ^ 2)⁻¹ * (∑ k ∈ Icc 0 ⌊t⌋₊, bb k) := by
    funext t
    rw [← logDiv_eq_sum_cumulative t]
  rw [hfun2]
  refine integrableOn_mul_sum_Icc (c := bb) (a := a) (b := b) (by linarith : 0 ≤ a) ?_
  refine ContinuousOn.integrableOn_Icc ?_
  intro z hz
  have hz2 : 2 ≤ z := le_trans ha hz.1
  have hz0 : z ≠ 0 := by linarith
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  fun_prop (disch := positivity)

/-- Generic interval-integrability for `1/t` over `[a,b]`, `2 ≤ a ≤ b`. -/
lemma intervalIntegrable_inv_id_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ (t : ℝ)⁻¹) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := by
    rw [Set.uIcc_of_le hab] at hz
    exact le_trans ha hz.1
  have hz0 : z ≠ 0 := by linarith
  fun_prop (disch := positivity)

/-- Generic interval-integrability for `(1+logt)/(t·log²t)` over `[a,b]`, `2 ≤ a ≤ b`. -/
lemma intervalIntegrable_one_add_log_div_id_log_sq_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ (1 + Real.log t) / (t * (Real.log t) ^ 2)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := by
    rw [Set.uIcc_of_le hab] at hz
    exact le_trans ha hz.1
  have hz0 : z ≠ 0 := by linarith
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  fun_prop (disch := positivity)

/-- Exact upper bound for `primeRecips` (before constant simplification). -/
lemma primeRecips_le_log4_mul_loglog_add {x : ℝ} (hx : 2 ≤ x) :
    primeRecips x ≤ Real.log 4 * Real.log (Real.log x) + Real.log 4 * (1 + 2 / Real.log 2) := by
  rw [primeRecips_eq_logDiv_div_log_add_integral hx]
  have hlogx : 0 < Real.log x := by
    exact log_pos (by linarith : (1 : ℝ) < x)
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx
  have hlog2_ne : Real.log 2 ≠ 0 := by positivity
  have hbnd : logDiv x / Real.log x ≤ Real.log 4 * (1 + 1 / Real.log x) := by
    have hle := logDiv_le_log4_mul_one_add_log hx
    have hd : logDiv x / Real.log x ≤ Real.log 4 * (1 + Real.log x) / Real.log x :=
      div_le_div_of_nonneg_right hle (le_of_lt hlogx)
    have hd' : Real.log 4 * (1 + Real.log x) / Real.log x =
        Real.log 4 * (1 + 1 / Real.log x) := by
      field_simp [hlogx_ne]
      ring
    rw [← hd']
    exact hd
  have hmain : (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) ≤
      Real.log 4 * ((1 / Real.log 2 - 1 / Real.log x) +
        (Real.log (Real.log x) - Real.log (Real.log 2))) := by
    have hmono : (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) ≤
        ∫ t in 2..x, Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := by
      refine intervalIntegral.integral_mono_on hx (intervalIntegrable_logDiv_div_id_log_sq hx)
        ((intervalIntegrable_one_add_log_div_id_log_sq hx).const_mul _) ?_
      intro t ht
      have ht2 : 2 ≤ t := ht.1
      have hle := logDiv_le_log4_mul_one_add_log ht2
      have hpos : 0 < t * (Real.log t) ^ 2 := by
        have hlog0 : 0 < Real.log t := by exact log_pos (by linarith : (1 : ℝ) < t)
        positivity
      have hd : logDiv t / (t * (Real.log t) ^ 2) ≤
          Real.log 4 * (1 + Real.log t) / (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right hle (le_of_lt hpos)
      have hd' : Real.log 4 * (1 + Real.log t) / (t * (Real.log t) ^ 2) =
          Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := by
        field_simp
      rw [← hd']
      exact hd
    calc
      (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) ≤
          ∫ t in 2..x, Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := hmono
      _ = Real.log 4 * (∫ t in 2..x, (1 + Real.log t) / (t * (Real.log t) ^ 2)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.log 4 * ((1 / Real.log 2 - 1 / Real.log x) +
          (Real.log (Real.log x) - Real.log (Real.log 2))) := by
        rw [integral_one_add_log_div_id_log_sq hx]
  calc
    logDiv x / Real.log x + (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) ≤
        Real.log 4 * (1 + 1 / Real.log x) + Real.log 4 * ((1 / Real.log 2 - 1 / Real.log x) +
          (Real.log (Real.log x) - Real.log (Real.log 2))) := by
      linarith
    _ = Real.log 4 * Real.log (Real.log x) + Real.log 4 * (1 + 1 / Real.log 2 - Real.log (Real.log 2)) := by
      field_simp [hlogx_ne, hlog2_ne]
      ring
    _ ≤ Real.log 4 * Real.log (Real.log x) + Real.log 4 * (1 + 2 / Real.log 2) := by
      have hn : -Real.log (Real.log 2) ≤ 1 / Real.log 2 := by
        have hu : 0 < 1 / Real.log 2 := by positivity
        have hlogu : Real.log (1 / Real.log 2) ≤ 1 / Real.log 2 := by
          have hle := Real.log_le_sub_one_of_pos hu
          nlinarith
        simpa [one_div] using hlogu
      have h4 : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 4))
      have hred : (1 + 1 / Real.log 2 - Real.log (Real.log 2) : ℝ) ≤ 1 + 2 / Real.log 2 := by
        field_simp [hlog2_ne] at hn ⊢
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hred h4]

/-- `Real.log 3 > 1`, numerically. -/
lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  have h := Real.log_three_gt_d9
  norm_num at h
  linarith

/-- `log log x ≥ 0` for `x ≥ 3`. -/
lemma log_log_nonneg_of_three_le {x : ℝ} (hx : 3 ≤ x) : 0 ≤ Real.log (Real.log x) := by
  have hlog3 : (1 : ℝ) < Real.log 3 := log_three_gt_one
  have hlogx : (1 : ℝ) < Real.log x := lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith))
  have hlogxpos : 0 < Real.log x := by linarith
  have hz : (0 : ℝ) < Real.log (Real.log x) := by
    simpa using (Real.log_lt_log zero_lt_one hlogx)
  exact le_of_lt hz

/-- `mertens_upper`, the main upper bound. -/
theorem mertens_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      primeRecips X ≤ C * (Real.log (Real.log X) + 1) := by
  refine ⟨Real.log 4 * (2 + 2 / Real.log 2), ?pos, ?main⟩
  · have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  · intro X hX3
    have hX2 : 2 ≤ X := by linarith
    have hle := primeRecips_le_log4_mul_loglog_add hX2
    have hlog4n : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 4))
    have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hloglog : 0 ≤ Real.log (Real.log X) := log_log_nonneg_of_three_le hX3
    have hlast : Real.log 4 * Real.log (Real.log X) + Real.log 4 * (1 + 2 / Real.log 2) ≤
        (Real.log 4 * (2 + 2 / Real.log 2)) * (Real.log (Real.log X) + 1) := by
      have h2 : 0 ≤ 1 + 2 / Real.log 2 := by positivity
      have hp : 0 ≤ Real.log 4 * (1 + 2 / Real.log 2) * Real.log (Real.log X) := by
        exact mul_nonneg (mul_nonneg hlog4n h2) hloglog
      field_simp [ne_of_gt hlog2p]
      nlinarith [hlog4n, hloglog, hp]
    exact le_trans hle hlast

end MertensBounds


section LowerBounds

/-! ## The lower bound for `primeRecips`, eventually of size `log log x` -/


/-- `θ t / (t * t)`-type integral lower bound for `logDiv`:
if `θ t ≥ cθ * t` for `t ∈ [A, x]` then `logDiv x ≥ cθ * (log x - log A)`. -/
lemma logDiv_ge_cθ_mul_log_sub {x A cθ : ℝ} (hx : 2 ≤ x) (hA : 2 ≤ A) (hAx : A ≤ x)
    (hcθ : 0 ≤ cθ) (hθ : ∀ ⦃t : ℝ⦄, A ≤ t → cθ * t ≤ Chebyshev.theta t) :
    cθ * (Real.log x - Real.log A) ≤ logDiv x := by
  rw [logDiv_eq_theta_div_add_integral hx]
  have hx0 : 0 < x := by linarith
  have hA0 : 0 < A := by linarith
  -- 1) lower bound of the integral over [A,x]
  have hpiece : cθ * (Real.log x - Real.log A) ≤ ∫ t in A..x, Chebyshev.theta t / (t * t) := by
    have hint1 : (∫ t in A..x, (t : ℝ)⁻¹) = Real.log x - Real.log A := by
      rw [integral_inv_of_pos hA0 hx0]
      rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hA0)]
    have hmono : (∫ t in A..x, cθ * (t : ℝ)⁻¹) ≤
        ∫ t in A..x, Chebyshev.theta t / (t * t) := by
      refine intervalIntegral.integral_mono_on hAx
        ((intervalIntegrable_inv_id_gen hA hAx).const_mul cθ)
        (intervalIntegrable_theta_div_id_sq_gen hA hAx) ?_
      intro t ht
      have htA : A ≤ t := ht.1
      have ht0 : 0 < t := by linarith
      have hle := hθ htA
      have hd : cθ * t / (t * t) ≤ Chebyshev.theta t / (t * t) :=
        div_le_div_of_nonneg_right hle (by positivity)
      have hd' : cθ * t / (t * t) = cθ * (t : ℝ)⁻¹ := by
        field_simp [ne_of_gt ht0]
      rw [← hd']
      exact hd
    calc
      cθ * (Real.log x - Real.log A) = cθ * (∫ t in A..x, (t : ℝ)⁻¹) := by rw [hint1]
      _ = (∫ t in A..x, cθ * (t : ℝ)⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ t in A..x, Chebyshev.theta t / (t * t) := hmono
  -- 2) integral over [A,x] is bounded by the whole integral and θ x/x ≥ 0
  have hAint : 0 ≤ ∫ t in 2..A, Chebyshev.theta t / (t * t) := by
    refine intervalIntegral.integral_nonneg (by linarith : (2 : ℝ) ≤ A) ?_
    intro u hu
    have hu1 : 2 ≤ u := hu.1
    have hden : 0 < u * u := by positivity
    exact div_nonneg (Chebyshev.theta_nonneg u) (le_of_lt hden)
  have hnonneg : 0 ≤ Chebyshev.theta x / x := by
    have hx2 : 0 < x := by linarith
    exact div_nonneg (Chebyshev.theta_nonneg x) (le_of_lt hx2)
  have hsplit : (∫ t in A..x, Chebyshev.theta t / (t * t)) +
      (∫ t in 2..A, Chebyshev.theta t / (t * t)) = ∫ t in 2..x, Chebyshev.theta t / (t * t) := by
    have h1 : IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * t)) volume 2 A :=
      intervalIntegrable_theta_div_id_sq_gen (by norm_num) (by linarith : (2 : ℝ) ≤ A)
    have h2 : IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * t)) volume A x :=
      intervalIntegrable_theta_div_id_sq_gen hA hAx
    simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals h1 h2
  calc
    cθ * (Real.log x - Real.log A) ≤ ∫ t in A..x, Chebyshev.theta t / (t * t) := hpiece
    _ ≤ (∫ t in A..x, Chebyshev.theta t / (t * t)) + (∫ t in 2..A, Chebyshev.theta t / (t * t)) := by
      linarith
    _ = ∫ t in 2..x, Chebyshev.theta t / (t * t) := hsplit
    _ ≤ Chebyshev.theta x / x + (∫ t in 2..x, Chebyshev.theta t / (t * t)) := by linarith

/-- A linear lower bound on `logDiv` on `[A, x]` implies a `log log` lower bound
for `primeRecips`. -/
lemma primeRecips_ge_cθ_mul_loglog {x A cθ : ℝ} (hx : 2 ≤ x) (hA : 2 ≤ A) (hAx : A ≤ x)
    (hcθ : 0 ≤ cθ)
    (hlogDiv : ∀ ⦃t : ℝ⦄, A ≤ t → cθ * (Real.log t - Real.log A) ≤ logDiv t) :
    cθ * (Real.log (Real.log x) - Real.log (Real.log A) - 1) ≤ primeRecips x := by
  rw [primeRecips_eq_logDiv_div_log_add_integral hx]
  have hlogA : 0 < Real.log A := by exact log_pos (by linarith : (1 : ℝ) < A)
  have hlogA_ne : Real.log A ≠ 0 := ne_of_gt hlogA
  have hlogx : 0 < Real.log x := by exact log_pos (by linarith : (1 : ℝ) < x)
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx
  have hintA : 0 ≤ ∫ t in 2..A, logDiv t / (t * (Real.log t) ^ 2) := by
    refine intervalIntegral.integral_nonneg (by linarith : (2 : ℝ) ≤ A) ?_
    intro u hu
    have hu1 : 2 ≤ u := hu.1
    have hlogu0 : 0 < Real.log u := by exact log_pos (by linarith : (1 : ℝ) < u)
    have hden : 0 < u * (Real.log u) ^ 2 := by positivity
    exact div_nonneg (logDiv_nonneg u) (le_of_lt hden)
  have hvalbound : cθ * ((Real.log (Real.log x) - Real.log (Real.log A)) -
        Real.log A * (1 / Real.log A - 1 / Real.log x)) ≤
      ∫ t in A..x, logDiv t / (t * (Real.log t) ^ 2) := by
    have hmono' : (∫ t in A..x, cθ * ((Real.log t - Real.log A) / (t * (Real.log t) ^ 2))) ≤
        ∫ t in A..x, logDiv t / (t * (Real.log t) ^ 2) := by
      refine intervalIntegral.integral_mono_on hAx ?hf ?hg ?_
      · refine ContinuousOn.intervalIntegrable ?_
        intro z hz
        have hzA : A ≤ z := by
          rw [Set.uIcc_of_le hAx] at hz
          exact hz.1
        have hz0 : 0 < z := by linarith
        have hlogz0 : Real.log z ≠ 0 := by
          apply log_ne_zero_of_pos_of_ne_one <;> linarith [hzA]
        fun_prop (disch := positivity)
      · exact intervalIntegrable_logDiv_div_id_log_sq_gen hA hAx
      · intro t ht
        have htA : A ≤ t := ht.1
        have ht0 : 0 < t := by linarith
        have hlogt0 : 0 < Real.log t := by exact log_pos (by linarith : (1 : ℝ) < t)
        have hle := hlogDiv htA
        have hd : cθ * (Real.log t - Real.log A) / (t * (Real.log t) ^ 2) ≤
            logDiv t / (t * (Real.log t) ^ 2) :=
          div_le_div_of_nonneg_right hle (by positivity)
        have hd' : cθ * (Real.log t - Real.log A) / (t * (Real.log t) ^ 2) =
            cθ * ((Real.log t - Real.log A) / (t * (Real.log t) ^ 2)) := by
          field_simp
        rw [← hd']
        exact hd
    have hconst : (∫ t in A..x, cθ * ((Real.log t - Real.log A) / (t * (Real.log t) ^ 2))) =
        cθ * ((Real.log (Real.log x) - Real.log (Real.log A)) -
          Real.log A * (1 / Real.log A - 1 / Real.log x)) := by
      rw [intervalIntegral.integral_const_mul]
      rw [integral_log_sub_logA_div_id_log_sq hA hAx]
    exact hconst.symm.trans_le hmono'
  have hsplit : (∫ t in A..x, logDiv t / (t * (Real.log t) ^ 2)) +
      (∫ t in 2..A, logDiv t / (t * (Real.log t) ^ 2)) = ∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2) := by
    have h1 : IntervalIntegrable (fun t ↦ logDiv t / (t * (Real.log t) ^ 2)) volume 2 A :=
      intervalIntegrable_logDiv_div_id_log_sq_gen (by norm_num) (by linarith : (2 : ℝ) ≤ A)
    have h2 : IntervalIntegrable (fun t ↦ logDiv t / (t * (Real.log t) ^ 2)) volume A x :=
      intervalIntegrable_logDiv_div_id_log_sq_gen hA hAx
    simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hnonneg : 0 ≤ logDiv x / Real.log x := by
    exact div_nonneg (logDiv_nonneg x) (le_of_lt hlogx)
  -- arithmetic: the exact value ≥ cθ·(loglogx − loglogA − 1)
  have hsmall : Real.log A * (1 / Real.log A - 1 / Real.log x) ≤ 1 := by
    have h2 : 0 ≤ Real.log A / Real.log x := div_nonneg (le_of_lt hlogA) (le_of_lt hlogx)
    field_simp [hlogA_ne, hlogx_ne]
    nlinarith
  have hval : cθ * ((Real.log (Real.log x) - Real.log (Real.log A)) -
        Real.log A * (1 / Real.log A - 1 / Real.log x)) ≥
      cθ * (Real.log (Real.log x) - Real.log (Real.log A) - 1) := by
    have hd : (Real.log (Real.log x) - Real.log (Real.log A)) -
          Real.log A * (1 / Real.log A - 1 / Real.log x) ≥
        Real.log (Real.log x) - Real.log (Real.log A) - 1 := by
      linarith [hsmall]
    exact mul_le_mul_of_nonneg_left hd hcθ
  calc
    cθ * (Real.log (Real.log x) - Real.log (Real.log A) - 1) ≤
        cθ * ((Real.log (Real.log x) - Real.log (Real.log A)) -
          Real.log A * (1 / Real.log A - 1 / Real.log x)) := hval
    _ ≤ ∫ t in A..x, logDiv t / (t * (Real.log t) ^ 2) := hvalbound
    _ ≤ (∫ t in A..x, logDiv t / (t * (Real.log t) ^ 2)) + (∫ t in 2..A, logDiv t / (t * (Real.log t) ^ 2)) := by linarith
    _ = ∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2) := hsplit
    _ ≤ logDiv x / Real.log x + (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) := by linarith

/-- For reals `A ≥ 2` and `M`, there is `X₀ ≥ A` with `log (log x) ≥ M` for all `x ≥ X₀`. -/
lemma exists_X0_ge_loglog_and_ge (A M : ℝ) (hA : 2 ≤ A) :
    ∃ X₀ : ℝ, A ≤ X₀ ∧ 1 < X₀ ∧ ∀ ⦃x : ℝ⦄, X₀ ≤ x → M ≤ Real.log (Real.log x) := by
  let M0 := max (max M (Real.log (Real.log A))) 0
  refine ⟨Real.exp (Real.exp M0), ?_, ?_, ?_⟩
  · have hApos : 0 < A := by linarith
    have hlogA : 0 < Real.log A := by exact log_pos (by linarith : (1 : ℝ) < A)
    have hM0A : Real.log (Real.log A) ≤ M0 := by
      calc
        Real.log (Real.log A) ≤ max M (Real.log (Real.log A)) := le_max_right M _
        _ ≤ max (max M (Real.log (Real.log A))) 0 := le_max_left _ 0
    have h1 : Real.log A ≤ Real.exp M0 := by
      calc
        Real.log A = Real.exp (Real.log (Real.log A)) := (Real.exp_log hlogA).symm
        _ ≤ Real.exp M0 := Real.exp_monotone hM0A
    calc
      A = Real.exp (Real.log A) := (Real.exp_log hApos).symm
      _ ≤ Real.exp (Real.exp M0) := Real.exp_monotone h1
  · have hM00 : 0 ≤ M0 := le_max_right _ 0
    have he1 : (1 : ℝ) ≤ Real.exp M0 := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp M0 := Real.exp_monotone hM00
    have h1lt : (1 : ℝ) < Real.exp 1 := one_lt_exp_iff.mpr zero_lt_one
    calc
      (1 : ℝ) < Real.exp 1 := h1lt
      _ ≤ Real.exp (Real.exp M0) := Real.exp_monotone he1
  · intro x hx
    have hM0M : M ≤ M0 := by
      calc
        M ≤ max M (Real.log (Real.log A)) := le_max_left M _
        _ ≤ max (max M (Real.log (Real.log A))) 0 := le_max_left _ 0
    have hxX : Real.exp (Real.exp M0) ≤ x := hx
    have hposX : 0 < Real.exp (Real.exp M0) := Real.exp_pos _
    have h1 : Real.exp M0 ≤ Real.log x := by
      have hle : Real.log (Real.exp (Real.exp M0)) ≤ Real.log x := Real.log_le_log hposX hxX
      simpa using hle
    have h2 : M ≤ Real.log (Real.log x) := by
      have hlogX : 0 < Real.exp M0 := Real.exp_pos M0
      have h3 : Real.log (Real.exp M0) ≤ Real.log (Real.log x) := Real.log_le_log hlogX h1
      have h4 : M0 ≤ Real.log (Real.log x) := by simpa using h3
      exact le_trans hM0M h4
    exact h2


/-- `mertens_lower`. -/
theorem mertens_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * Real.log (Real.log X) ≤ (∑ p ∈ (⌊X⌋₊).primesLE, (1 : ℝ) / p) := by
  obtain ⟨cθ, hcθ, A, hA2, hθ⟩ := theta_linear_lower
  let M := 2 * (Real.log (Real.log A) + 1)
  obtain ⟨X₀, hX₀A, hX₀gt1, hX₀M⟩ := exists_X0_ge_loglog_and_ge A M hA2
  refine ⟨cθ / 2, div_pos hcθ (by norm_num), X₀, hX₀gt1, ?_⟩
  intro X hX
  have hXA : A ≤ X := le_trans hX₀A hX
  have hX2 : 2 ≤ X := le_trans hA2 hXA
  have hlogDiv : ∀ ⦃t : ℝ⦄, A ≤ t → cθ * (Real.log t - Real.log A) ≤ logDiv t := by
    intro t ht
    have ht2 : 2 ≤ t := le_trans hA2 ht
    exact logDiv_ge_cθ_mul_log_sub ht2 hA2 ht (le_of_lt hcθ) hθ
  have hprime : cθ * (Real.log (Real.log X) - Real.log (Real.log A) - 1) ≤
      (∑ p ∈ (⌊X⌋₊).primesLE, (1 : ℝ) / p) := by
    simpa [primeRecips] using
      (primeRecips_ge_cθ_mul_loglog hX2 hA2 hXA (le_of_lt hcθ) hlogDiv)
  have hM : M ≤ Real.log (Real.log X) := hX₀M hX
  have hloglog : (2 * (Real.log (Real.log A) + 1) : ℝ) ≤ Real.log (Real.log X) := by
    simpa [M] using hM
  have hhalf : (cθ / 2) * Real.log (Real.log X) ≤
      cθ * (Real.log (Real.log X) - Real.log (Real.log A) - 1) := by
    nlinarith [hloglog, hcθ]
  exact le_trans hhalf hprime


end LowerBounds

end Commons.NumberTheory.Mertens
