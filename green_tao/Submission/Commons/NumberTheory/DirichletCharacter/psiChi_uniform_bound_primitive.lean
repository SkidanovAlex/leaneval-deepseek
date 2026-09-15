import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_truncatedPerron
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_two_lower
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_uniform_poly_strip
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_deriv_bound_near_one_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Commons.Analysis.Integral.integral_inv_sqrt_quarter_add_sq_le
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.Analysis.Fourier.perronStep_deviation
import Submission.Commons.NumberTheory.Zeta.perronOne_bound
import Submission.Commons.NumberTheory.Zeta.mangoldtPerronError_bound
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_mul_rpow
import Submission.Commons.NumberTheory.DirichletCharacter.perronSeries_sum_eq

open Complex DirichletCharacter Filter
open scoped BigOperators Interval Topology
open MeasureTheory intervalIntegral
set_option maxHeartbeats 12000000

namespace Commons.NumberTheory.DirichletCharacter


noncomputable section

open scoped BigOperators
open Finset


/-! # Truncated Perron formula for `χ · Λ`

This file develops the truncated Perron formula for the Dirichlet series attached to
`n ↦ χ(n) · Λ(n)`, needed to relate the twisted Chebyshev function
`Σ_{n ≤ x} χ(n) Λ(n)` to the integral of `LSeries (χ · Λ)` over a vertical segment
`Re s = 1 + 1 / log x`, `|Im s| ≤ T`.

The structure mirrors the classical (un-twisted) proof: the integral is expanded into a
series of per-step Perron kernels, each of which approximates an indicator function, and
the total deviation is bounded with the same explicit bound as in the classical case.
-/

/-! ## Elementary facts about `x ≥ 3` -/

private lemma log_pos_of_three_le {x : ℝ} (hx : 3 ≤ x) : 0 < Real.log x := by
  have h1x : 1 < x := by linarith
  exact Real.log_pos h1x

private lemma sigma_ge_one {x : ℝ} (hx : 3 ≤ x) : 1 ≤ 1 + 1 / Real.log x := by
  have hlog : 0 < Real.log x := log_pos_of_three_le hx
  nlinarith [one_div_pos.mpr hlog]

private lemma nat_le_x_iff_floor {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (n : ℝ) ≤ x ↔ n ≤ ⌊x⌋₊ := by
  constructor
  · intro h
    exact Nat.le_floor h
  · intro h
    have hcast : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h
    exact le_trans hcast (Nat.floor_le hx)

/-! ## The per-step Perron kernel -/

/-- The per-step Perron integral `(1/2π) ∫_{-T}^{T} exp((σ+it)·log z)/(σ+it) dt`. -/
private noncomputable def perronStep (σ T : ℝ) (z : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
    Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ))) /
      ((σ : ℂ) + Complex.I * (t : ℂ)))

/-- Per-step deviation bound, restated for our definition `perronStep`. -/
private lemma perronStep_dev_le {σ T z : ℝ} (hσ : 1 ≤ σ) (hT : 1 ≤ T) (hz : 0 < z)
    (hz1 : z ≠ 1) :
    ‖perronStep σ T z - (if 1 < z then (1 : ℂ) else 0)‖ ≤
      (32 / (2 * Real.pi)) * (z ^ σ) * min 1 (1 / (T * |Real.log z|)) := by
  simpa [perronStep] using
    (Commons.Analysis.Fourier.perronStep_deviation σ T z hσ hT hz hz1)

private lemma one_lt_div_iff {x n : ℝ} (hn : 0 < n) : (1 < x / n) ↔ (n < x) := by
  rw [lt_div_iff₀ hn]
  simp

/-- Indicator equivalence for the Perron step: `1 < x/n` iff `n < x`. -/
private lemma perronStep_indicator {x n : ℝ} (hn : 0 < n) :
    (if 1 < x / n then (1 : ℂ) else 0) = if n < x then (1 : ℂ) else 0 := by
  by_cases h : n < x
  · have : 1 < x / n := (one_lt_div_iff hn).mpr h
    simp [h, this]
  · have hnot : ¬ 1 < x / n := by
      intro h1
      exact h ((one_lt_div_iff hn).mp h1)
    simp [h, hnot]

/-- Bound on a single von-Mangoldt weighted Perron deviation term (n ≥ 1, n ≠ x). -/
private lemma perronStep_mangoldt_le {x T : ℝ} (hx3 : 3 ≤ x) (hT : 2 ≤ T) {n : ℕ} (hn1 : 1 ≤ n)
    (hnx : (n : ℝ) ≠ x) :
    ‖perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)) -
        (if (n : ℝ) < x then (1 : ℂ) else 0)‖ ≤
      (32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
  have hxpos : 0 < x := by linarith
  have hz : 0 < x / (n : ℝ) := div_pos hxpos hnpos
  have hz1 : x / (n : ℝ) ≠ 1 := by
    intro h
    have hxeq : x = (n : ℝ) := by
      have h' := congrArg (fun y : ℝ => y * (n : ℝ)) h
      rw [div_mul_cancel₀ _ hnpos.ne'] at h'
      simpa using h'
    exact hnx hxeq.symm
  have hmain := perronStep_dev_le (σ := 1 + 1 / Real.log x) (T := T) (z := x / (n : ℝ))
    (sigma_ge_one hx3) (by linarith) hz hz1
  have hind : (if 1 < x / (n : ℝ) then (1 : ℂ) else 0) = if (n : ℝ) < x then (1 : ℂ) else 0 :=
    perronStep_indicator (x := x) (n := (n : ℝ)) hnpos
  simpa [hind] using hmain

/-- `‖1 - w‖ ≤ 3/2` provided `‖w‖ ≤ 1/2`. -/
private lemma norm_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖(1 : ℂ) - w‖ ≤ 3 / 2 := by
  calc
    ‖(1 : ℂ) - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ 1 + 1 / 2 := by simpa using add_le_add_left hw (‖(1 : ℂ)‖)
    _ = 3 / 2 := by norm_num

private lemma perronStep_one (σ T : ℝ) :
    perronStep σ T 1 =
      (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
        (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
  unfold perronStep
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp

private lemma perronStep_one_norm {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ‖perronStep σ T 1‖ ≤ 1 / 2 := by
  rw [perronStep_one]
  exact Commons.NumberTheory.Zeta.perronOne_bound σ T hσ hT

/-! ## The twisted von Mangoldt sequence `χ · Λ` -/

/-- The sequence `n ↦ χ(n) Λ(n)` attached to a Dirichlet character `χ`. -/
private def chiLambda {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  fun n => χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

private lemma chiLambda_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    chiLambda χ 0 = 0 := by
  simp [chiLambda, ArithmeticFunction.map_zero]

private lemma chiLambda_norm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖chiLambda χ n‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hc : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have h1 : ‖chiLambda χ n‖ =
      ‖χ ((n : ℕ) : ZMod N)‖ * (ArithmeticFunction.vonMangoldt n : ℝ) := by
    simp [chiLambda, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
  rw [h1]
  calc
    ‖χ ((n : ℕ) : ZMod N)‖ * (ArithmeticFunction.vonMangoldt n : ℝ)
        ≤ 1 * (ArithmeticFunction.vonMangoldt n : ℝ) :=
          mul_le_mul_of_nonneg_right hc hΛ
    _ = (ArithmeticFunction.vonMangoldt n : ℝ) := one_mul _

/-! ## The twisted truncated Perron integral -/

/-- The truncated Perron integral from the statement. -/
private noncomputable def perronInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
    (LSeries (chiLambda χ) (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
      (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))

/-- Pointwise bound for the `n`-th term of the twisted Perron error sum. -/
private lemma chiLambda_pointwise {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x T : ℝ} (hx3 : 3 ≤ x) (hT : 2 ≤ T) (n : ℕ) :
    ‖(if (n : ℝ) ≤ x then chiLambda χ n else 0)
        - chiLambda χ n * perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) +
          (if (n : ℝ) = x then 2 * (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
  have hΛnn : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg (n := n)
  by_cases hn0 : n = 0
  · subst n
    have hx0 : ¬ ((0 : ℝ) = x) := by intro h; linarith
    simp [chiLambda, hx0, ArithmeticFunction.map_zero]
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    by_cases hnx : (n : ℝ) = x
    · -- case n = x
      have hle : (n : ℝ) ≤ x := le_of_eq hnx
      have hxeq : x = (n : ℝ) := hnx.symm
      have hdiv : x / (n : ℝ) = 1 := by
        rw [hxeq]
        exact div_self (by exact_mod_cast (Nat.pos_of_ne_zero hn0).ne')
      rw [if_pos hle, if_pos hnx, hdiv]
      have hfac : chiLambda χ n - chiLambda χ n * perronStep (1 + 1 / Real.log x) T 1
          = chiLambda χ n * ((1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1) := by ring
      rw [hfac]
      have hred : (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((32 / (2 * Real.pi)) * (1 : ℝ) ^ (1 + 1 / Real.log x) *
              min 1 (1 / (T * |Real.log (1 : ℝ)|))) +
          (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) = 2 * (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [Real.one_rpow, Real.log_one, abs_zero, mul_zero, div_zero, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
        ring
      rw [hred]
      have hQ : ‖(1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1‖ ≤ 3 / 2 := by
        apply norm_sub_one_le
        apply perronStep_one_norm (σ := 1 + 1 / Real.log x) (T := T)
        · exact lt_of_lt_of_le zero_lt_one (sigma_ge_one hx3)
        · linarith
      calc
        ‖chiLambda χ n * ((1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1)‖
            ≤ ‖chiLambda χ n‖ * ‖(1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1‖ :=
              norm_mul_le _ _
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (3 / 2) :=
              mul_le_mul (chiLambda_norm_le χ n) hQ (norm_nonneg _) hΛnn
        _ ≤ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) := by nlinarith
    · -- case n ≠ x
      rw [if_neg hnx]
      have hind : (if (n : ℝ) ≤ x then chiLambda χ n else 0)
          = chiLambda χ n * (if (n : ℝ) < x then (1 : ℂ) else 0) := by
        by_cases hlt : (n : ℝ) < x
        · have hle' : (n : ℝ) ≤ x := le_of_lt hlt
          simp [hlt, hle']
        · have hle' : ¬ (n : ℝ) ≤ x := by
            intro h
            exact hlt (lt_of_le_of_ne h hnx)
          simp [hlt, hle']
      have hB : ‖(if (n : ℝ) < x then (1 : ℂ) else 0) -
          perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
          ≤ (32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) := by
        rw [norm_sub_rev]
        exact perronStep_mangoldt_le hx3 hT hn1 hnx
      calc
        ‖(if (n : ℝ) ≤ x then chiLambda χ n else 0)
            - chiLambda χ n * perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
            = ‖chiLambda χ n *
                ((if (n : ℝ) < x then (1 : ℂ) else 0) -
                  perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)))‖ := by
              rw [hind, ← mul_sub]
        _ ≤ ‖chiLambda χ n‖ *
              ‖(if (n : ℝ) < x then (1 : ℂ) else 0) -
                perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖ := norm_mul_le _ _
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
                min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) :=
              mul_le_mul (chiLambda_norm_le χ n) hB (norm_nonneg _) hΛnn
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
                min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) + 0 := by
              rw [add_zero]

/-! ## The Perron integral as a series of per-step kernels -/

private lemma chiSummable_weighted {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖chiLambda χ n‖ * (x / (n : ℝ)) ^ σ) := by
  have hΛ := Commons.NumberTheory.Zeta.summable_vonMangoldt_mul_rpow hx hσ
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (div_nonneg hx.le (by positivity)) _))
    (fun n => ?_) hΛ
  exact mul_le_mul_of_nonneg_right (chiLambda_norm_le χ n)
    (Real.rpow_nonneg (div_nonneg hx.le (by positivity)) _)

/-- The Perron integral expands into the weighted per-step sums. -/
private lemma perronInt_eq_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 1 < x) (T : ℝ) :
    perronInt χ x T =
      ∑' n : ℕ, chiLambda χ n * perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)) := by
  unfold perronInt
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hσ : 1 < 1 + 1 / Real.log x := by
    have h1 : 0 < 1 / Real.log x := one_div_pos.mpr hlog
    linarith
  have hsum := chiSummable_weighted χ (by linarith : (0:ℝ) < x) hσ
  rw [perronSeries_sum_eq (chiLambda χ) (chiLambda_zero χ) x (by linarith : (0:ℝ) < x) (1 + 1 / Real.log x) T hσ hsum]
  apply tsum_congr
  intro n
  simp only [perronStep]
  ring

/-- The partial Chebyshev sum for `χ · Λ` equals the indicator-truncated `tsum`. -/
private lemma chiSum_eq_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chiLambda χ n)
      = ∑' n : ℕ, (if (n : ℝ) ≤ x then chiLambda χ n else 0) := by
  have hmain : (∑' n : ℕ, (if (n : ℝ) ≤ x then chiLambda χ n else 0))
      = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if (n : ℝ) ≤ x then chiLambda χ n else 0) := by
    apply tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.Icc 0 ⌊x⌋₊)
      (f := fun n : ℕ => if (n : ℝ) ≤ x then chiLambda χ n else 0)
    intro n hn
    by_cases h : (n : ℝ) ≤ x
    · exfalso
      have hnfl : n ≤ ⌊x⌋₊ := (nat_le_x_iff_floor hx n).mp h
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnfl⟩)
    · simp [h]
  rw [hmain]
  have hset : Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  have h0 : (if ((0 : ℕ) : ℝ) ≤ x then chiLambda χ 0 else 0) = 0 := by
    rw [if_pos (show ((0 : ℕ) : ℝ) ≤ x from by simpa using hx), chiLambda_zero]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hn).2
  have : (n : ℝ) ≤ x := (nat_le_x_iff_floor hx n).mpr hnle
  simp [this]

/-- Indicator-cut twisted von Mangoldt sequence is summable (finite support). -/
private lemma summable_indicator_chi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => if (n : ℝ) ≤ x then chiLambda χ n else 0) := by
  let s : Finset ℕ := Finset.Icc 0 ⌊x⌋₊
  have hfin : HasSum (fun n : ℕ => if (n : ℝ) ≤ x then chiLambda χ n else 0)
      (∑ n ∈ s, (if (n : ℝ) ≤ x then chiLambda χ n else 0)) := by
    apply hasSum_sum_of_ne_finset_zero (s := s)
    intro n hn
    by_cases hle : (n : ℝ) ≤ x
    · exfalso
      have hnfl : n ≤ ⌊x⌋₊ := (nat_le_x_iff_floor hx n).mp hle
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnfl⟩)
    · simp [hle]
  exact hfin.summable

/-- A natural number equal to `x` must be `⌊x⌋₊`. -/
private lemma nat_eq_floor_of_eq {x : ℝ} (n : ℕ) (h : (n : ℝ) = x) : n = ⌊x⌋₊ := by
  rw [← h]
  simp

/-- Extra term `2·Λ n` for the boundary index `n = x` is summable (support ≤ 1). -/
private lemma summable_extra {x : ℝ} :
    Summable (fun n : ℕ => if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) := by
  let s : Finset ℕ := {⌊x⌋₊}
  have hfin : HasSum (fun n : ℕ => if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0)
      (∑ n ∈ s, (if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0)) := by
    apply hasSum_sum_of_ne_finset_zero (s := s)
    intro n hn
    have hnne : n ≠ ⌊x⌋₊ := by
      intro heq
      exact hn (Finset.mem_singleton.mpr heq)
    have hnx : (n : ℝ) ≠ x := by
      intro hx0
      exact hnne (nat_eq_floor_of_eq n hx0)
    simp [hnx]
  exact hfin.summable

/-- The extra boundary contribution is `≤ 2·log x`. -/
private lemma extra_tsum_le {x : ℝ} (hx3 : 3 ≤ x) :
    (∑' n : ℕ, if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) ≤
      2 * Real.log x := by
  let s : Finset ℕ := {⌊x⌋₊}
  have htsum : (∑' n : ℕ, if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0)
      = ∑ n ∈ s, (if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) := by
    apply tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := s)
    intro n hn
    have hnne : n ≠ ⌊x⌋₊ := by
      intro heq
      exact hn (Finset.mem_singleton.mpr heq)
    have hnx : (n : ℝ) ≠ x := by
      intro hx0
      exact hnne (nat_eq_floor_of_eq n hx0)
    simp [hnx]
  rw [htsum]
  simp only [s, Finset.sum_singleton]
  have hterm : (if (⌊x⌋₊ : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℝ)) else 0)
      ≤ 2 * ArithmeticFunction.vonMangoldt ⌊x⌋₊ := by
    by_cases h : (⌊x⌋₊ : ℝ) = x
    · simp [h]
    · simp [h, ArithmeticFunction.vonMangoldt_nonneg]
  calc
    (if (⌊x⌋₊ : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℝ)) else 0)
        ≤ 2 * ArithmeticFunction.vonMangoldt ⌊x⌋₊ := hterm
    _ ≤ 2 * Real.log (⌊x⌋₊ : ℝ) := by
      gcongr
      exact ArithmeticFunction.vonMangoldt_le_log (n := ⌊x⌋₊)
    _ ≤ 2 * Real.log x := by
      have hlogle : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
        apply Real.log_le_log
        · have h3n : (3 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
            have := Nat.le_floor (a := x) (n := 3) (by linarith : (3 : ℝ) ≤ x)
            exact_mod_cast this
          linarith
        · exact Nat.floor_le (by linarith : 0 ≤ x)
      nlinarith

/-- The main inequality: the twisted Chebyshev sum is approximated by the truncated
Perron integral, with the same explicit error as in the untwisted case. -/
private lemma chiPsi_sub_perron_main {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x T : ℝ} (hx3 : 3 ≤ x) (hT : 2 ≤ T) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chiLambda χ n) - perronInt χ x T‖ ≤
      (32 / (2 * Real.pi)) *
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
          min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) + 2 * Real.log x := by
  let ind : ℕ → ℂ := fun n => if (n : ℝ) ≤ x then chiLambda χ n else 0
  let q : ℕ → ℂ := fun n => chiLambda χ n * perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))
  let u : ℕ → ℂ := fun n => ind n - q n
  let a : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
      min 1 (1 / (T * |Real.log (x / (n : ℝ))|))
  let extra : ℕ → ℝ := fun n => if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0
  let e : ℕ → ℝ := fun n => (32 / (2 * Real.pi)) * a n + extra n
  have hxpos : 0 < x := by linarith
  have hS : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chiLambda χ n) = ∑' n : ℕ, ind n := by
    dsimp [ind]
    exact chiSum_eq_tsum χ hxpos.le
  have hJ : perronInt χ x T = ∑' n : ℕ, q n := by
    dsimp [q]
    exact perronInt_eq_tsum χ (by linarith) T
  have hsum_a : Summable a := by
    rcases Commons.NumberTheory.Zeta.mangoldtPerronError_bound with ⟨CA, _hCApos, hCA⟩
    exact (hCA x hx3 T hT).1
  have hsum_ind : Summable ind := by
    simpa [ind] using (summable_indicator_chi χ hxpos.le)
  have hsum_extra : Summable extra := by
    simpa [extra] using (summable_extra (x := x))
  have hpt : ∀ n : ℕ, ‖u n‖ ≤ e n := by
    intro n
    have hmain := chiLambda_pointwise χ hx3 hT n
    simp only [u, ind, q, e, a, extra] at hmain ⊢
    convert hmain using 1
    ring
  have hsum_e : Summable e := by
    have hmul : Summable (fun n : ℕ => (32 / (2 * Real.pi)) * a n) := by
      simpa [a] using (hsum_a.const_smul (32 / (2 * Real.pi)) : Summable (fun n => (32 / (2 * Real.pi)) • a n))
    exact Summable.add hmul hsum_extra
  have hsum_norm_u : Summable (fun n : ℕ => ‖u n‖) := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => (hpt n)) hsum_e
  have hsum_u : Summable u := Summable.of_norm hsum_norm_u
  calc
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chiLambda χ n) - perronInt χ x T‖
        = ‖(∑' n : ℕ, ind n) - (∑' n : ℕ, q n)‖ := by rw [hS, hJ]
    _ = ‖∑' n : ℕ, u n‖ := by
      have hqsum : (∑' n : ℕ, q n) = (∑' n : ℕ, ind n) - (∑' n : ℕ, u n) := by
        have hts := Summable.tsum_sub hsum_ind hsum_u
        simpa [u, q] using hts
      rw [hqsum]
      congr 1
      ring
    _ ≤ ∑' n : ℕ, ‖u n‖ := norm_tsum_le_tsum_norm hsum_norm_u
    _ ≤ ∑' n : ℕ, e n := by
      exact hasSum_le (fun n => hpt n) hsum_norm_u.hasSum hsum_e.hasSum
    _ = (32 / (2 * Real.pi)) * (∑' n : ℕ, a n) + (∑' n : ℕ, extra n) := by
      have hmul' : (∑' n : ℕ, (32 / (2 * Real.pi)) * a n) =
          (32 / (2 * Real.pi)) * (∑' n : ℕ, a n) := tsum_mul_left
      have hts := Summable.tsum_add (f := fun n : ℕ => (32 / (2 * Real.pi)) * a n) (g := extra)
        (by simpa [a] using (hsum_a.const_smul (32 / (2 * Real.pi)) : Summable (fun n => (32 / (2 * Real.pi)) • a n)))
        hsum_extra
      rw [hts, hmul']
    _ ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, a n) + 2 * Real.log x := by
      have hle : (∑' n : ℕ, extra n) ≤ 2 * Real.log x := by
        simpa [extra] using (extra_tsum_le (x := x) hx3)
      linarith

private lemma log_ge_one_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h1 : Real.exp 1 ≤ x := le_trans Real.exp_one_lt_three.le hx
  have h2 := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at h2


private theorem LFunction_poly_strip_explicit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hlo : (1 / 8 : ℝ) ≤ s.re) (hhi : s.re ≤ 1) :
    ‖LFunction χ s‖ ≤ 16 * (1 + |s.im|) * (N : ℝ) := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hlo
  have hsabs : |s.re| ≤ 1 := by rw [abs_of_pos hs0]; exact hhi
  have hnorm : ‖s‖ ≤ 1 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + |s.im| := add_le_add hsabs le_rfl
  have hb := LFunction_norm_half_plane χ hχ hs0
  have hmain : 2 * (N : ℝ) * ‖s‖ / s.re ≤ 16 * (N : ℝ) * (1 + |s.im|) := by
    have hinv : (s.re)⁻¹ ≤ 8 := by
      have hle : 1 / s.re ≤ 8 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 / 8 : ℝ)) hlo
        simpa using h
      simpa using hle
    calc 2 * (N : ℝ) * ‖s‖ / s.re = 2 * (N:ℝ) * ‖s‖ * (s.re)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 2 * (N:ℝ) * ‖s‖ * 8 := by
            apply mul_le_mul_of_nonneg_left hinv; positivity
      _ = 16 * (N : ℝ) * ‖s‖ := by ring
      _ ≤ 16 * (N : ℝ) * (1 + |s.im|) := by
            apply mul_le_mul_of_nonneg_left hnorm; positivity
  calc ‖LFunction χ s‖ ≤ 2 * (N : ℝ) * ‖s‖ / s.re := hb
    _ ≤ 16 * (N : ℝ) * (1 + |s.im|) := hmain
    _ = 16 * (1 + |s.im|) * (N : ℝ) := by ring

private lemma abs_im_sub_le (a b : ℝ) : |a| ≤ |a - b| + |b| := by
  calc |a| = |(a - b) + b| := by congr 1; ring
    _ ≤ |a - b| + |b| := abs_add_le _ _

noncomputable def boxC (cOff cReal : ℝ) : ℝ := min (min (cReal / 3) (cOff / 6)) (1 / 8)

theorem logDeriv_box_uniform {cOff cReal : ℝ} (hcOffpos : 0 < cOff) (hcRealpos : 0 < cReal)
    (hOff : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ (σ t : ℝ), t ≠ 0 → 1 - cOff / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
      LFunction χ ((σ : ℂ) + (t : ℂ) * I) ≠ 0)
    (hReal : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      χ * χ ≠ 1 → ∀ σ : ℝ, 1 - cReal / Real.log (2 * (N : ℝ)) ≤ σ →
      LFunction χ (σ : ℂ) ≠ 0)
    (ε Cs D : ℝ) (hε : 0 < ε) (hCs : 0 < Cs) (hD : 0 < D)
    (hSiegel : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 →
      LFunction χ (β : ℂ) = 0 → Cs * (N : ℝ) ^ (-ε) ≤ 1 - β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
        (hprim : χ.IsPrimitive) (T δ : ℝ) (hT : 3 ≤ T)
        (hδpos : 0 < δ)
        (hδc : δ ≤ boxC cOff cReal / Real.log ((N : ℝ) * (T + 3)))
        (hδS : δ ≤ Cs * (N : ℝ) ^ (-ε) / 4)
        (hL1 : 1 ≤ Real.log ((N : ℝ) * (T + 3)))
        (hδlo : 1 / δ ^ 2 ≤ D * (Real.log ((N : ℝ) * (T + 3))) ^ 3)
        (σ t : ℝ) (ht : |t| ≤ T) (hσlo : 1 - δ ≤ σ) (hσhi : σ ≤ 2),
        LFunction χ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧
        ‖logDeriv (LFunction χ) ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          C * (Real.log ((N : ℝ) * (T + 3))) ^ 4 := by
  set c0 : ℝ := boxC cOff cReal with hc0def
  have hc0pos : 0 < c0 := by
    rw [hc0def, boxC]
    exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hc0le8 : c0 ≤ 1 / 8 := by rw [hc0def, boxC]; exact min_le_right _ _
  have hc0leR : c0 ≤ cReal / 3 := by
    rw [hc0def, boxC]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hc0leO : c0 ≤ cOff / 6 := by
    rw [hc0def, boxC]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  refine ⟨32 * D, by positivity, ?_⟩
  intro N _inst χ hχ hprim T δ hT hδpos hδc hδS hL1 hδlo σ t ht hσlo hσhi
  have hN2 : 2 ≤ N := two_le_of_ne_one χ hχ
  have hN2' : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by linarith
  set L : ℝ := Real.log ((N : ℝ) * (T + 3)) with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hδcL : δ ≤ c0 / L := hδc
  have hδSL : δ ≤ Cs * (N : ℝ) ^ (-ε) / 4 := hδS
  have hlog2le : Real.log 2 ≤ L := by
    rw [hLdef]; apply Real.log_le_log (by norm_num); nlinarith [hN1, hT]
  have hδle8 : δ ≤ 1 / 8 := by
    have h2 : c0 / L ≤ 1 / 8 := by
      rw [div_le_iff₀ hLpos]; nlinarith [hc0le8, hL1]
    linarith [hδcL, h2]
  have hT3 : (3:ℝ) ≤ T + 3 := by linarith
  have hlog2N : Real.log (2 * (N:ℝ)) ≤ L := by
    rw [hLdef]; apply Real.log_le_log (by positivity); nlinarith [hN1, hT]
  have hlog2Npos : 0 < Real.log (2 * (N:ℝ)) := Real.log_pos (by linarith)
  set cc : ℂ := (2:ℂ) + (t:ℂ) * I with hccdef
  set R : ℝ := 1 + 3 * δ with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRle : R ≤ 2 := by rw [hRdef]; linarith
  have hzf : ∀ w : ℂ, w ∈ Metric.ball cc R → LFunction χ w ≠ 0 := by
    intro w hw hzero
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hwre : 2 - R < w.re := by
      have h1 : |(w - cc).re| ≤ ‖w - cc‖ := Complex.abs_re_le_norm _
      have h2 : (w - cc).re = w.re - 2 := by simp [hccdef]
      rw [h2] at h1
      have h3 : -(w.re - 2) ≤ |w.re - 2| := neg_le_abs _
      linarith [h1, h3, hw]
    have hwim : |w.im| < |t| + R := by
      have h1 : |(w - cc).im| ≤ ‖w - cc‖ := Complex.abs_im_le_norm _
      have h2 : (w - cc).im = w.im - t := by simp [hccdef]
      rw [h2] at h1
      have h3 : |w.im| ≤ |w.im - t| + |t| := abs_im_sub_le w.im t
      linarith [h1, h3, hw]
    have hwre' : 1 - 3 * δ < w.re := by
      have h : R = 1 + 3 * δ := hRdef
      linarith [hwre]
    rcases eq_or_ne w.im 0 with him0 | himne
    · have hwreal : w = ((w.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him0]
      rw [hwreal] at hzero
      rcases eq_or_ne (χ * χ) 1 with hsq | hsq
      · by_cases hw1 : 1 ≤ w.re
        · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (by simpa using hw1) hzero
        · push_neg at hw1
          have hwr_pos : 0 < w.re := by linarith [hwre']
          have hS := hSiegel N χ hprim hχ hsq w.re hwr_pos hw1 hzero
          have hup : 1 - w.re < 3 * δ := by linarith [hwre']
          have h3d : 3 * δ ≤ 3 * (Cs * (N:ℝ)^(-ε) / 4) := by linarith [hδSL]
          have hpos4 : 0 < Cs * (N:ℝ)^(-ε) / 4 := by positivity
          nlinarith [hS, hup, h3d, hpos4]
      · by_cases hw1 : 1 ≤ w.re
        · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (by simpa using hw1) hzero
        · push_neg at hw1
          have hneed : 1 - cReal / Real.log (2 * (N:ℝ)) ≤ w.re := by
            have h1 : 1 - w.re < 3 * δ := by linarith [hwre']
            have h2 : 3 * δ ≤ 3 * (c0 / L) := by linarith [hδcL]
            have h3 : 3 * (c0 / L) ≤ cReal / Real.log (2 * (N:ℝ)) := by
              have hc3 : 3 * c0 ≤ cReal := by linarith [hc0leR]
              rw [show 3 * (c0 / L) = (3 * c0) / L by ring, div_le_div_iff₀ hLpos hlog2Npos]
              nlinarith [hlog2N, hc3, hLpos, hcRealpos]
            linarith [h1, h2, h3]
          exact hReal N χ hprim hχ hsq w.re hneed hzero
    · have hw' : w = ((w.re : ℂ) + (w.im : ℂ) * I) := (Complex.re_add_im w).symm
      rw [hw'] at hzero
      have himabs : |w.im| ≤ T + 2 := by linarith [hwim, ht, hRle]
      have hlog_le : Real.log ((N:ℝ) * (|w.im| + 2)) < 2 * L := by
        have hT0 : (0:ℝ) ≤ T := by linarith
        have h3 : |w.im| + 2 < (T+3)^2 := by nlinarith [himabs, hT0, sq_nonneg T]
        have h4 : (N:ℝ) * (|w.im| + 2) < (N:ℝ) * (T+3)^2 := by nlinarith [hNpos]
        have h5 : (N:ℝ) * (T+3)^2 ≤ ((N:ℝ) * (T + 3)) ^ 2 := by
          have ha : (0:ℝ) ≤ (T+3)^2 := by positivity
          have hNm1 : (0:ℝ) ≤ (N:ℝ) - 1 := by linarith [hN1]
          have hprod : (0:ℝ) ≤ (N:ℝ) * (T+3)^2 * ((N:ℝ) - 1) :=
            mul_nonneg (mul_nonneg hNpos.le ha) hNm1
          nlinarith [hprod]
        have h2 : (N:ℝ) * (|w.im| + 2) < ((N:ℝ) * (T + 3)) ^ 2 := lt_of_lt_of_le h4 h5
        have h7 := Real.log_lt_log (by positivity : (0:ℝ) < (N:ℝ) * (|w.im| + 2)) h2
        rw [Real.log_pow] at h7
        have h8 : Real.log ((N:ℝ) * (T+3)) = L := hLdef
        rw [h8] at h7
        exact h7
      have hlogpos : 0 < Real.log ((N:ℝ) * (|w.im| + 2)) :=
        Real.log_pos (by nlinarith [hN1, abs_nonneg w.im])
      have hneed : 1 - cOff / Real.log ((N:ℝ) * (|w.im| + 2)) ≤ w.re := by
        have h1 : 1 - w.re < 3 * δ := by linarith [hwre']
        have h2 : 3 * δ ≤ 3 * (c0 / L) := by linarith [hδcL]
        have h3 : 3 * (c0 / L) ≤ cOff / Real.log ((N:ℝ) * (|w.im| + 2)) := by
          have hc6 : 6 * c0 ≤ cOff := by linarith [hc0leO]
          rw [show 3 * (c0 / L) = (3 * c0) / L by ring, div_le_div_iff₀ hLpos hlogpos]
          nlinarith [hlog_le, hc6, hcOffpos, hLpos]
        linarith [h1, h2, h3]
      exact (hOff N χ hprim hχ w.re w.im himne hneed) hzero
  have hposM : (0:ℝ) ≤ 16 * (T+3) * (N:ℝ) := by positivity
  set M : ℝ := 16 * (T + 3) * (N : ℝ) + (Real.log (N : ℝ) + Real.log (T + 4) + 6) + 1 with hMdef
  have hM1 : (1:ℝ) ≤ M := by
    rw [hMdef]
    have h2 : (0:ℝ) ≤ Real.log (N:ℝ) + Real.log (T+4) + 6 := by
      have h3 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
      have h4 : (0:ℝ) ≤ Real.log (T+4) := Real.log_nonneg (by linarith)
      linarith
    linarith
  have hgm : (1/2:ℝ) ≤ M := by linarith [hM1]
  have hballM : ∀ w : ℂ, w ∈ Metric.ball cc R → ‖LFunction χ w‖ ≤ M := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have himw : |w.im| < T + 2 := by
      have h1 : |(w - cc).im| ≤ ‖w - cc‖ := Complex.abs_im_le_norm _
      have h2 : (w - cc).im = w.im - t := by simp [hccdef]
      rw [h2] at h1
      have h3 : |w.im| ≤ |w.im - t| + |t| := abs_im_sub_le w.im t
      linarith [h1, h3, hw, ht, hRle]
    have hwre : 2 - R < w.re := by
      have h1 : |(w - cc).re| ≤ ‖w - cc‖ := Complex.abs_re_le_norm _
      have h2 : (w - cc).re = w.re - 2 := by simp [hccdef]
      rw [h2] at h1
      have h3 : -(w.re - 2) ≤ |w.re - 2| := neg_le_abs _
      linarith [h1, h3, hw]
    by_cases hcase : 1 ≤ w.re
    · have h1 := norm_LFunction_le_re_ge_one χ hχ w hcase
      have h2 : Real.log (2 + |w.im|) ≤ Real.log (T + 4) := by
        apply Real.log_le_log (by positivity)
        linarith [himw]
      rw [hMdef]
      linarith [h1, h2, hposM]
    · push_neg at hcase
      have hlo : (1/8:ℝ) ≤ w.re := by
        have h' : 1 - 3*δ < w.re := by
          have h : R = 1 + 3 * δ := hRdef
          linarith [hwre]
        have h3d : 3 * δ ≤ 3/8 := by linarith [hδle8]
        linarith
      have h1 := LFunction_poly_strip_explicit (s := w) χ hχ hlo hcase.le
      have h3 : 16 * (1 + |w.im|) * (N:ℝ) ≤ 16 * (T+3) * (N:ℝ) := by
        have h4 : 1 + |w.im| ≤ T + 3 := by linarith [himw]
        have h6 : 16 * (1 + |w.im|) ≤ 16 * (T+3) := by linarith
        calc 16 * (1 + |w.im|) * (N:ℝ) = (16 * (1 + |w.im|)) * (N:ℝ) := by ring
          _ ≤ (16 * (T+3)) * (N:ℝ) := mul_le_mul_of_nonneg_right h6 (by positivity)
          _ = 16 * (T+3) * (N:ℝ) := by ring
      rw [hMdef]
      have hL2 : (0:ℝ) ≤ Real.log (N:ℝ) + Real.log (T+4) + 6 := by
        have h3 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
        have h4 : (0:ℝ) ≤ Real.log (T+4) := Real.log_nonneg (by linarith)
        linarith
      linarith [h1, h3, hL2]
  set z₀ : ℂ := (σ:ℂ) + (t:ℂ) * I with hz₀def
  have hz0sub : z₀ - cc = (((σ - 2 : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [hz₀def, hccdef]
  have hz0norm : ‖z₀ - cc‖ = 2 - σ := by
    rw [hz0sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [hσhi] : (σ - 2 : ℝ) ≤ 0)]
    ring
  have hzg : z₀ ∈ Metric.ball cc R := by
    rw [Metric.mem_ball, dist_eq_norm, hz0norm, hRdef]
    linarith [hσlo]
  have hρlt : δ < R - ‖z₀ - cc‖ := by
    rw [hz0norm, hRdef]; linarith [hσlo]
  have hgm2 : (1/2:ℝ) ≤ ‖LFunction χ cc‖ := by
    have hcc : cc = (2:ℂ) + I * (t:ℂ) := by rw [hccdef]; ring
    rw [hcc]
    exact LFunction_two_lower χ t
  have hdisk := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
    (g := LFunction χ) (c := cc) (R := R) (m := 1/2) (M := M)
    hRpos (by norm_num) hgm
    (fun w _ => (differentiable_LFunction hχ).analyticAt w) hzf hballM hgm2
    (z₀ := z₀) hzg δ hδpos hρlt
  have hlogM : Real.log (2 * M) ≤ 7 * L := by
    have hlogN : Real.log (N:ℝ) ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by positivity) (by nlinarith [hN1, hT])
    have hlogT : Real.log (T+4) ≤ L := by
      rw [hLdef]; apply Real.log_le_log (by positivity); nlinarith [hN2', hT3]
    have hLle : L ≤ (N:ℝ) * (T + 3) := by
      rw [hLdef]; exact Real.log_le_self (by positivity)
    have hNT1 : (1:ℝ) ≤ (N:ℝ) * (T+3) := by nlinarith [hN1, hT3]
    have h2M : 2 * M ≤ 64 * ((N:ℝ) * (T + 3)) := by
      rw [hMdef]
      nlinarith [hlogN, hlogT, hLle, hNT1]
    have hpos : (0:ℝ) < 2 * M := by linarith [hM1]
    have hNTpos : (0:ℝ) < (N:ℝ) * (T+3) := by positivity
    have h1 : Real.log (2 * M) ≤ Real.log (64 * ((N:ℝ) * (T + 3))) :=
      Real.log_le_log hpos h2M
    rw [Real.log_mul (by norm_num) (ne_of_gt hNTpos)] at h1
    have h64 : Real.log (64:ℝ) ≤ 6 := by
      have hlog64 : Real.log (64:ℝ) = 6 * Real.log 2 := by
        rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
        norm_num
      rw [hlog64]
      linarith [Real.log_two_lt_d9]
    have h5 : Real.log ((N:ℝ) * (T+3)) = L := hLdef
    rw [h5] at h1
    linarith [h1, h64, hL1]
  have hfrac : (‖z₀ - cc‖ + δ) / ((R - ‖z₀ - cc‖ - δ) * δ) ≤ 2 / δ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hnum : ‖z₀ - cc‖ + δ ≤ 1 + 2*δ := by rw [hz0norm]; linarith [hσlo]
    have hden : δ ≤ R - ‖z₀ - cc‖ - δ := by rw [hz0norm, hRdef]; linarith [hσlo]
    nlinarith [hnum, hden, hδpos]
  have hlog2 : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  have hkey : ‖logDeriv (LFunction χ) z₀‖ ≤ 32 * D * L ^ 4 := by
    rw [logDeriv_apply]
    refine le_trans hdisk ?_
    rw [hlog2]
    have hA : Real.log (2 * M) - -Real.log 2 = Real.log (2*M) + Real.log 2 := by ring
    rw [hA]
    have hLnn : 0 < L := hLpos
    have h1 : 2 * (Real.log (2*M) + Real.log 2) ≤ 16 * L := by linarith [hlogM, hlog2le]
    have hnn1 : (0:ℝ) ≤ 2 * (Real.log (2*M) + Real.log 2) := by
      have hM2 : (1:ℝ) ≤ 2 * M := by linarith [hM1]
      have h5 : (0:ℝ) ≤ Real.log (2*M) := Real.log_nonneg hM2
      have h6 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    have hnn2 : (0:ℝ) ≤ (‖z₀-cc‖+δ)/((R-‖z₀-cc‖-δ)*δ) := by positivity
    have h2' : 2 * (Real.log (2*M) + Real.log 2) * ((‖z₀-cc‖+δ)/((R-‖z₀-cc‖-δ)*δ))
        ≤ (16*L) * (2/δ^2) := mul_le_mul h1 hfrac hnn2 (by positivity)
    have h3 : (16*L) * (2/δ^2) = 32 * L / δ^2 := by ring
    have hδ2 : (0:ℝ) < δ^2 := by positivity
    have h2 : 2 * (Real.log (2*M) + Real.log 2) * (‖z₀-cc‖+δ) / ((R-‖z₀-cc‖-δ)*δ)
        ≤ 32 * L / δ^2 := by
      rw [mul_div_assoc, ← h3]
      exact h2'
    have h5 : (32:ℝ) * L / δ^2 ≤ 32 * D * L^4 := by
      have h4 : (32:ℝ) * L / δ^2 = 32 * L * (1/δ^2) := by ring
      rw [h4]
      calc 32 * L * (1/δ^2) ≤ 32 * L * (D * L^3) := by
            apply mul_le_mul_of_nonneg_left hδlo (by linarith [hLpos])
        _ = 32 * D * L^4 := by ring
    exact le_trans h2 h5
  refine ⟨?_, ?_⟩
  · intro h0
    exact hzf _ hzg h0
  · simpa only [hz₀def] using hkey


/-- The Perron integrand for `χ`: `−(L′/L)(s,χ)·x^s/s`. -/
private noncomputable def chiG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) (s : ℂ) : ℂ :=
  (-(deriv (LFunction χ) s) / (LFunction χ s)) * (x : ℂ) ^ s / s

/-- The truncated Perron integral of `χ` along the line `Re s = 1 + 1/log x`. -/
private noncomputable def chiPerron {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) *
    ∫ t in (-T)..T,
      chiG χ x (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)

private lemma cpow_diff {x : ℝ} (hx : 0 < x) : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) := by
  have h : (fun s : ℂ => (x : ℂ) ^ s) =
      fun s : ℂ => Complex.exp ((Real.log x : ℂ) * s) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hx)), Complex.ofReal_log hx.le]
  rw [h]; fun_prop

private lemma chiG_differentiableOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {U : Set ℂ}
    (h0 : ∀ s ∈ U, s ≠ 0) (hL : ∀ s ∈ U, LFunction χ s ≠ 0) :
    DifferentiableOn ℂ (chiG χ x) U := by
  intro s hs
  change DifferentiableWithinAt ℂ
    (fun s : ℂ => (-(deriv (LFunction χ) s) / LFunction χ s) * (x : ℂ) ^ s / s) U s
  have hLd : DifferentiableAt ℂ (LFunction χ) s := (differentiable_LFunction hχ).differentiableAt
  have hLdd : DifferentiableAt ℂ (fun z : ℂ => deriv (LFunction χ) z) s :=
    ((differentiable_LFunction hχ).deriv).differentiableAt
  have h1 : DifferentiableAt ℂ (fun z : ℂ => -(deriv (LFunction χ) z) / LFunction χ z) s :=
    (hLdd.neg).div hLd (hL s hs)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s :=
    (cpow_diff hx).differentiableAt
  have h3 : DifferentiableAt ℂ (fun z : ℂ => (-(deriv (LFunction χ) z) / LFunction χ z) *
      (x : ℂ) ^ z) s := h1.mul h2
  exact (h3.div differentiableAt_id (h0 s hs)).differentiableWithinAt


private lemma chiG_differentiableAt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h0 : s ≠ 0) (hL : LFunction χ s ≠ 0) : DifferentiableAt ℂ (chiG χ x) s := by
  change DifferentiableAt ℂ
    (fun s : ℂ => (-(deriv (LFunction χ) s) / LFunction χ s) * (x : ℂ) ^ s / s) s
  have hLd : DifferentiableAt ℂ (LFunction χ) s := (differentiable_LFunction hχ).differentiableAt
  have hLdd : DifferentiableAt ℂ (fun z : ℂ => deriv (LFunction χ) z) s :=
    ((differentiable_LFunction hχ).deriv).differentiableAt
  have h1 : DifferentiableAt ℂ (fun z : ℂ => -(deriv (LFunction χ) z) / LFunction χ z) s :=
    (hLdd.neg).div hLd hL
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s := (cpow_diff hx).differentiableAt
  exact ((h1.mul h2).div differentiableAt_id h0)

private lemma chiG_norm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) (s : ℂ)
    (hs : s ≠ 0) :
    ‖chiG χ x s‖ = ‖logDeriv (LFunction χ) s‖ * x ^ s.re / ‖s‖ := by
  have hlog : -(deriv (LFunction χ) s) / LFunction χ s = -logDeriv (LFunction χ) s := by
    rw [logDeriv_apply]; ring
  rw [chiG, hlog, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- The contour-shift identity for the twisted Perron integral: since `−L′/L·x^s/s` is
analytic on the rectangle (no poles), the right edge decomposes into the three other edges. -/
private lemma chiPerron_rect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x T σ₁ : ℝ} (hx : 1 < x) (hT : 0 < T) (hσ₁ : 0 < σ₁)
    (hσ₁lt : σ₁ < 1 + 1 / Real.log x)
    (hL0 : ∀ s : ℂ, s.re ∈ Set.Icc σ₁ (1 + 1 / Real.log x) → |s.im| ≤ T →
      LFunction χ s ≠ 0) :
    chiPerron χ x T =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        ((∫ u in σ₁..(1 + 1 / Real.log x),
            chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)) -
         (∫ u in σ₁..(1 + 1 / Real.log x),
            chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I))) +
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  set z : ℂ := (σ₁ : ℂ) - Complex.I * (T : ℂ) with hz
  set w : ℂ := (((1 + 1 / Real.log x : ℝ) : ℂ)) + Complex.I * (T : ℂ) with hw
  have hzre : z.re = σ₁ := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hwre : w.re = 1 + 1 / Real.log x := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hzr_lt : z.re < w.re := by rw [hzre, hwre]; exact hσ₁lt
  have hzi_lt : z.im < w.im := by rw [hzim, hwim]; linarith
  have hdiff : DifferentiableOn ℂ (chiG χ x) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    refine chiG_differentiableOn χ hχ (by linarith : (0:ℝ) < x) ?_ ?_
    · intro s hs
      intro h0
      have h1 := (Complex.mem_reProdIm.mp hs).1
      rw [h0] at h1
      rw [Set.uIcc_of_le (le_of_lt hzr_lt), hzre, hwre] at h1
      simp at h1
      linarith [hσ₁]
    · intro s hs
      have h1 := (Complex.mem_reProdIm.mp hs).1
      have h2 := (Complex.mem_reProdIm.mp hs).2
      rw [Set.uIcc_of_le (le_of_lt hzr_lt), hzre, hwre] at h1
      rw [hzim, hwim] at h2
      rw [Set.uIcc_of_le (by linarith : (-T:ℝ) ≤ T)] at h2
      exact hL0 s h1 (by rw [abs_le]; exact ⟨h2.1, h2.2⟩)
  have hzero : Commons.NumberTheory.Zeta.rectInt z w (chiG χ x) = 0 := by
    have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (chiG χ x) z w hdiff
    simpa [Commons.NumberTheory.Zeta.rectInt] using hc
  rw [Commons.NumberTheory.Zeta.rectInt] at hzero
  simp only [smul_eq_mul] at hzero
  -- identify the edges
  have hbot : (∫ (u : ℝ) in z.re..w.re, chiG χ x ((u : ℂ) + (z.im : ℂ) * Complex.I))
      = ∫ (u : ℝ) in σ₁..(1 + 1 / Real.log x),
          chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I) := by
    rw [hzre, hwre]
    apply intervalIntegral.integral_congr
    intro u _
    apply congrArg (chiG χ x)
    rw [hzim]
    push_cast
    ring
  have htop : (∫ (u : ℝ) in z.re..w.re, chiG χ x ((u : ℂ) + (w.im : ℂ) * Complex.I))
      = ∫ (u : ℝ) in σ₁..(1 + 1 / Real.log x),
          chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I) := by
    rw [hzre, hwre]
    apply intervalIntegral.integral_congr
    intro u _
    apply congrArg (chiG χ x)
    rw [hwim]
  have hright : (∫ (y : ℝ) in z.im..w.im,
        chiG χ x ((w.re : ℂ) + (y : ℂ) * Complex.I))
      = ∫ (y : ℝ) in (-T)..T,
          chiG χ x ((((1 + 1 / Real.log x : ℝ) : ℂ)) + (y : ℂ) * Complex.I) := by
    rw [hzim, hwim, hwre]
  have hleft : (∫ (y : ℝ) in z.im..w.im,
        chiG χ x ((z.re : ℂ) + (y : ℂ) * Complex.I))
      = ∫ (y : ℝ) in (-T)..T, chiG χ x ((σ₁ : ℂ) + (y : ℂ) * Complex.I) := by
    rw [hzim, hwim, hzre]
  rw [hbot, htop, hright, hleft] at hzero
  set Bi : ℂ := ∫ (u : ℝ) in σ₁..(1 + 1 / Real.log x),
      chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I) with hBi
  set Ti : ℂ := ∫ (u : ℝ) in σ₁..(1 + 1 / Real.log x),
      chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I) with hTi
  set Ri : ℂ := ∫ (y : ℝ) in (-T)..T,
      chiG χ x ((((1 + 1 / Real.log x : ℝ) : ℂ)) + (y : ℂ) * Complex.I) with hRi
  set Li : ℂ := ∫ (t : ℝ) in (-T)..T, chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I) with hLi
  have hR2 : Complex.I * Ri = Ti - Bi + Complex.I * Li := by
    linear_combination hzero
  have hII : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I]; ring
  have hRt : Ri = -Complex.I * Ti + Complex.I * Bi + Li := by
    calc Ri = -Complex.I * (Complex.I * Ri) := by
          rw [← mul_assoc, hII]; ring
      _ = -Complex.I * (Ti - Bi + Complex.I * Li) := by rw [hR2]
      _ = -Complex.I * Ti + Complex.I * Bi + Li := by
          rw [mul_add, mul_sub, ← mul_assoc, hII]; ring
  have hPeq : chiPerron χ x T = (1 / (2 * (Real.pi : ℂ))) * Ri := by
    rw [chiPerron, hRi]
  rw [hPeq, hRt]
  have hI : (1 / (2 * (Real.pi : ℂ) * Complex.I)) = -Complex.I / (2 * (Real.pi : ℂ)) := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I) = (2 * (Real.pi : ℂ)) * Complex.I by ring]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, Complex.inv_I]
    ring
  rw [hI]
  ring

private lemma chiG_eq_LSeries {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 < s.re) (hs0 : s ≠ 0) :
    chiG χ x s = LSeries (fun n : ℕ => (χ (n : ZMod N) : ℂ) *
        (ArithmeticFunction.vonMangoldt n : ℂ)) s * (x : ℂ) ^ s / s := by
  have h1 : LSeries (fun n : ℕ => (χ (n : ZMod N) : ℂ) *
      (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s :=
    LSeries_congr (fun {n} _ => by ring) s
  have h2 := LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs
  rw [logDeriv_apply] at h2
  have h3 : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) s = -(deriv (LFunction χ) s / LFunction χ s) := by
    rw [h2]
    ring
  have h4 : LSeries (fun n : ℕ => (χ (n : ZMod N) : ℂ) *
      (ArithmeticFunction.vonMangoldt n : ℂ)) s = -(deriv (LFunction χ) s / LFunction χ s) := by
    rw [h1]; exact h3
  have h5 : chiG χ x s = (-(deriv (LFunction χ) s) / LFunction χ s) * (x : ℂ) ^ s / s := rfl
  rw [h5, neg_div, h4]

/-- The truncated Perron bound for `χ` in terms of `chiPerron`. -/
private lemma psiChi_trunc_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - chiPerron χ x T‖ ≤
        C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨Ctr, hCtr, htrunc⟩ := chebyshevPsiChi_truncatedPerron χ
  refine ⟨Ctr, hCtr, ?_⟩
  intro x T hx hT
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hs0 : 1 < 1 + 1 / Real.log x := by
    have h : 0 < 1 / Real.log x := one_div_pos.mpr hlogx
    linarith
  have hkey : chiPerron χ x T = (1 / (2 * Real.pi)) *
      (∫ (t : ℝ) in (-T)..T,
        LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) := by
    rw [chiPerron]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    beta_reduce
    rw [show ((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I =
        ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ) by ring]
    have hsre : 1 < (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re := by
      have hre : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re =
          1 + 1 / Real.log x := by simp [Complex.mul_re]
      rw [hre]; exact hs0
    have hsne0 : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
      intro h0
      have h1 : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re = 0 := by
        rw [h0]; simp
      have hre : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re =
          1 + 1 / Real.log x := by simp [Complex.mul_re]
      rw [hre] at h1
      linarith [hs0]
    exact chiG_eq_LSeries χ hχ (by linarith : (0:ℝ) < x) hsre hsne0
  have h := htrunc x hx T hT
  rw [hkey]
  exact h

private lemma chiPerron_bound_uniform {cOff cReal : ℝ} (hcOffpos : 0 < cOff) (hcRealpos : 0 < cReal)
    (hOff : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ (σ t : ℝ), t ≠ 0 → 1 - cOff / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
      LFunction χ ((σ : ℂ) + (t : ℂ) * I) ≠ 0)
    (hReal : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      χ * χ ≠ 1 → ∀ σ : ℝ, 1 - cReal / Real.log (2 * (N : ℝ)) ≤ σ →
      LFunction χ (σ : ℂ) ≠ 0)
    (ε Cs D : ℝ) (hε : 0 < ε) (hCs : 0 < Cs) (hD : 0 < D)
    (hSiegel : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 →
      LFunction χ (β : ℂ) = 0 → Cs * (N : ℝ) ^ (-ε) ≤ 1 - β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
        (hχprim : χ.IsPrimitive) (x T δ : ℝ), 3 ≤ x → 3 ≤ T → 0 < δ →
        δ ≤ boxC cOff cReal / Real.log ((N : ℝ) * (T + 3)) →
        δ ≤ Cs * (N : ℝ) ^ (-ε) / 4 →
        1 ≤ Real.log ((N : ℝ) * (T + 3)) →
        1 / δ ^ 2 ≤ D * (Real.log ((N : ℝ) * (T + 3))) ^ 3 →
        ‖chiPerron χ x T‖ ≤ C * ((Real.log ((N : ℝ) * (T + 3))) ^ 5 *
            x ^ (1 - δ)
          + (Real.log ((N : ℝ) * (T + 3))) ^ 5 * x ^ (1 + 1 / Real.log x) / T) := by
  obtain ⟨Cb, hCb, hbox⟩ := logDeriv_box_uniform hcOffpos hcRealpos hOff hReal ε Cs D hε hCs hD hSiegel
  refine ⟨12 * Cb, by positivity, ?_⟩
  intro N _inst χ hχ hχprim x T δ hx hT hδpos hδc hδS hL1in hδlo
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  set L : ℝ := Real.log ((N : ℝ) * (T + 3)) with hLdef
  have hL1 : 1 ≤ L := hL1in
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hlogT : Real.log T ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by linarith)
    nlinarith [hN1]
  set σ₁ : ℝ := 1 - δ with hσdef
  have hc0le8 : boxC cOff cReal ≤ 1 / 8 := by rw [boxC]; exact min_le_right _ _
  have hc0nn : 0 ≤ boxC cOff cReal := by rw [boxC]; positivity
  have hδle12 : δ ≤ 1 / 2 := by
    have h2 : boxC cOff cReal / L ≤ boxC cOff cReal := by
      rw [div_le_iff₀ hLpos]; nlinarith [hc0nn, hL1]
    linarith [hδc, h2, hc0le8]
  have hσhalf : 1 / 2 ≤ σ₁ := by
    have h2 : σ₁ = 1 - δ := hσdef
    linarith
  have hσpos : 0 < σ₁ := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := log_ge_one_of_three_le (by linarith)
  set s₀ : ℝ := 1 + 1 / Real.log x with hs0def
  have hinvx : 0 < 1 / Real.log x := one_div_pos.mpr hlogx
  have hs0le2 : s₀ ≤ 2 := by
    have h1 : 1 / Real.log x ≤ 1 := by rw [div_le_one hlogx]; exact hlogx1
    have h2 : s₀ = 1 + 1 / Real.log x := hs0def
    linarith
  have hs0pos : 0 < s₀ := by
    have h2 : s₀ = 1 + 1 / Real.log x := hs0def
    linarith
  have hσlt : σ₁ < s₀ := by
    have h2 : σ₁ = 1 - δ := hσdef
    have h3 : s₀ = 1 + 1 / Real.log x := hs0def
    linarith [hδpos, hinvx]
  have hδcb : δ ≤ boxC cOff cReal / L := hδc
  have hL0 : ∀ s : ℂ, s.re ∈ Set.Icc σ₁ s₀ → |s.im| ≤ T → LFunction χ s ≠ 0 := by
    intro s hs1 hs2
    have h4 : s.re ≤ 2 := le_trans hs1.2 hs0le2
    have h6 : σ₁ = 1 - δ := hσdef
    have h1 : 1 - δ ≤ s.re := by linarith [hs1.1, h6]
    have h5 := (hbox N χ hχ hχprim T δ hT hδpos hδcb hδS hL1 hδlo s.re s.im hs2 h1 h4).1
    rw [show s = ((s.re : ℂ) + (s.im : ℂ) * Complex.I) from (Complex.re_add_im s).symm]
    exact h5
  have hnormB : ∀ (u r : ℝ), u ∈ Set.Icc σ₁ s₀ → |r| ≤ T →
      ‖logDeriv (LFunction χ) ((u : ℂ) + (r : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 := by
    intro u r hu hr
    have h6 : σ₁ = 1 - δ := hσdef
    have h1 : 1 - δ ≤ u := by linarith [hu.1, h6]
    have h2 : u ≤ 2 := le_trans hu.2 hs0le2
    have h3 := (hbox N χ hχ hχprim T δ hT hδpos hδcb hδS hL1 hδlo u r hr h1 h2).2
    exact h3
  have hrect := chiPerron_rect χ hχ (by linarith : (1 : ℝ) < x) hTpos hσpos hσlt hL0
  have hcontSeg : ContinuousOn (fun t : ℝ => chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I))
      (Set.uIcc (-T) T) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at ht
    have htabs : |t| ≤ T := by rw [abs_le]; exact ⟨ht.1, ht.2⟩
    have hs0ne : ((σ₁ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have h1 : ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h0]; simp
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, sub_zero] at h1
      linarith [h1, hσpos]
    have hLne : LFunction χ ((σ₁ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
      hL0 _ ⟨by simp, by simpa using hσlt.le⟩ (by simpa using htabs)
    have hc0 := chiG_differentiableAt χ hχ hxpos hs0ne hLne
    have h1 : Tendsto (fun t : ℝ => ((σ₁ : ℂ) + (t : ℂ) * Complex.I))
        (𝓝[Set.uIcc (-T) T] t) (𝓝 ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousWithinAt
    exact hc0.continuousAt.tendsto.comp h1
  -- top edge
  have htop : ‖∫ u in σ₁..s₀, chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) := by
    have hpt : ∀ u ∈ Set.uIoc σ₁ s₀,
        ‖chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 * x ^ s₀ / T := by
      intro u hu
      rw [Set.uIoc, min_eq_left (le_of_lt hσlt), max_eq_right (le_of_lt hσlt)] at hu
      have huI : u ∈ Set.Icc σ₁ s₀ := ⟨le_of_lt hu.1, hu.2⟩
      have h1 : ‖chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 * x ^ u / T := by
        have hs : ((u : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
          intro h0
          have h2 : ((u : ℂ) + (T : ℂ) * Complex.I).re = 0 := by rw [h0]; simp
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_zero, mul_one, sub_zero] at h2
          linarith [h2, huI.1, hσpos]
        have hre : ((u : ℂ) + (T : ℂ) * Complex.I).re = u := by simp
        have hnk : T ≤ ‖((u : ℂ) + (T : ℂ) * Complex.I)‖ := by
          have h1 : |((u : ℂ) + (T : ℂ) * Complex.I).im| ≤
              ‖((u : ℂ) + (T : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
          have h2 : ((u : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
          rw [h2, abs_of_pos hTpos] at h1
          exact h1
        have hb := hnormB u T huI (by rw [abs_of_pos hTpos])
        rw [chiG_norm χ hxpos _ hs, hre]
        have hbs := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hxpos.le u)
        have hnkpos : 0 < ‖((u : ℂ) + (T : ℂ) * Complex.I)‖ := by linarith [hnk, hTpos]
        calc ‖logDeriv (LFunction χ) ((u : ℂ) + (T : ℂ) * Complex.I)‖ * x ^ u /
              ‖((u : ℂ) + (T : ℂ) * Complex.I)‖
            ≤ (Cb * L ^ 4) * x ^ u / ‖((u : ℂ) + (T : ℂ) * Complex.I)‖ :=
              div_le_div_of_nonneg_right hbs (le_of_lt hnkpos)
          _ ≤ (Cb * L ^ 4) * x ^ u / T :=
              div_le_div_of_nonneg_left (by positivity) hTpos hnk
          _ = Cb * L ^ 4 * x ^ u / T := by ring
      have h2 : x ^ u ≤ x ^ s₀ := Real.rpow_le_rpow_of_exponent_le hx1 hu.2
      have h5 : Cb * L ^ 4 * x ^ u ≤ Cb * L ^ 4 * x ^ s₀ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      calc ‖chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 * x ^ u / T := h1
        _ ≤ Cb * L ^ 4 * x ^ s₀ / T := div_le_div_of_nonneg_right h5 hTpos.le
    calc ‖∫ u in σ₁..s₀, chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ (Cb * L ^ 4 * x ^ s₀ / T) * |s₀ - σ₁| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (f := fun u : ℝ => chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I))
            (C := Cb * L ^ 4 * x ^ s₀ / T) hpt
      _ = (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) := by rw [abs_of_pos (by linarith)]
  -- bottom edge
  have hbot : ‖∫ u in σ₁..s₀, chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I)‖
      ≤ (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) := by
    have hpt : ∀ u ∈ Set.uIoc σ₁ s₀,
        ‖chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 * x ^ s₀ / T := by
      intro u hu
      rw [Set.uIoc, min_eq_left (le_of_lt hσlt), max_eq_right (le_of_lt hσlt)] at hu
      have huI : u ∈ Set.Icc σ₁ s₀ := ⟨le_of_lt hu.1, hu.2⟩
      have h1 : ‖chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 * x ^ u / T := by
        have hs : ((u : ℂ) - (T : ℂ) * Complex.I) ≠ 0 := by
          intro h0
          have h2 : ((u : ℂ) - (T : ℂ) * Complex.I).re = 0 := by rw [h0]; simp
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_zero, mul_one, sub_zero] at h2
          linarith [h2, huI.1, hσpos]
        have hre : ((u : ℂ) - (T : ℂ) * Complex.I).re = u := by simp
        have hnk : T ≤ ‖((u : ℂ) - (T : ℂ) * Complex.I)‖ := by
          have h1 : |((u : ℂ) - (T : ℂ) * Complex.I).im| ≤
              ‖((u : ℂ) - (T : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
          have h2 : ((u : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
          rw [h2, abs_neg, abs_of_pos hTpos] at h1
          exact h1
        have hb0 := hnormB u (-T) huI (by rw [abs_neg, abs_of_pos hTpos])
        have hb : ‖logDeriv (LFunction χ) ((u : ℂ) - (T : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 := by
          convert hb0 using 1
          push_cast; ring
        rw [chiG_norm χ hxpos _ hs, hre]
        have hbs := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hxpos.le u)
        have hnkpos : 0 < ‖((u : ℂ) - (T : ℂ) * Complex.I)‖ := by linarith [hnk, hTpos]
        calc ‖logDeriv (LFunction χ) ((u : ℂ) - (T : ℂ) * Complex.I)‖ * x ^ u /
              ‖((u : ℂ) - (T : ℂ) * Complex.I)‖
            ≤ (Cb * L ^ 4) * x ^ u / ‖((u : ℂ) - (T : ℂ) * Complex.I)‖ :=
              div_le_div_of_nonneg_right hbs (le_of_lt hnkpos)
          _ ≤ (Cb * L ^ 4) * x ^ u / T :=
              div_le_div_of_nonneg_left (by positivity) hTpos hnk
          _ = Cb * L ^ 4 * x ^ u / T := by ring
      have h2 : x ^ u ≤ x ^ s₀ := Real.rpow_le_rpow_of_exponent_le hx1 hu.2
      have h5 : Cb * L ^ 4 * x ^ u ≤ Cb * L ^ 4 * x ^ s₀ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      calc ‖chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I)‖ ≤ Cb * L ^ 4 * x ^ u / T := h1
        _ ≤ Cb * L ^ 4 * x ^ s₀ / T := div_le_div_of_nonneg_right h5 hTpos.le
    calc ‖∫ u in σ₁..s₀, chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I)‖
        ≤ (Cb * L ^ 4 * x ^ s₀ / T) * |s₀ - σ₁| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (f := fun u : ℝ => chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I))
            (C := Cb * L ^ 4 * x ^ s₀ / T) hpt
      _ = (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) := by rw [abs_of_pos (by linarith)]
  -- left edge
  have hleft : ‖∫ t in (-T)..T, chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 12 * Cb * L ^ 5 * x ^ σ₁ := by
    have hpoint : ∀ t ∈ Set.Icc (-T) T,
        ‖chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          (Cb * L ^ 4 * x ^ σ₁) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ := by
      intro t ht
      have htabs : |t| ≤ T := by rw [abs_le]; exact ⟨ht.1, ht.2⟩
      have hs : ((σ₁ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        intro h0
        have h2 : ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h0]; simp
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero, mul_one, sub_zero] at h2
        linarith [h2, hσpos]
      have hre : ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = σ₁ := by simp
      have hsq : Real.sqrt (1 / 4 + t ^ 2) ≤ ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [← Real.sqrt_sq (norm_nonneg _)]
        apply Real.sqrt_le_sqrt
        have h1 : ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = σ₁ ^ 2 + t ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, Complex.add_im, Complex.mul_im]
          ring
        rw [h1]; nlinarith [hσhalf]
      have hb := hnormB σ₁ t ⟨le_refl _, le_of_lt hσlt⟩ htabs
      rw [chiG_norm χ hxpos _ hs, hre]
      have hspos : 0 < Real.sqrt (1 / 4 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hLHS : ‖logDeriv (LFunction χ) ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ * x ^ σ₁ ≤
          (Cb * L ^ 4) * x ^ σ₁ :=
        mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hxpos.le σ₁)
      calc ‖logDeriv (LFunction χ) ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ * x ^ σ₁ /
            ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (Cb * L ^ 4) * x ^ σ₁ / ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ :=
            div_le_div_of_nonneg_right hLHS (norm_nonneg _)
        _ ≤ (Cb * L ^ 4) * x ^ σ₁ / Real.sqrt (1 / 4 + t ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) hspos hsq
        _ = (Cb * L ^ 4 * x ^ σ₁) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ := by
            rw [div_eq_mul_inv]
    have hFint : IntervalIntegrable (fun t : ℝ => ‖chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖)
        volume (-T) T := hcontSeg.norm.intervalIntegrable
    have hGcont : ContinuousOn (fun t : ℝ => (Real.sqrt (1 / 4 + t ^ 2))⁻¹) (Set.uIcc (-T) T) := by
      apply ContinuousOn.inv₀
      · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
      · intro t ht
        exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hGint : IntervalIntegrable (fun t : ℝ =>
        (Cb * L ^ 4 * x ^ σ₁) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹) volume (-T) T :=
      (continuousOn_const.mul hGcont).intervalIntegrable
    have hmono : (∫ t : ℝ in (-T)..T,
          ‖chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        ∫ t : ℝ in (-T)..T, (Cb * L ^ 4 * x ^ σ₁) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ :=
      intervalIntegral.integral_mono_on (by linarith) hFint hGint hpoint
    have hval : (∫ t : ℝ in (-T)..T, (Cb * L ^ 4 * x ^ σ₁) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹)
        = (Cb * L ^ 4 * x ^ σ₁) * (∫ t : ℝ in (-T)..T, (Real.sqrt (1 / 4 + t ^ 2))⁻¹) :=
      intervalIntegral.integral_const_mul _ _
    have hub := Commons.Analysis.Integral.integral_inv_sqrt_quarter_add_sq_le T hT1
    have hlogTle : 4 + 2 * Real.log T ≤ 6 * L := by linarith
    calc ‖∫ t in (-T)..T, chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ∫ t : ℝ in (-T)..T, ‖chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ t : ℝ in (-T)..T, (Cb * L ^ 4 * x ^ σ₁) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ := hmono
      _ = (Cb * L ^ 4 * x ^ σ₁) * (∫ t : ℝ in (-T)..T, (Real.sqrt (1 / 4 + t ^ 2))⁻¹) := hval
      _ ≤ (Cb * L ^ 4 * x ^ σ₁) * (4 + 2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hub (by positivity)
      _ ≤ 12 * Cb * L ^ 5 * x ^ σ₁ := by
          have hxσ : (0:ℝ) ≤ x ^ σ₁ := Real.rpow_nonneg hxpos.le σ₁
          have hnn : (0:ℝ) ≤ Cb * L ^ 4 * x ^ σ₁ := by positivity
          have h1 : (Cb * L ^ 4 * x ^ σ₁) * (4 + 2 * Real.log T) ≤
              (Cb * L ^ 4 * x ^ σ₁) * (6 * L) := mul_le_mul_of_nonneg_left hlogTle hnn
          have h2 : (Cb * L ^ 4 * x ^ σ₁) * (6 * L) = 6 * (Cb * L ^ 4 * x ^ σ₁) * L := by ring
          have h3 : 6 * (Cb * L ^ 4 * x ^ σ₁) * L ≤ 12 * Cb * L ^ 5 * x ^ σ₁ := by
            nlinarith [hnn, hLpos, hxσ]
          linarith [h1, h2, h3]
  -- combine
  rw [hrect]
  have h1 : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      ((∫ u in σ₁..s₀, chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)) -
       (∫ u in σ₁..s₀, chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I)))‖
      ≤ (1 / (2 * Real.pi)) * ((Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) +
        (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁)) := by
    have hI : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one]
      simp [Real.pi_pos.le]
    rw [norm_mul, hI]
    have h2 : ‖(∫ u in σ₁..s₀, chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)) -
        (∫ u in σ₁..s₀, chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I))‖ ≤
        (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) + (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) := by
      have hsub := norm_sub_le (∫ u in σ₁..s₀, chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I))
        (∫ u in σ₁..s₀, chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I))
      linarith [hsub, htop, hbot]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h3 : ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (1 / (2 * Real.pi)) * (12 * Cb * L ^ 5 * x ^ σ₁) := by
    have hI : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div]
      simp [Real.pi_pos.le]
    rw [norm_mul, hI]
    exact mul_le_mul_of_nonneg_left hleft (by positivity)
  have h4 : (s₀ - σ₁) ≤ 3 / 2 := by linarith [hσhalf, hs0le2]
  have hsum : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      ((∫ u in σ₁..s₀, chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)) -
       (∫ u in σ₁..s₀, chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I))) +
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (1 / (2 * Real.pi)) * ((Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) +
          (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁)) +
        (1 / (2 * Real.pi)) * (12 * Cb * L ^ 5 * x ^ σ₁) := by
    have hsub := norm_add_le ((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      ((∫ u in σ₁..s₀, chiG χ x ((u : ℂ) + (T : ℂ) * Complex.I)) -
       (∫ u in σ₁..s₀, chiG χ x ((u : ℂ) - (T : ℂ) * Complex.I))))
      ((1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, chiG χ x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)))
    linarith [hsub, h1, h3]
  refine le_trans hsum ?_
  have hxσ : (0:ℝ) ≤ x ^ σ₁ := Real.rpow_nonneg hxpos.le σ₁
  have hxt : (0:ℝ) ≤ x ^ s₀ := Real.rpow_nonneg hxpos.le s₀
  have hpi : (1 / (2 * Real.pi)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hfin : (1 / (2 * Real.pi)) * ((Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) +
        (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁)) +
      (1 / (2 * Real.pi)) * (12 * Cb * L ^ 5 * x ^ σ₁)
      ≤ 12 * Cb * (L ^ 5 * x ^ σ₁ + L ^ 5 * x ^ s₀ / T) := by
    have hhalf1 : (1 / (2 * Real.pi)) ≤ 1 / 2 := by
      have h := one_div_le_one_div_of_le (a := (2:ℝ)) (b := 2 * Real.pi) (by norm_num)
        (by linarith [Real.pi_gt_three])
      simpa [mul_comm] using h
    have hA : (0:ℝ) ≤ Cb * L ^ 4 * x ^ s₀ / T := by positivity
    have hB : (0:ℝ) ≤ 12 * Cb * L ^ 5 * x ^ σ₁ := by positivity
    have hC1 : (0:ℝ) ≤ Cb * L ^ 5 * x ^ σ₁ := by positivity
    have hC2 : (0:ℝ) ≤ Cb * L ^ 5 * x ^ s₀ / T := by positivity
    have hslpos : 0 < s₀ - σ₁ := by linarith [hσlt]
    have hL45 : L ^ 4 ≤ L ^ 5 := by
      calc L ^ 4 = L ^ 4 * 1 := by ring
        _ ≤ L ^ 4 * L := mul_le_mul_of_nonneg_left hL1 (by positivity)
        _ = L ^ 5 := by ring
    have hx : (0:ℝ) ≤ x ^ s₀ := Real.rpow_nonneg hxpos.le s₀
    have hX : (0:ℝ) ≤ 2 * (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) := by nlinarith [hA, hslpos]
    have h1 : (3 / 2) * (Cb * L ^ 4 * x ^ s₀ / T) ≤ 12 * Cb * L ^ 5 * x ^ s₀ / T := by
      have h2 : (3 / 2) * Cb * L ^ 4 * x ^ s₀ ≤ 12 * Cb * L ^ 5 * x ^ s₀ := by
        have h5 : (3 / 2) * Cb * x ^ s₀ * L ^ 4 ≤ (3 / 2) * Cb * x ^ s₀ * L ^ 5 :=
          mul_le_mul_of_nonneg_left hL45 (by positivity)
        have h6 : (3 / 2) * Cb * x ^ s₀ * L ^ 5 ≤ 12 * Cb * x ^ s₀ * L ^ 5 := by
          have h7 : (0:ℝ) ≤ Cb * x ^ s₀ * L ^ 5 := by positivity
          nlinarith [h7]
        linarith [h5, h6]
      have h3 : (3 / 2) * (Cb * L ^ 4 * x ^ s₀ / T) = ((3 / 2) * Cb * L ^ 4 * x ^ s₀) / T := by ring
      rw [h3]
      exact div_le_div_of_nonneg_right h2 hTpos.le
    calc (1 / (2 * Real.pi)) * ((Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) +
            (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁)) +
          (1 / (2 * Real.pi)) * (12 * Cb * L ^ 5 * x ^ σ₁)
        = (1 / (2 * Real.pi)) * (2 * (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁)) +
            (1 / (2 * Real.pi)) * (12 * Cb * L ^ 5 * x ^ σ₁) := by ring
      _ ≤ (1 / 2) * (2 * (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁)) +
            (1 / 2) * (12 * Cb * L ^ 5 * x ^ σ₁) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hhalf1 hX
          · exact mul_le_mul_of_nonneg_right hhalf1 hB
      _ = (Cb * L ^ 4 * x ^ s₀ / T) * (s₀ - σ₁) + 6 * Cb * L ^ 5 * x ^ σ₁ := by ring
      _ ≤ (3 / 2) * (Cb * L ^ 4 * x ^ s₀ / T) + 6 * Cb * L ^ 5 * x ^ σ₁ := by
          nlinarith [hA, h4, hslpos]
      _ ≤ 12 * Cb * (L ^ 5 * x ^ σ₁ + L ^ 5 * x ^ s₀ / T) := by
          have h3 : (0:ℝ) ≤ 6 * Cb * L ^ 5 * x ^ σ₁ := by positivity
          have hR : 12 * Cb * (L ^ 5 * x ^ σ₁ + L ^ 5 * x ^ s₀ / T)
              = 12 * Cb * L ^ 5 * x ^ σ₁ + 12 * Cb * L ^ 5 * x ^ s₀ / T := by ring
          rw [hR]
          nlinarith [h1, hC1]
  refine le_trans hfin ?_
  rw [hLdef, hσdef, hs0def]

/-! ## The final bound -/


private lemma psiChi_trunc_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1),
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - chiPerron χ x T‖ ≤
        C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  rcases Commons.NumberTheory.Zeta.mangoldtPerronError_bound with ⟨CA, hCApos, hCA⟩
  refine ⟨(32 / (2 * Real.pi)) * CA + 2, by positivity, ?_⟩
  intro N _ χ hχ x T hx hT
  have hm := chiPsi_sub_perron_main (χ := χ) hx hT
  have hA : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
      CA * (x * (Real.log x) ^ 2 / T + Real.log x) := (hCA x hx T hT).2
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hkey : perronInt χ x T = chiPerron χ x T := by
    rw [chiPerron, perronInt]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [show ((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I =
        ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ) by ring]
    have hs0 : 1 < 1 + 1 / Real.log x := by
      have : 0 < 1 / Real.log x := one_div_pos.mpr hlogxpos
      linarith
    have hsre : 1 < (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re := by
      have hre : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re =
          1 + 1 / Real.log x := by simp [Complex.mul_re]
      rw [hre]; exact hs0
    have hsne0 : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
      intro h0
      have h1 : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re = 0 := by
        rw [h0]; simp
      have hre : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re =
          1 + 1 / Real.log x := by simp [Complex.mul_re]
      rw [hre] at h1
      have : 0 < 1 / Real.log x := one_div_pos.mpr hlogxpos
      linarith
    exact (chiG_eq_LSeries χ hχ (by linarith : (0:ℝ) < x) hsre hsne0).symm
  rw [hkey] at hm
  have hm' : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - chiPerron χ x T‖
      ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
            min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) + 2 * Real.log x := by
    simpa [chiLambda] using hm
  have hlogB : 2 * Real.log x ≤ 2 * (x * (Real.log x) ^ 2 / T + Real.log x) := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
    nlinarith
  have hBpos : 0 ≤ x * (Real.log x) ^ 2 / T + Real.log x := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
    linarith
  calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - chiPerron χ x T‖
      ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
            min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) + 2 * Real.log x := hm'
    _ ≤ (32 / (2 * Real.pi)) * (CA * (x * (Real.log x) ^ 2 / T + Real.log x)) +
          2 * Real.log x := by
          have hc : 0 ≤ (32 / (2 * Real.pi)) := by positivity
          nlinarith [hA]
    _ ≤ ((32 / (2 * Real.pi)) * CA + 2) * (x * (Real.log x) ^ 2 / T + Real.log x) := by
          nlinarith [hlogB, hBpos]

private lemma ev_log_le_rpow {r : ℝ} (hr : 0 < r) :
    ∀ᶠ y : ℝ in atTop, Real.log y ≤ y ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound (show (0:ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with y hy hy1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) r),
    one_mul] at hy
  exact le_trans (le_abs_self _) hy

private lemma ev_const_le_rpow {r : ℝ} (hr : 0 < r) (C : ℝ) :
    ∀ᶠ y : ℝ in atTop, C ≤ y ^ r := by
  by_cases hC : C ≤ 0
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    exact le_trans hC (Real.rpow_nonneg hy r)
  · push_neg at hC
    exact (tendsto_rpow_atTop hr).eventually_ge_atTop C

private lemma ev_pow_log_add_le_id (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    ∀ᶠ y : ℝ in atTop, (a * Real.log y + 5) ^ (k + 1) ≤ y := by
  set m : ℝ := 1 / (4 * ((k:ℝ) + 1)) with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  have h1 : ∀ᶠ y : ℝ in atTop, Real.log y ≤ (1 / (4 * (|a| + 1))) * y ^ m := by
    have h := (isLittleO_log_rpow_atTop hmpos).bound (show (0:ℝ) < 1/(4*(|a|+1)) by positivity)
    filter_upwards [h, eventually_ge_atTop (1:ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) m)] at hy
    exact le_trans (le_abs_self _) hy
  have h2 : ∀ᶠ y : ℝ in atTop, (20/3 : ℝ) ≤ y ^ m := ev_const_le_rpow hmpos (20/3)
  filter_upwards [h1, h2, eventually_ge_atTop (1:ℝ)] with y hy1 hy2 hyge1
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hlog1 : (0:ℝ) ≤ Real.log y := Real.log_nonneg hyge1
  have h3 : a * Real.log y + 5 ≤ y ^ m := by
    have h4 : a ≤ |a| := le_abs_self a
    have h5 : a * Real.log y ≤ |a| * Real.log y := mul_le_mul_of_nonneg_right h4 hlog1
    have h6 : |a| * Real.log y ≤ |a| * ((1/(4*(|a|+1))) * y^m) :=
      mul_le_mul_of_nonneg_left hy1 (abs_nonneg a)
    have h7 : |a| * ((1/(4*(|a|+1))) * y^m) ≤ (1/4) * y^m := by
      have h8 : (0:ℝ) ≤ y ^ m := Real.rpow_nonneg hy0 m
      have h9 : |a| / (4*(|a|+1)) ≤ 1/4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg a]
      calc |a| * ((1/(4*(|a|+1))) * y^m) = (|a|/(4*(|a|+1))) * y^m := by ring
        _ ≤ (1/4) * y^m := mul_le_mul_of_nonneg_right h9 h8
    have h8 : (0:ℝ) ≤ y ^ m := Real.rpow_nonneg hy0 m
    have h10 : (1/4) * y^m + 5 ≤ y^m := by nlinarith [hy2]
    linarith
  have h3nn : (0:ℝ) ≤ a * Real.log y + 5 := by nlinarith [ha, hlog1]
  have h11 : (a * Real.log y + 5) ^ (k+1) ≤ (y^m)^(k+1) :=
    pow_le_pow_left₀ h3nn h3 (k+1)
  calc (a * Real.log y + 5) ^ (k+1) ≤ (y^m)^(k+1) := h11
    _ = y ^ (m * (((k:ℕ) + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]
    _ = y ^ ((1:ℝ)/4) := by
        congr 1
        rw [hm]; push_cast; field_simp
    _ ≤ y ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hyge1 (by norm_num)
    _ = y := Real.rpow_one y

theorem psiChi_uniform_bound_primitive (A : ℝ) (hA : 0 < A) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      (N : ℝ) ≤ (Real.log x) ^ A →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
        ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) := by
  obtain ⟨Cs, hCs, hSieg0⟩ := LFunction_realZero_siegel_uniform (1 / (2 * A)) (by positivity)
  have hSiegel : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 →
      LFunction χ (β : ℂ) = 0 → Cs * (N : ℝ) ^ (-(1/(2 * A))) ≤ 1 - β := by
    intro N inst χ hprim hne hsq β h1 h2 h3
    exact hSieg0 N χ hprim hne hsq β h1 h2 h3
  obtain ⟨cOff, hcOffpos, hOff0⟩ := LFunction_zeroFree_offAxis_uniform
  obtain ⟨cReal, hcRealpos, hReal⟩ := LFunction_zeroFree_uniform_realAxis
  have hOff : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ (σ t : ℝ), t ≠ 0 → 1 - cOff / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
      LFunction χ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun N _ χ h1 h2 σ t ht h => hOff0 χ h1 h2 σ t ht h
  have hcBpos : 0 < boxC cOff cReal := by
    rw [boxC]; exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hcBle8 : boxC cOff cReal ≤ 1 / 8 := by rw [boxC]; exact min_le_right _ _
  set D : ℝ := max (1 / (boxC cOff cReal) ^ 2) (16 / Cs ^ 2) + 1 with hDdef
  have hDpos : 0 < D := by
    have h1 : (0:ℝ) < 1 / (boxC cOff cReal) ^ 2 := by positivity
    rw [hDdef]; linarith [le_max_left (1 / (boxC cOff cReal) ^ 2) (16 / Cs ^ 2)]
  obtain ⟨CP, hCPpos, hPerron⟩ :=
    chiPerron_bound_uniform hcOffpos hcRealpos hOff hReal (1 / (2 * A)) Cs D (by positivity)
      hCs hDpos hSiegel
  obtain ⟨Ctr, hCtrpos, htrunc⟩ := psiChi_trunc_uniform
  have hc3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3le12 : Real.log 3 ≤ 12 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) ≠ 1)
    linarith
  set c₁ : ℝ := min ((boxC cOff cReal / 3) * Real.log 3) (Cs * Real.sqrt (Real.log 3) / 4) with hc1def
  have hc1pos : 0 < c₁ := by
    rw [hc1def]
    exact lt_min (mul_pos (by positivity : (0:ℝ) < boxC cOff cReal / 3) hc3pos) (by positivity)
  have hc1leI : c₁ ≤ (boxC cOff cReal / 3) * Real.log 3 := by rw [hc1def]; exact min_le_left _ _
  have hc1leII : c₁ ≤ Cs * Real.sqrt (Real.log 3) / 4 := by rw [hc1def]; exact min_le_right _ _
  have hc1le : c₁ ≤ 1 / 2 := by
    have h1 : (boxC cOff cReal / 3) * Real.log 3 ≤ 1 / 2 := by
      have h2 : boxC cOff cReal / 3 ≤ 1 / 8 / 3 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith [hcBle8]
      have h3 : ((1:ℝ) / 8 / 3) * Real.log 3 ≤ 1 / 2 := by nlinarith [hlog3le12]
      have h5 : boxC cOff cReal / 3 * Real.log 3 ≤ ((1:ℝ) / 8 / 3) * Real.log 3 :=
        mul_le_mul_of_nonneg_right h2 hc3pos.le
      linarith
    linarith [hc1leI, h1]
  set cF : ℝ := c₁ / 2 with hcFdef
  have hcFpos : 0 < cF := by rw [hcFdef]; linarith
  have hcFle : cF ≤ 1 / 4 := by rw [hcFdef]; linarith
  have h1cFpos : 0 < 1 - cF := by linarith
  set Big : ℝ := Ctr + CP + CP * Real.exp 1 + 5 with hBigdef
  have hBigpos : 0 < Big := by rw [hBigdef]; positivity
  set Dbig : ℝ := Real.log Big + 20 + 100 / cF + 100 / (1 - cF) + 10 with hDbigdef
  have hDbig0 : 0 ≤ Dbig := by
    rw [hDbigdef]
    have h4 : (0:ℝ) ≤ 100 / cF := le_of_lt (div_pos (by norm_num) hcFpos)
    have h5 : (0:ℝ) ≤ 100 / (1 - cF) := le_of_lt (div_pos (by norm_num) h1cFpos)
    linarith [Real.log_nonneg (by nlinarith [hCtrpos, hCPpos, Real.exp_pos 1] : (1:ℝ) ≤ Big)]
  have hDbigCtr : Real.log Ctr ≤ Dbig := by
    rw [hDbigdef]
    have h1 : Real.log Ctr ≤ Real.log Big := by
      rw [hBigdef]; exact Real.log_le_log hCtrpos (by nlinarith [hCPpos, Real.exp_pos 1])
    have h4 : (0:ℝ) ≤ 100 / cF := le_of_lt (div_pos (by norm_num) hcFpos)
    have h5 : (0:ℝ) ≤ 100 / (1 - cF) := le_of_lt (div_pos (by norm_num) h1cFpos)
    linarith
  have hDbig_CP : Real.log (CP + 1) ≤ Dbig := by
    rw [hDbigdef]
    have h1 : Real.log (CP + 1) ≤ Real.log Big := by
      rw [hBigdef]
      apply Real.log_le_log (by positivity)
      nlinarith [hCtrpos, hCPpos, Real.exp_pos 1]
    have h4 : (0:ℝ) ≤ 100 / cF := le_of_lt (div_pos (by norm_num) hcFpos)
    have h5 : (0:ℝ) ≤ 100 / (1 - cF) := le_of_lt (div_pos (by norm_num) h1cFpos)
    linarith
  have hDbig_CPe : Real.log (CP * Real.exp 1 + 1) ≤ Dbig := by
    rw [hDbigdef]
    have h1 : Real.log (CP * Real.exp 1 + 1) ≤ Real.log Big := by
      rw [hBigdef]
      apply Real.log_le_log (by positivity)
      nlinarith [hCtrpos, hCPpos, Real.exp_pos 1]
    have h4 : (0:ℝ) ≤ 100 / cF := le_of_lt (div_pos (by norm_num) hcFpos)
    have h5 : (0:ℝ) ≤ 100 / (1 - cF) := le_of_lt (div_pos (by norm_num) h1cFpos)
    linarith
  have hDbig_cF : 100 / cF ≤ Dbig := by
    rw [hDbigdef]
    have h4 : (0:ℝ) ≤ 100 / (1 - cF) := le_of_lt (div_pos (by norm_num) h1cFpos)
    linarith [Real.log_nonneg (by nlinarith [hCtrpos, hCPpos, Real.exp_pos 1] : (1:ℝ) ≤ Big)]
  have hlog3Dbig : Real.log 3 ≤ Dbig := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) ≠ 1)
    have h20 : (2:ℝ) ≤ Dbig := by
      rw [hDbigdef]
      have h4 : (0:ℝ) ≤ 100 / cF := le_of_lt (div_pos (by norm_num) hcFpos)
      have h5 : (0:ℝ) ≤ 100 / (1 - cF) := le_of_lt (div_pos (by norm_num) h1cFpos)
      linarith [Real.log_nonneg (by nlinarith [hCtrpos, hCPpos, Real.exp_pos 1] : (1:ℝ) ≤ Big)]
    linarith
  have hfin : ∀ᶠ x : ℝ in atTop,
      (3 ≤ Real.log x) ∧
      ((A * Real.log (Real.log x) + 5) ^ 20 ≤ Real.log x) ∧
      (Real.log (Real.log x) ≤ (Real.log x) ^ ((1:ℝ)/40)) ∧
      (1000 * (Dbig + 1) ≤ (Real.log x) ^ ((19:ℝ)/80)) ∧
      (1000 * (Real.log x) ^ ((1:ℝ)/40) ≤ (Real.log x) ^ ((19:ℝ)/80)) ∧
      (Real.log Ctr + Real.log (Real.log x) + cF * Real.sqrt (Real.log x) + 1 ≤ Real.log x) ∧
      (Real.log 9 + A * Real.log (Real.log x) ≤ (Real.log x) ^ ((19:ℝ)/40)) := by
    have hA1 : ∀ᶠ x : ℝ in atTop, (3:ℝ) ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually_ge_atTop 3
    have hA2 : ∀ᶠ x : ℝ in atTop, (A * Real.log (Real.log x) + 5) ^ 20 ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually (ev_pow_log_add_le_id A hA.le 19)
    have hA3 : ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ≤ (Real.log x) ^ ((1:ℝ)/40) :=
      Real.tendsto_log_atTop.eventually (ev_log_le_rpow (show (0:ℝ) < 1/40 by norm_num))
    have hA4 : ∀ᶠ x : ℝ in atTop, 1000 * (Dbig + 1) ≤ (Real.log x) ^ ((19:ℝ)/80) :=
      Real.tendsto_log_atTop.eventually
        ((tendsto_rpow_atTop (show (0:ℝ) < 19/80 by norm_num)).eventually_ge_atTop (1000 * (Dbig + 1)))
    have hA5 : ∀ᶠ x : ℝ in atTop,
        1000 * (Real.log x) ^ ((1:ℝ)/40) ≤ (Real.log x) ^ ((19:ℝ)/80) := by
      have q1 : ∀ᶠ x : ℝ in atTop, (1000:ℝ) ≤ (Real.log x) ^ ((17:ℝ)/80) :=
        Real.tendsto_log_atTop.eventually
          ((tendsto_rpow_atTop (show (0:ℝ) < 17/80 by norm_num)).eventually_ge_atTop 1000)
      filter_upwards [q1, eventually_ge_atTop (2:ℝ)] with y hq hy1
      have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
      have h2' : 1000 * (Real.log y) ^ ((1:ℝ)/40) ≤
          (Real.log y) ^ ((17:ℝ)/80) * (Real.log y) ^ ((1:ℝ)/40) :=
        mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hlogy.le _)
      have h3' : (Real.log y) ^ ((17:ℝ)/80) * (Real.log y) ^ ((1:ℝ)/40) =
          (Real.log y) ^ ((19:ℝ)/80) := by
        rw [← Real.rpow_add hlogy, show (17:ℝ)/80 + 1/40 = 19/80 by norm_num]
      rw [h3'] at h2'
      exact h2'
    have hA6 : ∀ᶠ x : ℝ in atTop,
        Real.log Ctr + Real.log (Real.log x) + cF * Real.sqrt (Real.log x) + 1 ≤ Real.log x := by
      have e1 : ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ≤ (Real.log x) ^ ((1:ℝ)/4) :=
        Real.tendsto_log_atTop.eventually (ev_log_le_rpow (show (0:ℝ) < 1/4 by norm_num))
      have e2 : ∀ᶠ x : ℝ in atTop, Real.log Ctr ≤ (Real.log x) ^ ((1:ℝ)/4) :=
        Real.tendsto_log_atTop.eventually (ev_const_le_rpow (show (0:ℝ) < 1/4 by norm_num) (Real.log Ctr))
      have e3 : ∀ᶠ x : ℝ in atTop,
          2 * (Real.log x)^((1:ℝ)/4) + (Real.log x)^((1:ℝ)/2) + 1 ≤ Real.log x := by
        have q1 : ∀ᶠ x : ℝ in atTop, (8:ℝ) ≤ (Real.log x) ^ ((3:ℝ)/4) :=
          Real.tendsto_log_atTop.eventually
            ((tendsto_rpow_atTop (show (0:ℝ) < 3/4 by norm_num)).eventually_ge_atTop 8)
        have q2 : ∀ᶠ x : ℝ in atTop, (4:ℝ) ≤ (Real.log x) ^ ((1:ℝ)/2) :=
          Real.tendsto_log_atTop.eventually
            ((tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).eventually_ge_atTop 4)
        have q3 : ∀ᶠ x : ℝ in atTop, (8:ℝ) ≤ Real.log x :=
          Real.tendsto_log_atTop.eventually_ge_atTop 8
        filter_upwards [q1, q2, q3] with y hq1 hq2 hq3
        have hlogy : 0 < Real.log y := by linarith
        have r1 : (Real.log y) ^ ((1:ℝ)/4) * 8 ≤ Real.log y := by
          have hy14 : (0:ℝ) ≤ (Real.log y) ^ ((1:ℝ)/4) := Real.rpow_nonneg hlogy.le _
          calc (Real.log y)^((1:ℝ)/4) * 8 ≤ (Real.log y)^((1:ℝ)/4) * (Real.log y)^((3:ℝ)/4) :=
                mul_le_mul_of_nonneg_left hq1 hy14
            _ = (Real.log y)^((1:ℝ)/4 + 3/4) := by rw [← Real.rpow_add hlogy]
            _ = Real.log y := by rw [show (1:ℝ)/4 + 3/4 = 1 by norm_num, Real.rpow_one]
        have r2 : (Real.log y) ^ ((1:ℝ)/4) ≤ Real.log y / 8 := by
          rw [le_div_iff₀ (by norm_num)]; linarith [r1]
        have r3 : (Real.log y) ^ ((1:ℝ)/2) ≤ Real.log y / 4 := by
          have h3 : (Real.log y) ^ ((1:ℝ)/2) * 4 ≤ Real.log y := by
            have hy12 : (0:ℝ) ≤ (Real.log y) ^ ((1:ℝ)/2) := Real.rpow_nonneg hlogy.le _
            calc (Real.log y)^((1:ℝ)/2) * 4 ≤ (Real.log y)^((1:ℝ)/2) * (Real.log y)^((1:ℝ)/2) :=
                  mul_le_mul_of_nonneg_left hq2 hy12
              _ = (Real.log y)^((1:ℝ)/2 + 1/2) := by rw [← Real.rpow_add hlogy]
              _ = Real.log y := by rw [show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
          rw [le_div_iff₀ (by norm_num)]; linarith [h3]
        have r4 : (1:ℝ) ≤ Real.log y / 8 := by rw [le_div_iff₀ (by norm_num)]; linarith [hq3]
        nlinarith [r2, r3, r4]
      have e4 : ∀ᶠ x : ℝ in atTop, cF * Real.sqrt (Real.log x) ≤ (Real.log x) ^ ((1:ℝ)/2) := by
        filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
        have h1 : cF * Real.sqrt (Real.log x) ≤ (1/4) * Real.sqrt (Real.log x) :=
          mul_le_mul_of_nonneg_right hcFle (Real.sqrt_nonneg _)
        have h2 : Real.sqrt (Real.log x) = (Real.log x) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
        have h3 : (0:ℝ) ≤ (Real.log x) ^ ((1:ℝ)/2) := Real.rpow_nonneg (Real.log_nonneg hx) _
        linarith [h1, h2, h3]
      filter_upwards [e1, e2, e3, e4] with x he1 he2 he3 he4
      linarith
    have hA7 : ∀ᶠ x : ℝ in atTop,
        Real.log 9 + A * Real.log (Real.log x) ≤ (Real.log x) ^ ((19:ℝ)/40) := by
      have e1 : ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ≤ (Real.log x) ^ ((1:ℝ)/40) :=
        Real.tendsto_log_atTop.eventually (ev_log_le_rpow (show (0:ℝ) < 1/40 by norm_num))
      have e2 : ∀ᶠ x : ℝ in atTop, Real.log 9 ≤ (Real.log x) ^ ((19:ℝ)/40) / 2 := by
        have h := Real.tendsto_log_atTop.eventually
          ((tendsto_rpow_atTop (show (0:ℝ) < 19/40 by norm_num)).eventually_ge_atTop (2 * Real.log 9))
        filter_upwards [h] with x hx
        rw [le_div_iff₀ (by norm_num)]; linarith [hx]
      have e3 : ∀ᶠ x : ℝ in atTop,
          A * (Real.log x) ^ ((1:ℝ)/40) ≤ (Real.log x) ^ ((19:ℝ)/40) / 2 := by
        have h := Real.tendsto_log_atTop.eventually
          ((tendsto_rpow_atTop (show (0:ℝ) < 9/20 by norm_num)).eventually_ge_atTop (2 * A))
        filter_upwards [h, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hx1
        have hlogpos : (0:ℝ) < Real.log x := by linarith
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        have h2 : (2*A) * (Real.log x)^((1:ℝ)/40) ≤
            (Real.log x)^((9:ℝ)/20) * (Real.log x)^((1:ℝ)/40) :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hlogpos.le _)
        have h3 : (Real.log x)^((9:ℝ)/20) * (Real.log x)^((1:ℝ)/40) = (Real.log x)^((19:ℝ)/40) := by
          rw [← Real.rpow_add hlogpos, show (9:ℝ)/20 + 1/40 = 19/40 by norm_num]
        calc A * (Real.log x)^((1:ℝ)/40) * 2 = (2*A) * (Real.log x)^((1:ℝ)/40) := by ring
          _ ≤ (Real.log x)^((19:ℝ)/40) := le_trans h2 (le_of_eq h3)
      filter_upwards [e1, e2, e3] with x h1 h2 h3
      have h4 : A * Real.log (Real.log x) ≤ A * (Real.log x)^((1:ℝ)/40) :=
        mul_le_mul_of_nonneg_left h1 hA.le
      linarith [h2, h3, h4]
    filter_upwards [hA1, hA2, hA3, hA4, hA5, hA6, hA7] with x w1 w2 w3 w4 w5 w6 w7
    exact ⟨w1, w2, w3, w4, w5, w6, w7⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hfin
  refine ⟨cF, 4, hcFpos, by norm_num, max x₀ 3, ?_⟩
  intro x hx N _inst χ hχ hprim hN
  have hx3 : (3:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  obtain ⟨hC1, hC2, hC3, hC4, hC6, hC5, hC7⟩ := hx₀ x hxx₀
  have hxpos : (0:ℝ) < x := by linarith
  set Lx : ℝ := Real.log x with hLxdef
  have hLx1 : 1 ≤ Lx := by rw [hLxdef]; linarith
  have hLxpos : 0 < Lx := by linarith
  set b : ℝ := A * Real.log Lx + 5 with hbdef
  have hb1 : 1 ≤ b := by rw [hbdef]; nlinarith [hA.le, Real.log_nonneg hLx1]
  have hbpos : 0 < b := by linarith
  have hb20 : b ^ 20 ≤ Lx := by
    have h2 : (A * Real.log Lx + 5) ^ 20 ≤ Lx := by simpa only [← hLxdef] using hC2
    rw [hbdef]; exact h2
  have hble : b ≤ Lx ^ ((1:ℝ)/20) := by
    have h6 : (Lx ^ ((1:ℝ)/20)) ^ 20 = Lx := by
      rw [← Real.rpow_natCast (Lx ^ ((1:ℝ)/20)) 20, ← Real.rpow_mul (le_of_lt hLxpos)]
      rw [show (1:ℝ)/20 * ((20:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
    rw [← pow_le_pow_iff_left₀ (by positivity : (0:ℝ) ≤ b)
      (Real.rpow_nonneg (le_of_lt hLxpos) _) (by norm_num : (20:ℕ) ≠ 0), h6]
    exact hb20
  set ℓ : ℝ := Real.log ((N:ℝ) + 2) with hℓdef
  have hN2 : 2 ≤ N := two_le_of_ne_one χ hχ
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact Real.log_pos (by linarith)
  have hlog3leℓ : Real.log 3 ≤ ℓ := by
    rw [hℓdef]; apply Real.log_le_log (by norm_num); linarith
  have hℓb : ℓ ≤ b := by
    rw [hℓdef, hbdef]
    have h1 : (N:ℝ) + 2 ≤ Lx ^ A + 2 := by linarith [hN]
    have h2' : Real.log ((N:ℝ) + 2) ≤ Real.log (Lx ^ A + 2) := Real.log_le_log (by positivity) h1
    have h3' : Real.log (Lx ^ A + 2) ≤ A * Real.log Lx + 2 := by
      have hLxA : (0:ℝ) < Lx ^ A := Real.rpow_pos_of_pos hLxpos A
      have hone : (1:ℝ) ≤ Lx ^ A := Real.one_le_rpow hLx1 hA.le
      have h4' : Lx ^ A + 2 ≤ 3 * Lx ^ A := by nlinarith [hone]
      calc Real.log (Lx ^ A + 2) ≤ Real.log (3 * Lx ^ A) := Real.log_le_log (by positivity) h4'
        _ = Real.log 3 + A * Real.log Lx := by
              rw [Real.log_mul (by norm_num) (ne_of_gt hLxA), Real.log_rpow hLxpos]
        _ ≤ A * Real.log Lx + 2 := by
              have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) ≠ 1)
              linarith
    linarith
  set θ : ℝ := Real.sqrt (Lx / ℓ) with hθdef
  have hθpos : 0 < θ := Real.sqrt_pos.mpr (div_pos hLxpos hℓpos)
  set P : ℝ := Lx ^ ((19:ℝ)/80) with hPdef
  have hPpos : 0 < P := Real.rpow_pos_of_pos hLxpos _
  have hP2 : 2 ≤ P := by
    have h1 : 1000 * (Dbig + 1) ≤ P := hC4
    have h2 : (0:ℝ) ≤ Dbig := hDbig0
    linarith
  have hLx19_40 : Lx ^ ((19:ℝ)/40) = P^2 := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hLxpos)]
    congr 1; norm_num
  have hθlb : P ^ 2 ≤ θ := by
    have heq : P^2 = Real.sqrt (Lx ^ ((19:ℝ)/20)) := by
      rw [← hLx19_40, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hLxpos)]
      congr 1; norm_num
    rw [heq, hθdef]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hℓpos]
    have hℓ20 : ℓ ≤ Lx ^ ((1:ℝ)/20) := le_trans hℓb hble
    calc Lx ^ ((19:ℝ)/20) * ℓ ≤ Lx ^ ((19:ℝ)/20) * Lx ^ ((1:ℝ)/20) :=
          mul_le_mul_of_nonneg_left hℓ20 (Real.rpow_nonneg hLxpos.le _)
      _ = Lx ^ ((19:ℝ)/20 + 1/20) := by rw [← Real.rpow_add hLxpos ((19:ℝ)/20) (1/20)]
      _ = Lx := by rw [show (19:ℝ)/20 + 1/20 = 1 by norm_num, Real.rpow_one]
  have hPDbig : Dbig ≤ P / 1000 := by linarith [hC4]
  have hPlog : Real.log Lx ≤ P / 1000 := by
    have h1 : Real.log Lx ≤ Lx ^ ((1:ℝ)/40) := hC3
    have h2 : 1000 * Lx ^ ((1:ℝ)/40) ≤ P := hC6
    linarith
  have hcFP : (10:ℝ)^5 ≤ cF * P := by
    have h1 : 100 ≤ Dbig * cF := by
      rw [div_le_iff₀ hcFpos] at hDbig_cF; linarith [hDbig_cF]
    have h2 : Dbig * cF ≤ (P / 1000) * cF :=
      mul_le_mul_of_nonneg_right hPDbig hcFpos.le
    rw [show (10:ℝ)^5 = 100 * 1000 by norm_num]
    nlinarith [h1, h2]
  have hC7' : Real.log 9 + A * Real.log Lx ≤ Lx ^ ((19:ℝ)/40) := by
    have h := hC7; rw [hLxdef] at h; exact h
  have hθlog3 : Real.log 3 ≤ θ := by
    have h1 : Real.log 3 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 9 ≤ Real.log 9 + A * Real.log Lx := by
      have : 0 ≤ A * Real.log Lx := mul_nonneg hA.le (Real.log_nonneg hLx1)
      linarith
    linarith [h1, h2, hC7', hLx19_40, hθlb]
  set T : ℝ := Real.exp θ with hTdef
  have hTpos : 0 < T := Real.exp_pos θ
  have hT3 : 3 ≤ T := by
    rw [hTdef]
    calc (3:ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp θ := Real.exp_le_exp.mpr hθlog3
  have hbθ : b ≤ θ := by
    have h2' : Lx ^ ((1:ℝ)/20) ≤ P^2 := by
      rw [← hLx19_40]
      apply Real.rpow_le_rpow_of_exponent_le hLx1
      norm_num
    linarith [hble, h2', hθlb]
  have hlogN_le : Real.log (N:ℝ) ≤ θ := by
    have h6 : Real.log (N:ℝ) ≤ A * Real.log Lx := by
      have h7 : Real.log (Lx ^ A) = A * Real.log Lx := Real.log_rpow hLxpos A
      calc Real.log (N:ℝ) ≤ Real.log (Lx ^ A) :=
            Real.log_le_log hNpos (by rw [hLxdef]; exact hN)
        _ = A * Real.log Lx := h7
    linarith [h6, hbθ, hbdef]
  have hT9N : 9 * (N:ℝ) ≤ T := by
    rw [hTdef]
    have h1' : Real.log (9 * (N:ℝ)) ≤ θ := by
      have h2' : Real.log (9 * (N:ℝ)) = Real.log 9 + Real.log (N:ℝ) :=
        Real.log_mul (by norm_num) (ne_of_gt hNpos)
      have h3' : Real.log (N:ℝ) ≤ A * Real.log Lx := by
        have h4'' : Real.log (Lx ^ A) = A * Real.log Lx := Real.log_rpow hLxpos A
        calc Real.log (N:ℝ) ≤ Real.log (Lx ^ A) :=
              Real.log_le_log hNpos (by rw [hLxdef]; exact hN)
          _ = A * Real.log Lx := h4''
      have h5' : Real.log 9 + A * Real.log Lx ≤ Lx ^ ((19:ℝ)/40) := by
        have := hC7; rw [hLxdef] at this; exact this
      have h6' : Lx ^ ((19:ℝ)/40) = P ^ 2 := hLx19_40
      linarith [h2', h3', h5', h6', hθlb]
    calc 9 * (N:ℝ) = Real.exp (Real.log (9 * (N:ℝ))) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp θ := Real.exp_le_exp.mpr h1'
  have hlogT3 : Real.log (T + 3) ≤ 2 * θ := by
    have h1' : T + 3 ≤ Real.exp θ * Real.exp θ := by
      have h2' : (0:ℝ) < Real.exp θ := Real.exp_pos θ
      have h3' : (3:ℝ) ≤ Real.exp θ := hT3
      have h4' : (1:ℝ) ≤ Real.exp θ := by linarith
      nlinarith
    calc Real.log (T + 3) ≤ Real.log (Real.exp θ * Real.exp θ) :=
          Real.log_le_log (by linarith) h1'
      _ = 2 * θ := by
          rw [Real.log_mul (ne_of_gt (Real.exp_pos θ)) (ne_of_gt (Real.exp_pos θ)), Real.log_exp]
          ring
  set L : ℝ := Real.log ((N:ℝ) * (T + 3)) with hLdef
  have hL3θ : L ≤ 3 * θ := by
    rw [hLdef]
    have h1' : Real.log ((N:ℝ) * (T + 3)) = Real.log (N:ℝ) + Real.log (T + 3) :=
      Real.log_mul (ne_of_gt hNpos) (by linarith)
    linarith [h1', hlogN_le, hlogT3]
  have hL1 : 1 ≤ L := by
    rw [hLdef]; apply log_ge_one_of_three_le; nlinarith [hN2, hT3]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLgeθ : θ ≤ L := by
    rw [hLdef]
    have h1' : Real.log ((N:ℝ) * (T + 3)) = Real.log (N:ℝ) + Real.log (T + 3) :=
      Real.log_mul (ne_of_gt hNpos) (by linarith)
    have h2' : θ ≤ Real.log (T + 3) := by
      rw [hTdef]
      calc θ = Real.log (Real.exp θ) := (Real.log_exp θ).symm
        _ ≤ Real.log (Real.exp θ + 3) :=
            Real.log_le_log (Real.exp_pos θ) (by linarith)
    have h3' : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
    linarith [h1', h2', h3']
  have hLx_le_θ3 : Lx ≤ θ ^ 3 := by
    have h1' : Lx / b ≤ θ ^ 2 := by
      rw [hθdef, Real.sq_sqrt (div_nonneg hLxpos.le hℓpos.le)]
      exact div_le_div_of_nonneg_left hLxpos.le hℓpos hℓb
    have h2' : Lx / b * b = Lx := by field_simp
    nlinarith [h1', hbθ, hbpos]
  have hLx_le_L3 : Lx ≤ L ^ 3 := le_trans hLx_le_θ3 (pow_le_pow_left₀ (le_of_lt hθpos) hLgeθ 3)
  have hN2ε : (N:ℝ) ^ (2 * (1/(2*A))) ≤ L ^ 3 := by
    have hε' : 2 * (1 / (2 * A)) = 1 / A := by field_simp
    rw [hε']
    have h1' : (N:ℝ) ^ (1/A) ≤ Lx := by
      have hh : (N:ℝ) ^ (1/A) ≤ (Lx^A) ^ (1/A) :=
        Real.rpow_le_rpow (le_of_lt hNpos) (by rw [hLxdef]; exact hN) (by positivity : (0:ℝ) ≤ 1/A)
      have h2' : (Lx ^ A) ^ (1/A) = Lx := by
        rw [← Real.rpow_mul (le_of_lt hLxpos), show A * (1/A) = 1 by field_simp, Real.rpow_one]
      rwa [h2'] at hh
    linarith [h1', hLx_le_L3]
  set δ : ℝ := min (boxC cOff cReal / L) (Cs * (N:ℝ) ^ (-(1/(2*A))) / 4) with hδdef
  have hδpos : 0 < δ := lt_min (div_pos hcBpos hLpos) (by positivity)
  have hδc : δ ≤ boxC cOff cReal / L := min_le_left _ _
  have hδS : δ ≤ Cs * (N:ℝ)^(-(1/(2*A)))/4 := min_le_right _ _
  have hδlo : 1 / δ ^ 2 ≤ D * L ^ 3 := by
    rcases le_total (boxC cOff cReal / L) (Cs * (N:ℝ)^(-(1/(2*A)))/4) with hh | hh
    · have hδeq : δ = boxC cOff cReal / L := by rw [hδdef]; exact min_eq_left hh
      rw [hδeq]
      have h1' : 1 / (boxC cOff cReal / L) ^ 2 = (L / boxC cOff cReal) ^ 2 := by field_simp
      rw [h1']
      have h3' : (L / boxC cOff cReal) ^ 2 ≤ L ^ 3 * (1/(boxC cOff cReal)^2) := by
        rw [div_pow, show L ^ 3 * (1 / (boxC cOff cReal) ^ 2) = L^3 / (boxC cOff cReal)^2 by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [hL1]
      have h4' : 1 / (boxC cOff cReal) ^ 2 ≤ D := by
        rw [hDdef]; linarith [le_max_left (1 / (boxC cOff cReal) ^ 2) (16/Cs^2)]
      calc (L / boxC cOff cReal) ^ 2 ≤ L ^ 3 * (1/(boxC cOff cReal)^2) := h3'
        _ ≤ L ^ 3 * D := mul_le_mul_of_nonneg_left h4' (by positivity)
        _ = D * L ^ 3 := by ring
    · have hδeq : δ = Cs * (N:ℝ)^(-(1/(2*A)))/4 := by rw [hδdef]; exact min_eq_right hh
      rw [hδeq]
      have hNneg : (N:ℝ)^(-(1/(2*A))) = ((N:ℝ)^(1/(2*A)))⁻¹ := Real.rpow_neg hNpos.le _
      rw [hNneg]
      have h1' : 1 / (Cs * ((N:ℝ)^(1/(2*A)))⁻¹ / 4)^2 = 16 * ((N:ℝ)^(1/(2*A)))^2 / Cs^2 := by
        field_simp; ring
      rw [h1']
      have h2' : ((N:ℝ)^(1/(2*A)))^2 = (N:ℝ)^(1/A) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le,
          show (1:ℝ)/(2*A) * ((2:ℕ):ℝ) = 1/A by push_cast; field_simp]
      rw [h2']
      have h3' : (N:ℝ)^(1/A) ≤ L^3 := by
        have hε'' : 2 * (1/(2*A)) = 1/A := by field_simp
        have := hN2ε; rwa [hε''] at this
      have h4' : 16 / Cs^2 ≤ D := by
        rw [hDdef]; linarith [le_max_right (1/(boxC cOff cReal)^2) (16/Cs^2)]
      calc 16 * (N:ℝ)^(1/A) / Cs^2 = (16/Cs^2) * (N:ℝ)^(1/A) := by ring
        _ ≤ D * L^3 := by
            calc (16/Cs^2) * (N:ℝ)^(1/A) ≤ D * (N:ℝ)^(1/A) :=
                  mul_le_mul_of_nonneg_right h4' (Real.rpow_nonneg hNpos.le _)
              _ ≤ D * L^3 := mul_le_mul_of_nonneg_left h3' (le_of_lt hDpos)
  have hδLx : c₁ * θ ≤ δ * Lx := by
    rcases le_total (boxC cOff cReal / L) (Cs * (N:ℝ)^(-(1/(2*A)))/4) with hh | hh
    · have hδeq : δ = boxC cOff cReal / L := by rw [hδdef]; exact min_eq_left hh
      rw [hδeq]
      have hθsq : θ ^ 2 = Lx / ℓ := by rw [hθdef, Real.sq_sqrt (div_nonneg hLxpos.le hℓpos.le)]
      have hdiv : Lx / θ = θ * ℓ := by
        rw [div_eq_iff (ne_of_gt hθpos)]
        have hh : (θ * ℓ) * θ = θ^2 * ℓ := by ring
        rw [hh, hθsq]
        field_simp
      have hB : Lx / (3*θ) ≤ Lx / L := div_le_div_of_nonneg_left hLxpos.le hLpos hL3θ
      have hkey : (boxC cOff cReal / 3) * (ℓ * θ) = boxC cOff cReal * (Lx / (3*θ)) := by
        rw [mul_comm ℓ θ, ← hdiv]; ring
      calc c₁ * θ ≤ ((boxC cOff cReal / 3) * Real.log 3) * θ :=
            mul_le_mul_of_nonneg_right hc1leI (le_of_lt hθpos)
        _ = (boxC cOff cReal / 3) * (Real.log 3 * θ) := by ring
        _ ≤ (boxC cOff cReal / 3) * (ℓ * θ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hlog3leℓ (le_of_lt hθpos)
        _ = boxC cOff cReal * (Lx / (3*θ)) := hkey
        _ ≤ boxC cOff cReal * (Lx / L) := mul_le_mul_of_nonneg_left hB (le_of_lt hcBpos)
        _ = boxC cOff cReal / L * Lx := by ring
    · have hδeq : δ = Cs * (N:ℝ)^(-(1/(2*A)))/4 := by rw [hδdef]; exact min_eq_right hh
      rw [hδeq]
      have hNle : (N:ℝ)^(1/(2*A)) ≤ Lx^((1:ℝ)/2) := by
        have h : (N:ℝ)^(1/(2*A)) ≤ (Lx^A) ^ (1/(2*A)) :=
          Real.rpow_le_rpow (le_of_lt hNpos) (by rw [hLxdef]; exact hN)
            (by positivity : (0:ℝ) ≤ 1/(2*A))
        have h2' : (Lx^A)^(1/(2*A)) = Lx^((1:ℝ)/2) := by
          rw [← Real.rpow_mul (le_of_lt hLxpos)]; congr 1; field_simp
        rwa [h2'] at h
      have hNinv : Lx ^ (-(1:ℝ)/2) ≤ (N:ℝ)^(-(1/(2*A))) := by
        have h1 : Lx ^ (-(1:ℝ)/2) = (Lx ^ ((1:ℝ)/2))⁻¹ := by
          rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by norm_num, Real.rpow_neg hLxpos.le]
        have h2 : (N:ℝ) ^ (-(1/(2*A))) = ((N:ℝ) ^ (1/(2*A)))⁻¹ := by
          rw [show (-(1/(2*A))) = -(1/(2*A)) by ring, Real.rpow_neg hNpos.le]
        rw [h1, h2]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hLxpos _) (Real.rpow_pos_of_pos hNpos _)).mpr hNle
      have hsqrt : Lx ^ ((1:ℝ)/2) = θ * Real.sqrt ℓ := by
        rw [show Lx ^ ((1:ℝ)/2) = Real.sqrt Lx by rw [Real.sqrt_eq_rpow], hθdef]
        rw [← Real.sqrt_mul (div_nonneg hLxpos.le hℓpos.le)]
        congr 1; field_simp
      have h1' : Lx * Lx ^ (-(1:ℝ)/2) = Lx^((1:ℝ)/2) := by
        have h1 : Lx ^ (-(1:ℝ)/2) = (Lx ^ ((1:ℝ)/2))⁻¹ := by
          rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by norm_num, Real.rpow_neg hLxpos.le]
        rw [h1, ← div_eq_mul_inv, div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hLxpos _)),
          ← Real.rpow_add hLxpos ((1:ℝ)/2) ((1:ℝ)/2),
          show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
      have h6' : Real.sqrt (Real.log 3) ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hlog3leℓ
      calc c₁ * θ ≤ (Cs * Real.sqrt (Real.log 3) / 4) * θ :=
            mul_le_mul_of_nonneg_right hc1leII (le_of_lt hθpos)
        _ = (Cs/4) * (θ * Real.sqrt (Real.log 3)) := by ring
        _ ≤ (Cs/4) * (θ * Real.sqrt ℓ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left h6' (le_of_lt hθpos)
        _ = (Cs/4) * Lx^((1:ℝ)/2) := by rw [← hsqrt]
        _ = (Cs/4) * (Lx * Lx^(-(1:ℝ)/2)) := by rw [h1']
        _ ≤ (Cs/4) * (Lx * (N:ℝ)^(-(1/(2*A)))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hNinv hLxpos.le
        _ = Cs * (N:ℝ)^(-(1/(2*A)))/4 * Lx := by ring
  -- ===== the two exponential absorptions =====
  have hAbs1 : Real.log Ctr + 2 * Real.log Lx + 2 ≤ (1 - cF) * θ := by
    have h2' : Real.log Lx ≤ P / 1000 := hPlog
    have h3' : (1 - cF) * P^2 ≤ (1 - cF) * θ := mul_le_mul_of_nonneg_left hθlb (le_of_lt h1cFpos)
    have h4 : Real.log Ctr + 2 * Real.log Lx + 2 ≤ P / 1000 + 2 * (P / 1000) + 2 := by linarith
    have h5 : P / 1000 + 2 * (P / 1000) + 2 ≤ (1 - cF) * P^2 := by nlinarith [hP2, hcFle]
    linarith [h4, h5, h3']
  have hAbs2 : Real.log (CP + 1) + 5 * Real.log (3 * Lx) + 2 ≤ cF * θ := by
    have hlog3Lx : Real.log (3 * Lx) = Real.log 3 + Real.log Lx :=
      Real.log_mul (by norm_num) (ne_of_gt hLxpos)
    have h2' : Real.log Lx ≤ P / 1000 := hPlog
    have h3' : cF * P^2 ≤ cF * θ := mul_le_mul_of_nonneg_left hθlb (le_of_lt hcFpos)
    have hlogCP : Real.log (CP + 1) ≤ Dbig := hDbig_CP
    have h6 : Real.log (CP + 1) + 5 * Real.log (3 * Lx) + 2 ≤
        6 * (P/1000) + 5 * (P/1000) + 2 := by
      rw [hlog3Lx]
      linarith [hlogCP, hlog3Dbig, h2', hPDbig]
    have h7 : 6 * (P/1000) + 5 * (P/1000) + 2 ≤ cF * θ := by
      have h11 : 6 * (P/1000) + 5 * (P/1000) + 2 = 11 * P / 1000 + 2 := by ring
      rw [h11]
      have h12 : (10:ℝ)^5 * P ≤ cF * P^2 := by
        have h := hcFP; nlinarith [h, hPpos]
      have h13 : 11 * P / 1000 + 2 ≤ (10:ℝ)^5 * P := by nlinarith only [hP2]
      linarith [h3', h12, h13]
    linarith [h6, h7]
  have hAbs3 : Real.log (CP * Real.exp 1 + 1) + 5 * Real.log (3 * Lx) + 2 ≤ (1 - cF) * θ := by
    have hlog3Lx : Real.log (3 * Lx) = Real.log 3 + Real.log Lx :=
      Real.log_mul (by norm_num) (ne_of_gt hLxpos)
    have h2' : Real.log Lx ≤ P / 1000 := hPlog
    have h3' : (1 - cF) * P^2 ≤ (1 - cF) * θ := mul_le_mul_of_nonneg_left hθlb (le_of_lt h1cFpos)
    have hlogCP : Real.log (CP * Real.exp 1 + 1) ≤ Dbig := hDbig_CPe
    have h6 : Real.log (CP * Real.exp 1 + 1) + 5 * Real.log (3 * Lx) + 2 ≤
        6 * (P/1000) + 5 * (P/1000) + 2 := by
      rw [hlog3Lx]
      linarith [hlogCP, hlog3Dbig, h2', hPDbig]
    have h7 : 6 * (P/1000) + 5 * (P/1000) + 2 ≤ (1 - cF) * θ := by
      have h11 : 6 * (P/1000) + 5 * (P/1000) + 2 = 11 * P / 1000 + 2 := by ring
      rw [h11]
      have h12 : (3:ℝ)/4 * P^2 ≤ (1 - cF) * P^2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); linarith [hcFle]
      have h13 : 11 * P / 1000 + 2 ≤ (3:ℝ)/4 * P^2 := by nlinarith only [hP2]
      linarith [h3', h12, h13]
    linarith [h6, h7]
  -- ===== decompose =====
  have hψ : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) *
        (ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ Ctr * (x * Lx ^ 2 / T + Lx) + CP * (L ^ 5 * x ^ (1 - δ) + L ^ 5 * x ^ (1 + 1/Lx) / T) := by
    have htr := htrunc N χ hχ x T (by linarith) (by linarith)
    have hper := hPerron N χ hχ hprim x T δ hx3 hT3 hδpos hδc hδS hL1 hδlo
    have h1' : Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) = Ctr * (x * Lx ^ 2 / T + Lx) := by
      rw [hLxdef]
    have h2' : CP * (L ^ 5 * x ^ (1 - δ) + L ^ 5 * x ^ (1 + 1 / Real.log x) / T)
        = CP * (L ^ 5 * x ^ (1 - δ) + L ^ 5 * x ^ (1 + 1/Lx) / T) := by
      rw [hLxdef]
    rw [h1'] at htr
    rw [h2'] at hper
    calc ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
        = ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)
            - chiPerron χ x T) + chiPerron χ x T‖ := by ring_nf
      _ ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)
            - chiPerron χ x T)‖ + ‖chiPerron χ x T‖ := norm_add_le _ _
      _ ≤ _ := add_le_add htr hper
  -- ===== term bounds =====
  have hθle_sqrt : θ ≤ Real.sqrt Lx := by
    rw [hθdef]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hℓpos]
    have hlog3ge1 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact Real.exp_one_lt_three.le
    nlinarith [hLxpos, hlog3ge1, hlog3leℓ]
  have hθleLx : θ ≤ Lx := by
    have h1 : θ ≤ Real.sqrt Lx := hθle_sqrt
    have h2 : Real.sqrt Lx ≤ Lx := by
      rw [Real.sqrt_le_iff]; exact ⟨hLxpos.le, by nlinarith [hLx1]⟩
    linarith
  have hP5 : CP * (3*θ)^5 ≤ Real.exp (cF * θ) := by
    rw [← Real.log_le_iff_le_exp (by positivity)]
    have h3' : Real.log (CP * (3*θ)^5) = Real.log CP + 5 * Real.log (3*θ) := by
      rw [Real.log_mul (ne_of_gt hCPpos) (by positivity), Real.log_pow]; norm_num
    rw [h3']
    have h4' : Real.log (3*θ) ≤ Real.log (3*Lx) :=
      Real.log_le_log (by linarith) (by linarith [hθleLx])
    have h5' : Real.log CP ≤ Real.log (CP + 1) := Real.log_le_log (by linarith) (by linarith)
    linarith [hAbs2, h4', h5']
  have hP5e : CP * Real.exp 1 * (3*θ)^5 ≤ Real.exp ((1-cF) * θ) := by
    rw [← Real.log_le_iff_le_exp (by positivity)]
    have h3' : Real.log (CP * Real.exp 1 * (3*θ)^5) = Real.log CP + 1 + 5 * Real.log (3*θ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (ne_of_gt hCPpos) (Real.exp_ne_zero 1), Real.log_exp, Real.log_pow]
      norm_num
    rw [h3']
    have h4' : Real.log (3*θ) ≤ Real.log (3*Lx) :=
      Real.log_le_log (by linarith) (by linarith [hθleLx])
    have h5' : Real.log CP ≤ Real.log (CP * Real.exp 1 + 1) :=
      Real.log_le_log (by linarith) (by nlinarith [Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)])
    linarith [hAbs3, h4', h5']
  have hT1 : Ctr * (x * Lx ^ 2 / T + Lx) ≤ 2 * (x * Real.exp (-(cF * θ))) := by
    have hA : Ctr * (x * Lx^2 / T) ≤ x * Real.exp (-(cF*θ)) := by
      have h1' : x * Lx^2 / T = x * (Lx^2 * Real.exp (-(θ))) := by
        rw [hTdef, div_eq_mul_inv, ← Real.exp_neg]; ring
      rw [h1']
      have h2' : Ctr * Lx^2 ≤ Real.exp ((1-cF)*θ) := by
        rw [← Real.log_le_iff_le_exp (by positivity)]
        have h3' : Real.log (Ctr * Lx^2) = Real.log Ctr + 2 * Real.log Lx := by
          rw [Real.log_mul (ne_of_gt hCtrpos) (by positivity), Real.log_pow]; norm_num
        rw [h3']; linarith [hAbs1]
      calc Ctr * (x * (Lx^2 * Real.exp (-(θ))))
          = (Ctr * Lx^2) * (x * Real.exp (-(θ))) := by ring
        _ ≤ Real.exp ((1-cF)*θ) * (x * Real.exp (-(θ))) :=
            mul_le_mul_of_nonneg_right h2' (by positivity)
        _ = x * Real.exp (-(cF*θ)) := by
              have hexp : Real.exp ((1-cF)*θ) * Real.exp (-(θ)) = Real.exp (-(cF*θ)) := by
                rw [← Real.exp_add]; congr 1; ring
              rw [show Real.exp ((1-cF)*θ) * (x * Real.exp (-(θ))) =
                x * (Real.exp ((1-cF)*θ) * Real.exp (-(θ))) by ring, hexp]
    have hB : Ctr * Lx ≤ x * Real.exp (-(cF*θ)) := by
      have h2' : Real.log (Ctr * Lx) = Real.log Ctr + Real.log Lx :=
        Real.log_mul (ne_of_gt hCtrpos) (ne_of_gt hLxpos)
      have h3' : Real.log (x * Real.exp (-(cF*θ))) = Lx + -(cF*θ) := by
        rw [Real.log_mul hxpos.ne' (Real.exp_ne_zero _), Real.log_exp, ← hLxdef]
      have h6 : Real.log (Ctr * Lx) ≤ Real.log (x * Real.exp (-(cF*θ))) := by
        rw [h2', h3']
        have h4' : cF * θ ≤ cF * Real.sqrt Lx := mul_le_mul_of_nonneg_left hθle_sqrt hcFpos.le
        linarith [hC5, h4']
      exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h6
    linarith [hA, hB]
  have hT2 : CP * (L ^ 5 * x ^ (1 - δ) + L ^ 5 * x ^ (1 + 1/Lx) / T)
      ≤ 2 * (x * Real.exp (-(cF * θ))) := by
    have hL5 : L ^ 5 ≤ (3 * θ) ^ 5 := pow_le_pow_left₀ (le_of_lt hLpos) hL3θ 5
    have hA : CP * (L ^ 5 * x ^ (1 - δ)) ≤ x * Real.exp (-(cF*θ)) := by
      have hxpow : x ^ (1 - δ) = x * Real.exp (-(δ * Lx)) := by
        rw [Real.rpow_def_of_pos hxpos, ← hLxdef]
        rw [show Real.log x * (1 - δ) = Real.log x + (-(δ * Real.log x)) by ring]
        rw [Real.exp_add, Real.exp_log hxpos]
      rw [hxpow]
      have hexp : Real.exp (-(δ * Lx)) ≤ Real.exp (-(c₁ * θ)) :=
        Real.exp_le_exp.mpr (by linarith [hδLx])
      calc CP * (L ^ 5 * (x * Real.exp (-(δ*Lx))))
          = (CP * L^5) * (x * Real.exp (-(δ*Lx))) := by ring
        _ ≤ (CP * (3*θ)^5) * (x * Real.exp (-(c₁*θ))) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hL5 (le_of_lt hCPpos)
              · exact mul_le_mul_of_nonneg_left hexp hxpos.le
              · exact mul_nonneg hxpos.le (Real.exp_nonneg _)
              · positivity
        _ ≤ Real.exp (cF*θ) * (x * Real.exp (-(c₁*θ))) :=
              mul_le_mul_of_nonneg_right hP5 (by positivity)
        _ = x * Real.exp (-(cF*θ)) := by
              have hexp : Real.exp (cF*θ) * Real.exp (-(c₁*θ)) = Real.exp (-(cF*θ)) := by
                rw [← Real.exp_add]; congr 1; ring
              rw [show Real.exp (cF*θ) * (x * Real.exp (-(c₁*θ))) =
                x * (Real.exp (cF*θ) * Real.exp (-(c₁*θ))) by ring, hexp]
    have hB : CP * (L ^ 5 * x ^ (1 + 1/Lx) / T) ≤ x * Real.exp (-(cF*θ)) := by
      have hxpow : x ^ (1 + 1/Lx) = Real.exp 1 * x := by
        rw [Real.rpow_add hxpos, Real.rpow_one, Real.rpow_def_of_pos hxpos]
        rw [show Real.log x * (1/Lx) = 1 by rw [← hLxdef]; field_simp]
        ring
      rw [hxpow, hTdef, div_eq_mul_inv, ← Real.exp_neg]
      calc CP * (L ^ 5 * (Real.exp 1 * x) * Real.exp (-(θ)))
          = (CP * Real.exp 1 * L^5) * (x * Real.exp (-(θ))) := by ring
        _ ≤ (CP * Real.exp 1 * (3*θ)^5) * (x * Real.exp (-(θ))) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hL5 (by positivity)
        _ ≤ Real.exp ((1-cF)*θ) * (x * Real.exp (-(θ))) :=
              mul_le_mul_of_nonneg_right hP5e (by positivity)
        _ = x * Real.exp (-(cF*θ)) := by
              have hexp : Real.exp ((1-cF)*θ) * Real.exp (-(θ)) = Real.exp (-(cF*θ)) := by
                rw [← Real.exp_add]; congr 1; ring
              rw [show Real.exp ((1-cF)*θ) * (x * Real.exp (-(θ))) =
                x * (Real.exp ((1-cF)*θ) * Real.exp (-(θ))) by ring, hexp]
    linarith [hA, hB]
  -- ===== conclude =====
  have hθeq : θ = Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)) := by
    rw [hθdef, hLxdef, hℓdef]
  calc ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ 2 * (x * Real.exp (-(cF * θ))) + 2 * (x * Real.exp (-(cF * θ))) := by
        have h1 := hψ
        have h2 := hT1
        have h3 := hT2
        have h4 : CP * (L ^ 5 * x ^ (1 - δ) + L ^ 5 * x ^ (1 + 1/Lx) / T)
            ≤ 2 * (x * Real.exp (-(cF * θ))) := hT2
        linarith [hψ, hT1, hT2]
    _ = 4 * x * Real.exp (-(cF * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) := by
        rw [← hθeq]; ring



end
end Commons.NumberTheory.DirichletCharacter
