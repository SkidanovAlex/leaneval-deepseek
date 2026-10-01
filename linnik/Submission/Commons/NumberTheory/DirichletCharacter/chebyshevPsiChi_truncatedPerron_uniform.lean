import Mathlib
import Submission.Commons.Analysis.Fourier.perronStep_deviation
import Submission.Commons.NumberTheory.Zeta.perronOne_bound
import Submission.Commons.NumberTheory.Zeta.mangoldtPerronError_bound
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_mul_rpow
import Submission.Commons.NumberTheory.DirichletCharacter.perronSeries_sum_eq

noncomputable section

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.DirichletCharacter

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

/-! ## The main theorem -/

/-- **Uniform truncated Perron formula for `χ · Λ`.** There is a single absolute constant
`C`, valid simultaneously for *all* moduli `N`, all Dirichlet characters `χ` mod `N`, all
`x ≥ 3` and all `T ≥ 2`, such that
`‖Σ_{n ≤ x} χ(n)Λ(n) - (1/2π) ∫_{-T}^{T} L(s, χΛ) x^s / s dt‖ ≤ C (x log²x / T + log x)`,
where the integral is taken on the vertical line `s = 1 + 1/log x + i t`. -/
theorem chebyshevPsiChi_truncatedPerron_uniform :
    ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ), 3 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          - (1 / (2 * Real.pi)) *
            (∫ (t : ℝ) in -T..T,
              LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                  (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
                (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  rcases Commons.NumberTheory.Zeta.mangoldtPerronError_bound with ⟨CA, hCApos, hCA⟩
  refine ⟨(32 / (2 * Real.pi)) * CA + 2, by positivity, ?_⟩
  intro N _ χ x hx T hT
  have hm := chiPsi_sub_perron_main χ hx hT
  have hA : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
      CA * (x * (Real.log x) ^ 2 / T + Real.log x) := (hCA x hx T hT).2
  have hlogB : 2 * Real.log x ≤ 2 * (x * (Real.log x) ^ 2 / T + Real.log x) := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
    nlinarith
  have hBpos : 0 ≤ x * (Real.log x) ^ 2 / T + Real.log x := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
    linarith
  calc
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        - (1 / (2 * Real.pi)) *
          (∫ (t : ℝ) in -T..T,
            LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖
        ≤ (32 / (2 * Real.pi)) *
          (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
            min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) + 2 * Real.log x := by
          change ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chiLambda χ n) - perronInt χ x T‖ ≤
            (32 / (2 * Real.pi)) *
              (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
                ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
                min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) + 2 * Real.log x
          exact hm
    _ ≤ (32 / (2 * Real.pi)) * (CA * (x * (Real.log x) ^ 2 / T + Real.log x)) +
          2 * Real.log x := by
          have hc : 0 ≤ (32 / (2 * Real.pi)) := by positivity
          nlinarith [hA]
    _ ≤ ((32 / (2 * Real.pi)) * CA + 2) * (x * (Real.log x) ^ 2 / T + Real.log x) := by
          nlinarith [hlogB, hBpos]

end Commons.NumberTheory.DirichletCharacter
