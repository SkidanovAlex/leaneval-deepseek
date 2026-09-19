import Mathlib
import Submission.Commons.Analysis.Fourier.perronStep_deviation
import Submission.Commons.NumberTheory.Zeta.perronOne_bound
import Submission.Commons.NumberTheory.Zeta.mangoldt_perron_sum_eq
import Submission.Commons.NumberTheory.Zeta.mangoldtPerronError_bound
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_truncatedPerron

/-! Development of the truncated Perron formula for Chebyshev's psi function. -/

noncomputable section

open scoped BigOperators
open Filter Finset
open Real
open ArithmeticFunction hiding log id

namespace Commons.NumberTheory.Zeta

/-! ## Local definitions and facts -/

/-- The per-step Perron integral `(1/2π) ∫_{-T}^{T} exp((σ+it)·log z)/(σ+it) dt`. -/
private noncomputable def perronStep (σ T : ℝ) (z : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
    Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ))) /
      ((σ : ℂ) + Complex.I * (t : ℂ)))

/-- The mangoldt error summand appearing in the Perron bound. -/
private noncomputable def mangoldtErrSummand (x T : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
    min 1 (1 / (T * |Real.log (x / (n : ℝ))|))

private lemma log_pos_of_three_le {x : ℝ} (hx : 3 ≤ x) : 0 < Real.log x := by
  have h1x : 1 < x := by linarith
  exact Real.log_pos h1x

private lemma sigma_ge_one {x : ℝ} (hx : 3 ≤ x) : 1 ≤ 1 + 1 / Real.log x := by
  have hlog : 0 < Real.log x := log_pos_of_three_le hx
  nlinarith [one_div_pos.mpr hlog]

private lemma sigma_gt_one {x : ℝ} (hx : 3 ≤ x) : 1 < 1 + 1 / Real.log x := by
  have hlog : 0 < Real.log x := log_pos_of_three_le hx
  have : 0 < 1 / Real.log x := one_div_pos.mpr hlog
  linarith

private lemma nat_le_x_iff_floor {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (n : ℝ) ≤ x ↔ n ≤ ⌊x⌋₊ := by
  constructor
  · intro h
    exact Nat.le_floor h
  · intro h
    have hcast : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h
    exact le_trans hcast (Nat.floor_le hx)

/-- `ψ x` equals the tsum of the (complex) von Mangoldt values over naturals ≤ x. -/
private lemma psi_eq_tsum_indicator {x : ℝ} (hx : 0 ≤ x) :
    (Chebyshev.psi x : ℂ) = ∑' n : ℕ, if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0 := by
  have hmain : (∑' n : ℕ, if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
      = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0) := by
    apply tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.Icc 0 ⌊x⌋₊)
      (f := fun n : ℕ => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
    intro n hn
    by_cases hx0 : (n : ℝ) ≤ x
    · exfalso
      have hnfl : n ≤ ⌊x⌋₊ := (nat_le_x_iff_floor hx n).mp hx0
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnfl⟩)
    · simp [hx0]
  rw [hmain]
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hle : (n : ℝ) ≤ x := (nat_le_x_iff_floor hx n).mpr (Finset.mem_Icc.mp hn).2
  simp [hle]

/-- Per-step deviation bound, restated for our definition `perronStep`. -/
private lemma perronStep_dev_le {σ T z : ℝ} (hσ : 1 ≤ σ) (hT : 1 ≤ T) (hz : 0 < z) (hz1 : z ≠ 1) :
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
  exact perronOne_bound σ T hσ hT

/-- Factor `Λ n` out of the indicator-cut von Mangoldt value. -/
private lemma mangoldt_if_mul (x : ℝ) (n : ℕ) :
    (if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
      = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (if (n : ℝ) ≤ x then (1 : ℂ) else 0) := by
  by_cases h : (n : ℝ) ≤ x <;> simp [h]

/-- Pointwise bound for the `n`-th term of the error sum. -/
private lemma mangoldt_pointwise {x T : ℝ} (hx3 : 3 ≤ x) (hT : 2 ≤ T) (n : ℕ) :
    ‖(if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
        - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
      ≤ ((ArithmeticFunction.vonMangoldt n : ℝ)) *
            ((32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) +
          (if (n : ℝ) = x then 2 * (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    by_cases hnx : (n : ℝ) = x
    · -- case n = x
      have hle : (n : ℝ) ≤ x := le_of_eq hnx
      have hxeq : x = (n : ℝ) := hnx.symm
      have hdiv : x / (n : ℝ) = 1 := by
        rw [hxeq]
        exact div_self (by exact_mod_cast (Nat.pos_of_ne_zero hn0).ne')
      rw [if_pos hle]
      rw [if_pos hnx]
      rw [hdiv]
      have hfac : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) -
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              perronStep (1 + 1 / Real.log x) T 1
          = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              ((1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1) := by
        ring
      rw [hfac]
      have hnormΛ : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
          (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simp [abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
      have hQ : ‖(1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1‖ ≤ 3 / 2 := by
        apply norm_sub_one_le
        apply perronStep_one_norm (σ := 1 + 1 / Real.log x) (T := T)
        · have : 0 < 1 + 1 / Real.log x := by
            exact lt_of_lt_of_le zero_lt_one (sigma_ge_one hx3)
          exact this
        · linarith
      calc
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1)‖
            ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ *
                ‖(1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1‖ := by
              exact norm_mul_le _ _
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (3 / 2) := by
          rw [hnormΛ]
          exact mul_le_mul_of_nonneg_left hQ (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        _ ≤ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) := by
          nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
      simp [Real.log_one]
    · -- case n ≠ x
      rw [if_neg hnx]
      have hind : (if (n : ℝ) ≤ x then (1 : ℂ) else 0) = if (n : ℝ) < x then (1 : ℂ) else 0 := by
        by_cases hlt : (n : ℝ) < x
        · have hle' : (n : ℝ) ≤ x := le_of_lt hlt
          simp [hlt, hle']
        · have hle' : ¬ (n : ℝ) ≤ x := by
            intro h
            exact hlt (lt_of_le_of_ne h hnx)
          simp [hlt, hle']
      have hB : ‖(if (n : ℝ) < x then (1 : ℂ) else 0) - perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
          ≤ (32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) := by
        rw [norm_sub_rev]
        exact perronStep_mangoldt_le hx3 hT hn1 hnx
      calc
        ‖(if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
            = ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                ((if (n : ℝ) < x then (1 : ℂ) else 0) -
                  perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)))‖ := by
              rw [mangoldt_if_mul x n, hind, ← mul_sub]
            _ ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ *
                ‖((if (n : ℝ) < x then (1 : ℂ) else 0) -
                  perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)))‖ := by
              exact norm_mul_le _ _
            _ = (ArithmeticFunction.vonMangoldt n : ℝ) *
                ‖((if (n : ℝ) < x then (1 : ℂ) else 0) -
                  perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)))‖ := by
              have hnorm : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
                  (ArithmeticFunction.vonMangoldt n : ℝ) := by
                simp [abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

              rw [hnorm]
            _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
                ((32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
                  min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := by
              exact mul_le_mul_of_nonneg_left hB (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      simp

/-- The truncated Perron integral from the statement. -/
private noncomputable def perronInt (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
    (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
      (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))

/-- The Perron integral expands into the weighted per-step sums. -/
private lemma perronInt_eq_tsum {x : ℝ} (hx : 1 < x) {T : ℝ} :
    perronInt x T =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)) := by
  unfold perronInt
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [mangoldt_perron_sum_eq x (by linarith) (1 + 1 / Real.log x) T (by
    have : 0 < 1 / Real.log x := one_div_pos.mpr hlog
    linarith)]
  apply tsum_congr
  intro n
  simp [perronStep, mul_assoc]

/-- Indicator-cut von Mangoldt sequence is summable (finite support). -/
private lemma summable_indicator {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0) := by
  let s : Finset ℕ := Finset.Icc 0 ⌊x⌋₊
  have hfin : HasSum (fun n : ℕ => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
      (∑ n ∈ s, (if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)) := by
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
  simp [s]
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

/-- The main inequality: `ψ(x)` approximates the truncated Perron integral. -/
private lemma psi_sub_perron_main {x T : ℝ} (hx3 : 3 ≤ x) (hT : 2 ≤ T) :
    ‖(Chebyshev.psi x : ℂ) - perronInt x T‖ ≤
      (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) + 2 * Real.log x := by
  let ind : ℕ → ℂ := fun n => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0
  let q : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))
  let u : ℕ → ℂ := fun n => ind n - q n
  let a : ℕ → ℝ := fun n => mangoldtErrSummand x T n
  let extra : ℕ → ℝ := fun n => if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0
  let e : ℕ → ℝ := fun n => (32 / (2 * Real.pi)) * a n + extra n
  have hxpos : 0 < x := by linarith
  have hψ : (Chebyshev.psi x : ℂ) = ∑' n : ℕ, ind n := by
    dsimp [ind]
    exact psi_eq_tsum_indicator hxpos.le
  have hJ : perronInt x T = ∑' n : ℕ, q n := by
    dsimp [q]
    exact perronInt_eq_tsum (x := x) (hx := by linarith) (T := T)
  have hsum_a : Summable a := by
    rcases mangoldtPerronError_bound with ⟨CA, hCApos, hCA⟩
    exact (hCA x hx3 T hT).1
  have hsum_ind : Summable ind := by
    simpa [ind] using (summable_indicator (x := x) hxpos.le)
  have hsum_extra : Summable extra := by
    simpa [extra] using (summable_extra (x := x))
  have hpt : ∀ n : ℕ, ‖u n‖ ≤ e n := by
    intro n
    have hmain := mangoldt_pointwise (x := x) (T := T) hx3 hT n
    -- mangoldt_pointwise concludes ‖(if n≤x then Λn else 0) − (Λn)·Q‖ ≤ Λn·B + extra
    simp only [u, ind, q, e, a, extra, mangoldtErrSummand] at hmain ⊢
    -- RHS of hmain: (Λ n) * ((32/(2π)) * ((x/n)^c) * min 1 ...) + if (n:ℝ)=x then 2Λn else 0
    -- = (32/(2π))·(Λn·(x/n)^c·min...) + extra n
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
    ‖(Chebyshev.psi x : ℂ) - perronInt x T‖ = ‖(∑' n : ℕ, ind n) - (∑' n : ℕ, q n)‖ := by
      rw [hψ, hJ]
    _ = ‖∑' n : ℕ, u n‖ := by
      have hqsum : (∑' n : ℕ, q n) = (∑' n : ℕ, ind n) - (∑' n : ℕ, u n) := by
        have hts := Summable.tsum_sub hsum_ind hsum_u
        -- hts : Σ'(ind - u) = Σ'ind - Σ'u
        -- q n = ind n - u n
        simpa [u, q] using hts
      rw [hqsum]
      congr 1
      ring
    _ ≤ ∑' n : ℕ, ‖u n‖ := norm_tsum_le_tsum_norm hsum_norm_u
    _ ≤ ∑' n : ℕ, e n := by
      exact hasSum_le (fun n => hpt n) hsum_norm_u.hasSum hsum_e.hasSum
    _ = (32 / (2 * Real.pi)) * (∑' n : ℕ, a n) + (∑' n : ℕ, extra n) := by
      have hmul' : (∑' n : ℕ, (32 / (2 * Real.pi)) * a n) = (32 / (2 * Real.pi)) * (∑' n : ℕ, a n) := by
        exact tsum_mul_left (a := (32 / (2 * Real.pi))) (f := a)
      have hts := Summable.tsum_add (f := fun n : ℕ => (32 / (2 * Real.pi)) * a n) (g := extra)
        (by simpa [a] using (hsum_a.const_smul (32 / (2 * Real.pi)) : Summable (fun n => (32 / (2 * Real.pi)) • a n))) hsum_extra
      -- hts : Σ'( (32/2π)·a + extra ) = Σ'((32/2π)·a) + Σ'extra
      rw [hts, hmul']
    _ ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) + 2 * Real.log x := by
      have hle : (∑' n : ℕ, extra n) ≤ 2 * Real.log x := by
        simpa [extra] using (extra_tsum_le (x := x) hx3)
      rw [show (∑' n : ℕ, a n) = ∑' n : ℕ, mangoldtErrSummand x T n by rfl]
      nlinarith

theorem chebyshevPsi_truncatedPerron :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 3 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
          (∫ (t : ℝ) in -T..T,
            (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  rcases mangoldtPerronError_bound with ⟨CA, hCApos, hCA⟩
  refine ⟨(32 / (2 * Real.pi)) * CA + 2, by positivity, ?_⟩
  intro x hx T hT
  have hm := psi_sub_perron_main hx hT
  have hA : (∑' n : ℕ, mangoldtErrSummand x T n) ≤
      CA * (x * (Real.log x) ^ 2 / T + Real.log x) := (hCA x hx T hT).2
  have hTpos : 0 < T := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hmain1 : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
  have hlogB : 2 * Real.log x ≤ 2 * (x * (Real.log x) ^ 2 / T + Real.log x) := by nlinarith
  have hBpos : 0 ≤ x * (Real.log x) ^ 2 / T + Real.log x := by nlinarith
  calc
    ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
          (∫ (t : ℝ) in -T..T,
            (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖
        ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) + 2 * Real.log x := by
          change ‖(Chebyshev.psi x : ℂ) - perronInt x T‖ ≤
            (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) + 2 * Real.log x
          exact hm
    _ ≤ (32 / (2 * Real.pi)) * (CA * (x * (Real.log x) ^ 2 / T + Real.log x)) + 2 * Real.log x := by
          have hc : 0 ≤ (32 / (2 * Real.pi)) := by positivity
          nlinarith
    _ ≤ ((32 / (2 * Real.pi)) * CA + 2) * (x * (Real.log x) ^ 2 / T + Real.log x) := by
          nlinarith [hlogB, hBpos]

end Commons.NumberTheory.Zeta