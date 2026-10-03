import Mathlib
import Submission.Work.FIChain.Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset Filter MeasureTheory Set
open Submission.ASP
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Interval integrability of the `S₃^{±}` integrands

The integrands appearing in the `§8` average of `S₃^{±}` are, for fixed `x` and `lam`, *step
functions of `y`*: all the `y`-dependence sits in the variable `sy = s·y` of the divisor filter
`sy < b`, whence the integrand is a finite sum of scaled indicator-type functions.  We record
the `sy`-sum in a single definition `S3step`, of which both `S3minusC` and `S3plusC` are
instances, and prove that the resulting integrand `y ↦ |S3step ... (s·y)| / y` is measurable and
uniformly bounded — hence interval integrable, since it is bounded by `Mstep / Y` on the interval
`(Y, e·Y]` with `Y > 0`. -/

/-- The `sy`-dependent divisor-filtered sum underlying both `S3minusC` and `S3plusC`.  The two
definitions differ only in their `H`-factor (the inner `c`-sum). -/
def S3step (N : ℕ) (lam : ℕ → ℝ) (H : ℕ → ℝ) (sy : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 N,
    (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
      (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ * H ℓ

lemma S3minusC_eq_S3step (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) :
    S3minusC a lam N z sy sz C
      = S3step N lam (fun ℓ => S3minusInnerC a N ℓ z sz C) sy := rfl

lemma S3plusC_eq_S3step (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) :
    S3plusC a lam N z sy sz C
      = S3step N lam (fun ℓ => S3plusInnerC a N ℓ z sz C) sy := rfl

/-- `S3step` is additive in its `H`-argument (as a function of `sy`). -/
lemma S3step_sub (N : ℕ) (lam : ℕ → ℝ) (Hp Hm : ℕ → ℝ) (sy : ℝ) :
    S3step N lam (fun ℓ => Hp ℓ - Hm ℓ) sy
      = S3step N lam Hp sy - S3step N lam Hm sy := by
  simp only [S3step]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  ring

/-! ### Measurability -/

/-- The inner divisor-filtered Möbius sum is measurable in `sy`: it is a finite sum of indicators
of the half-lines `{sy | sy < b}`. -/
lemma measurable_inner_divSum (ℓ : ℕ) :
    Measurable (fun sy : ℝ =>
      ∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)) := by
  have h : Measurable (fun sy : ℝ => ∑ b ∈ ℓ.divisors,
      if sy < ((b : ℕ) : ℝ) then (ArithmeticFunction.moebius b : ℝ) else 0) := by
    refine Finset.measurable_sum _ (fun b hb => ?_)
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  convert h using 1
  ext sy
  rw [Finset.sum_filter]

lemma measurable_S3step (N : ℕ) (lam : ℕ → ℝ) (H : ℕ → ℝ) :
    Measurable (S3step N lam H) := by
  unfold S3step
  refine Finset.measurable_sum _ (fun ℓ hℓ => ?_)
  exact ((measurable_inner_divSum ℓ).mul_const (rhoOf lam ℓ)).mul_const (H ℓ)

/-! ### A uniform bound -/

/-- Termwise bound for the inner divisor-filtered Möbius sum. -/
lemma abs_inner_divSum_le (ℓ : ℕ) (sy : ℝ) :
    |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)| ≤ (ℓ.divisors.card : ℝ) := by
  calc |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)|
      ≤ ∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          |(ArithmeticFunction.moebius b : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        exact Submission.ASP.abs_moebius_cast_le_one b
    _ = ((ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ))).card : ℝ) := by simp
    _ ≤ (ℓ.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset (fun b => sy < ((b : ℕ) : ℝ)) ℓ.divisors)

/-- **Uniform bound**: `S3step` is bounded on all of `ℝ` by the `lam`-, `H`-dependent constant
`Mstep`. -/
lemma abs_S3step_le (N : ℕ) (lam : ℕ → ℝ) (H : ℕ → ℝ) (sy : ℝ) :
    |S3step N lam H sy| ≤ ∑ ℓ ∈ Finset.Icc 1 N,
        ((ℓ.divisors.card : ℝ)) * |rhoOf lam ℓ| * |H ℓ| := by
  unfold S3step
  calc |∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ * H ℓ|
      ≤ ∑ ℓ ∈ Finset.Icc 1 N,
        |(∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ * H ℓ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ℓ ∈ Finset.Icc 1 N, ((ℓ.divisors.card : ℝ)) * |rhoOf lam ℓ| * |H ℓ| := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (abs_inner_divSum_le ℓ sy) (abs_nonneg _)) (abs_nonneg _)

lemma Mstep_nonneg (N : ℕ) (lam : ℕ → ℝ) (H : ℕ → ℝ) :
    0 ≤ ∑ ℓ ∈ Finset.Icc 1 N, ((ℓ.divisors.card : ℝ)) * |rhoOf lam ℓ| * |H ℓ| := by
  apply Finset.sum_nonneg
  intro ℓ hℓ
  positivity

/-! ### Interval integrability -/

/-- The integrand `y ↦ |S3step N lam H (s·y)| / y` is interval integrable on `(Y, e·Y]` whenever
`Y > 0`: it is measurable, bounded by `Mstep` on all of `ℝ`, and `1/y` is bounded by `1/Y`
there. -/
lemma intervalIntegrable_abs_step_div (B : ℝ) (x : ℕ) (hY : 0 < Yc x B)
    (lam : ℕ → ℝ) (H : ℕ → ℝ) :
    IntervalIntegrable (fun y : ℝ => |S3step x lam H (sc x B * y)| / y) volume
      (Yc x B) (Real.exp 1 * Yc x B) := by
  let M : ℝ := ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) * |rhoOf lam ℓ| * |H ℓ|
  have hMnn : 0 ≤ M := Mstep_nonneg x lam H
  have hmeas : Measurable (fun y : ℝ => |S3step x lam H (sc x B * y)| / y) :=
    (((measurable_S3step x lam H).comp
      (measurable_const.mul measurable_id)).abs).div measurable_id
  constructor
  · refine Measure.integrableOn_of_bounded (s_finite := (measure_Ioc_lt_top).ne)
      (f_mble := hmeas.aestronglyMeasurable) (M := M / Yc x B) ?_
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro y hy
    have hy0 : 0 < y := lt_trans hY hy.1
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hy0]
    calc |S3step x lam H (sc x B * y)| / y
        ≤ M / y := div_le_div_of_nonneg_right
            (abs_S3step_le x lam H (sc x B * y)) (le_of_lt hy0)
      _ ≤ M / Yc x B := div_le_div_of_nonneg_left hMnn hY (le_of_lt hy.1)
  · rw [Set.Ioc_eq_empty]
    · exact integrableOn_empty
    · show ¬ Real.exp 1 * Yc x B < Yc x B
      exact not_lt.mpr (by nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1), hY])

/-- `Yc x B` is eventually positive. -/
lemma eventually_Yc_pos (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop, 0 < Yc x B := by
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hx1 : (1 : ℝ) < (x : ℝ) := by
    have h2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  unfold Yc sc
  apply div_pos
  · exact Real.sqrt_pos.mpr hx0
  · exact mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      (Real.rpow_pos_of_pos (Real.log_pos hx1) _)

theorem S3xC_intervalIntegrable (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ lam : ℕ → ℝ,
      IntervalIntegrable (fun y : ℝ => |Work.FIChain.S3minusC Work.FIChain.atilc lam x
          (Work.FIChain.zc x B) (Work.FIChain.sc x B * y)
          (Work.FIChain.sc x B * Work.FIChain.zc x B)
          (((⌊(Work.FIChain.zc x B) ^ ((1 : ℝ) / 2)⌋₊ : ℕ) : ℝ))| / y)
        volume (Work.FIChain.Yc x B) (Real.exp 1 * Work.FIChain.Yc x B) ∧
      IntervalIntegrable (fun y : ℝ => |Work.FIChain.S3plusC Work.FIChain.atilc lam x
          (Work.FIChain.zc x B) (Work.FIChain.sc x B * y)
          (Work.FIChain.sc x B * Work.FIChain.zc x B)
          (((⌊(Work.FIChain.zc x B) ^ ((1 : ℝ) / 2)⌋₊ : ℕ) : ℝ))| / y)
        volume (Work.FIChain.Yc x B) (Real.exp 1 * Work.FIChain.Yc x B) ∧
      IntervalIntegrable (fun y : ℝ => |Work.FIChain.S3plusC Work.FIChain.atilc lam x
          (Work.FIChain.zc x B) (Work.FIChain.sc x B * y)
          (Work.FIChain.sc x B * Work.FIChain.zc x B)
          (((⌊(Work.FIChain.zc x B) ^ ((1 : ℝ) / 2)⌋₊ : ℕ) : ℝ))
          - Work.FIChain.S3minusC Work.FIChain.atilc lam x
          (Work.FIChain.zc x B) (Work.FIChain.sc x B * y)
          (Work.FIChain.sc x B * Work.FIChain.zc x B)
          (((⌊(Work.FIChain.zc x B) ^ ((1 : ℝ) / 2)⌋₊ : ℕ) : ℝ))| / y)
        volume (Work.FIChain.Yc x B) (Real.exp 1 * Work.FIChain.Yc x B) := by
  filter_upwards [eventually_Yc_pos B hB] with x hY
  intro lam
  let Cv : ℝ := ((⌊(zc x B) ^ ((1 : ℝ) / 2)⌋₊ : ℕ) : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · exact intervalIntegrable_abs_step_div B x hY lam
      (fun ℓ => S3minusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv)
  · exact intervalIntegrable_abs_step_div B x hY lam
      (fun ℓ => S3plusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv)
  · have hgoal : ∀ y : ℝ,
        S3plusC atilc lam x (zc x B) (sc x B * y) (sc x B * zc x B) Cv
          - S3minusC atilc lam x (zc x B) (sc x B * y) (sc x B * zc x B) Cv
        = S3step x lam (fun ℓ => S3plusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv
            - S3minusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv) (sc x B * y) := by
      intro y
      rw [S3plusC_eq_S3step, S3minusC_eq_S3step, ← S3step_sub]
    have hfun : (fun y : ℝ => |S3plusC atilc lam x (zc x B) (sc x B * y) (sc x B * zc x B) Cv
          - S3minusC atilc lam x (zc x B) (sc x B * y) (sc x B * zc x B) Cv| / y)
        = (fun y : ℝ => |S3step x lam
            (fun ℓ => S3plusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv
              - S3minusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv) (sc x B * y)| / y) := by
      funext y
      rw [hgoal y]
    rw [hfun]
    exact intervalIntegrable_abs_step_div B x hY lam
      (fun ℓ => S3plusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv
        - S3minusInnerC atilc x ℓ (zc x B) (sc x B * zc x B) Cv)

end

end Work.FIChain
