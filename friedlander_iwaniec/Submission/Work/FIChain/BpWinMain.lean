/-
# `Submission.Work.FIChain.BpWinMain` — the `b₁ ≤ Δπ` half of the `Π`-removal

The ingredients of the `b₁ ≤ Δπ` half of `Work.FIChain.BprimeWindowIntegrated` (the companion
paper's §10, Theorem 3):

* `s1F Pz D` — the divisors of `Π(Pz)` that are `≤ D` (the range of the `b₁`-sum);
* `tau_grouping_s1F` — `Xf_tau_grouping` in that notation;
* `integrable_sum_wc_Xf_div`, `integrable_double_div`, `integrable_G1` — interval-integrability
  of the integrands occurring in the proof;
* `log_zpow_absorb`, `awbw_exp_bound` — the two numerical exponent bookkeepings
  (`L^{-12}·2L ≤ 2L^{-4}` and the product of the two pointwise inputs into `(√·Ã·L^{-12})²`);
* `bprime_window_main_le` — the bound for the `b₁ ≤ Δπ` half: pointwise triangle inequality,
  substitution `u = t/b₁`, range extension to the common range `[lo/D, hi]`, the `τ³`-grouping,
  pointwise Cauchy–Schwarz against `Aw` and `Bw`, and the constant integral.

This file contains no `sorry` and no `axiom`.
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FIChain.BpWinAux
import Submission.Work.FIChain.Xf_tau_grouping

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The range of the `b₁`-sum -/

/-- The divisors of `Π(Pz)` that are `≤ D`. -/
def s1F (Pz : ℕ) (D : ℝ) : Finset ℕ :=
  ((ProdP Pz).divisors).filter (fun b₁ : ℕ => (b₁ : ℝ) ≤ D)

/-- The weight `wc` is the divisor-count square, by definition. -/
lemma wc_eq (m : ℕ) : wc m = ((m.divisors.card : ℝ)) ^ 2 := rfl

/-- The weight `wc` is nonnegative. -/
lemma wc_nonneg (m : ℕ) : 0 ≤ wc m := by
  rw [wc_eq]; positivity

/-- `Xf_tau_grouping` in the `s1F` notation (and with the weight `wc = τ²`). -/
lemma tau_grouping_s1F (x Pz : ℕ) (D u : ℝ) :
    (∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) u|)
      ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u| := by
  have h := Xf_tau_grouping x Pz D u
  simpa only [s1F, wc_eq] using h

/-! ## 1. Integrability of the integrands -/

/-- Integrability of the composed `b₁`-term `(Σ_m wc m |Xf (m b₁) (t/b₁)|)/t`. -/
lemma integrable_sum_wc_Xf_div (x Pz b₁ : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ m ∈ Finset.Icc 1 x,
      wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t) volume a b := by
  refine intervalIntegrable_div_of_bounded' (C := (x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x))
    ha hab ?_ ?_
  · refine Finset.measurable_sum _ (fun m _ => ?_)
    exact Measurable.const_mul (Measurable.abs
      ((measurable_Xf' x Pz (m * b₁)).comp (measurable_id.div_const (b₁ : ℝ)))) (wc m)
  · intro t
    have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) (t / b₁)| :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (wc_nonneg _) (abs_nonneg _))
    rw [abs_of_nonneg hnn]
    calc (∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) (t / b₁)|)
        ≤ ∑ m ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 * AcountAtilC x :=
          Finset.sum_le_sum (fun m hm => mul_le_mul (wc_le x m hm)
            (abs_Xf_le_Acount x Pz (m * b₁) (t / b₁)) (abs_nonneg _)
            (pow_nonneg (Nat.cast_nonneg x) 2))
      _ = (x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x) := by
          rw [Finset.sum_const]
          simp only [smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
          ring

/-- Integrability of the un-composed `b₁`-term `(Σ_m wc m |Xf (m b₁) u|)/u`. -/
lemma integrable_sum_wc_Xf (x Pz b₁ : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => (∑ m ∈ Finset.Icc 1 x,
      wc m * |Xf x Pz (m * b₁) u|) / u) volume a b := by
  refine intervalIntegrable_div_of_bounded' (C := (x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x))
    ha hab ?_ ?_
  · refine Finset.measurable_sum _ (fun m _ => ?_)
    exact Measurable.const_mul (Measurable.abs (measurable_Xf' x Pz (m * b₁))) (wc m)
  · intro t
    have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) t| :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (wc_nonneg m) (abs_nonneg _))
    rw [abs_of_nonneg hnn]
    calc (∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) t|)
        ≤ ∑ m ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 * AcountAtilC x :=
          Finset.sum_le_sum (fun m hm => mul_le_mul (wc_le x m hm)
            (abs_Xf_le_Acount x Pz (m * b₁) t) (abs_nonneg _)
            (pow_nonneg (Nat.cast_nonneg x) 2))
      _ = (x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x) := by
          rw [Finset.sum_const]
          simp only [Nat.card_Icc, Nat.add_sub_cancel]
          ring

/-- The divisors of `Π(Pz)` that exceed `Dpi x κ` (the range of the Rankin tail). -/
def s2F (Pz x : ℕ) (κ : ℝ) : Finset ℕ :=
  ((ProdP Pz).divisors).filter (fun b₁ : ℕ => Dpi x κ < b₁)

/-- Integrability of the integrand of the tail `b₁ > Δπ` half. -/
lemma integrable_G2 (x Pz : ℕ) (κ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ m ∈ Finset.Icc 1 x, wc m *
      |∑ b₁ ∈ s2F Pz x κ, (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      volume a b := by
  refine intervalIntegrable_div_of_bounded'
    (C := (x : ℝ) * (x : ℝ) ^ 2 * ((s2F Pz x κ).card : ℝ) * AcountAtilC x) ha hab ?_ ?_
  · refine Finset.measurable_sum _ (fun m _ => ?_)
    refine Measurable.const_mul (Measurable.abs (Finset.measurable_sum _
      (fun b₁ _ => ?_))) (wc m)
    exact Measurable.const_mul
      ((measurable_Xf' x Pz (m * b₁)).comp (measurable_id.div_const (b₁ : ℝ)))
      ((ArithmeticFunction.moebius b₁ : ℝ))
  · intro t
    have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)| :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (wc_nonneg m) (abs_nonneg _))
    rw [abs_of_nonneg hnn]
    have hstep1 : (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
          (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|)
        ≤ ∑ m ∈ Finset.Icc 1 x, ∑ b₁ ∈ s2F Pz x κ,
            (x : ℝ) ^ 2 * AcountAtilC x := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (wc_nonneg m)) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun b₁ _ => ?_)
      have hμ : |(ArithmeticFunction.moebius b₁ : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := b₁)
        exact_mod_cast h
      calc wc m * |(ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|
          = wc m * (|(ArithmeticFunction.moebius b₁ : ℝ)| *
              |Xf x Pz (m * b₁) (t / b₁)|) := by rw [abs_mul]
        _ ≤ wc m * |Xf x Pz (m * b₁) (t / b₁)| :=
            mul_le_mul_of_nonneg_left
              (by nlinarith [abs_nonneg (Xf x Pz (m * b₁) (t / b₁))]) (wc_nonneg m)
        _ ≤ (x : ℝ) ^ 2 * AcountAtilC x :=
            mul_le_mul (wc_le x m hm) (abs_Xf_le_Acount x Pz (m * b₁) (t / b₁))
              (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg x) 2)
    refine le_trans hstep1 (le_of_eq ?_)
    rw [Finset.sum_const, Finset.sum_const]
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    ring

/-- Integrability of the `b₁`-sum of the composed terms. -/
lemma integrable_double_div (x Pz : ℕ) (s : Finset ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x,
      wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t) volume a b := by
  refine intervalIntegrable_div_of_bounded'
    (C := (s.card : ℝ) * ((x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x))) ha hab ?_ ?_
  · refine Finset.measurable_sum _ (fun b₁ _ => ?_)
    refine Finset.measurable_sum _ (fun m _ => ?_)
    exact Measurable.const_mul (Measurable.abs
      ((measurable_Xf' x Pz (m * b₁)).comp (measurable_id.div_const (b₁ : ℝ)))) (wc m)
  · intro t
    have hnn : 0 ≤ ∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) (t / b₁)| :=
      Finset.sum_nonneg (fun b₁ _ => Finset.sum_nonneg
        (fun m _ => mul_nonneg (wc_nonneg _) (abs_nonneg _)))
    rw [abs_of_nonneg hnn]
    calc (∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) (t / b₁)|)
        ≤ ∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 * AcountAtilC x :=
          Finset.sum_le_sum (fun b₁ _ => Finset.sum_le_sum (fun m hm => mul_le_mul
            (wc_le x m hm) (abs_Xf_le_Acount x Pz (m * b₁) (t / b₁)) (abs_nonneg _)
            (pow_nonneg (Nat.cast_nonneg x) 2)))
      _ = (s.card : ℝ) * ((x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x)) := by
          rw [Finset.sum_const, Finset.sum_const]
          simp only [smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
          ring

/-- Integrability of the integrand of the `b₁ ≤ Δπ` half. -/
lemma integrable_G1 (x Pz : ℕ) (D : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ m ∈ Finset.Icc 1 x, wc m *
      |∑ b₁ ∈ s1F Pz D, (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      volume a b := by
  refine intervalIntegrable_div_of_bounded'
    (C := (x : ℝ) * (x : ℝ) ^ 2 * ((s1F Pz D).card : ℝ) * AcountAtilC x) ha hab ?_ ?_
  · refine Finset.measurable_sum _ (fun m _ => ?_)
    refine Measurable.const_mul (Measurable.abs (Finset.measurable_sum _
      (fun b₁ _ => ?_))) (wc m)
    exact Measurable.const_mul
      ((measurable_Xf' x Pz (m * b₁)).comp (measurable_id.div_const (b₁ : ℝ)))
      ((ArithmeticFunction.moebius b₁ : ℝ))
  · intro t
    have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)| :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (wc_nonneg _) (abs_nonneg _))
    rw [abs_of_nonneg hnn]
    have hstep1 : (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
          (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|)
        ≤ ∑ m ∈ Finset.Icc 1 x, ∑ b₁ ∈ s1F Pz D,
            (x : ℝ) ^ 2 * AcountAtilC x := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (wc_nonneg _)) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun b₁ _ => ?_)
      have hμ : |(ArithmeticFunction.moebius b₁ : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := b₁)
        exact_mod_cast h
      calc wc m * |(ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|
          = wc m * (|(ArithmeticFunction.moebius b₁ : ℝ)| *
              |Xf x Pz (m * b₁) (t / b₁)|) := by rw [abs_mul]
        _ ≤ wc m * |Xf x Pz (m * b₁) (t / b₁)| :=
            mul_le_mul_of_nonneg_left
              (by nlinarith [abs_nonneg (Xf x Pz (m * b₁) (t / b₁))]) (wc_nonneg _)
        _ ≤ (x : ℝ) ^ 2 * AcountAtilC x :=
            mul_le_mul (wc_le x m hm) (abs_Xf_le_Acount x Pz (m * b₁) (t / b₁))
              (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg x) 2)
    refine le_trans hstep1 (le_of_eq ?_)
    rw [Finset.sum_const, Finset.sum_const]
    simp only [smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    ring

/-! ## 2. The two numerical exponent bookkeepings -/

/-- `L^{-12} · (2L) ≤ 2 L^{-4}` for `L ≥ 1`. -/
lemma log_zpow_absorb (L : ℝ) (hL1 : 1 ≤ L) :
    L ^ (-(12 : ℤ)) * (2 * L) ≤ 2 * L ^ (-(4 : ℤ)) := by
  have hLne : L ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hL1)
  have h1 : L ^ (-(12 : ℤ)) * L = L ^ (-(11 : ℤ)) := by
    calc L ^ (-(12 : ℤ)) * L = L ^ (-(12 : ℤ)) * L ^ (1 : ℤ) := by rw [zpow_one]
      _ = L ^ (-(12 : ℤ) + 1) := by rw [← zpow_add₀ hLne]
      _ = L ^ (-(11 : ℤ)) := by norm_num
  calc L ^ (-(12 : ℤ)) * (2 * L) = 2 * (L ^ (-(12 : ℤ)) * L) := by ring
    _ = 2 * L ^ (-(11 : ℤ)) := by rw [h1]
    _ ≤ 2 * L ^ (-(4 : ℤ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact zpow_le_zpow_right₀ hL1 (by norm_num)

/-- The exponent bookkeeping of the Cauchy–Schwarz step: the product of the two pointwise
inputs is bounded by the square of the single constant `√(KA·CB)·A·L^{-12}`. -/
lemma awbw_exp_bound (KA CB A L : ℝ) (hKA : 0 ≤ KA) (hCB : 0 ≤ CB) (hA : 0 ≤ A)
    (hL1 : 1 ≤ L) :
    KA * A * L ^ (-((2 : ℝ) ^ (26 : ℕ))) * (CB * A * L ^ (262144 : ℕ))
      ≤ (Real.sqrt (KA * CB) * A * L ^ (-(12 : ℤ))) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hcomb : L ^ (-((2 : ℝ) ^ (26 : ℕ))) * L ^ (262144 : ℕ)
      = L ^ (-((2 : ℝ) ^ (26 : ℕ)) + ((262144 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast L 262144, ← Real.rpow_add hLpos]
  have hsq2 : (L ^ (-(12 : ℤ))) ^ 2 = L ^ (-(24 : ℤ)) := by
    rw [sq, ← zpow_add₀ (ne_of_gt hLpos)]
    norm_num
  have hkey : L ^ (-((2 : ℝ) ^ (26 : ℕ))) * L ^ (262144 : ℕ) ≤ (L ^ (-(12 : ℤ))) ^ 2 := by
    rw [hcomb, hsq2, ← Real.rpow_intCast L (-(24 : ℤ))]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    norm_num
  calc KA * A * L ^ (-((2 : ℝ) ^ (26 : ℕ))) * (CB * A * L ^ (262144 : ℕ))
      = (KA * CB * (A * A)) * (L ^ (-((2 : ℝ) ^ (26 : ℕ))) * L ^ (262144 : ℕ)) := by ring
    _ ≤ (KA * CB * (A * A)) * (L ^ (-(12 : ℤ))) ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (Real.sqrt (KA * CB) * A * L ^ (-(12 : ℤ))) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hKA hCB)]
        ring

/-! ## 3. The `b₁ ≤ Δπ` half -/

/-- **The `b₁ ≤ Δπ` half of the `Π`-removal.**  For `0 < lo ≤ lo/D ≤ hi`, `1 ≤ log x`, the
`L¹`-length bound `log (hi/(lo/D)) ≤ 2 log x`, and the two pointwise inputs `Aw ≤ KA·Ã·L^{-2^26}`,
`Bw ≤ CB·Ã·L^{262144}` on `[lo/D, hi]`, the `b₁ ≤ D` part of the window integral is at most
`2√(KA·CB)·Ã·L^{-4}`. -/
lemma bprime_window_main_le (x Pz : ℕ) (D lo hi : ℝ)
    (hDpos : 0 < D) (hlo_pos : 0 < lo) (hloD_le_hi : lo / D ≤ hi) (hlo_le_hi : lo ≤ hi)
    (KA CB : ℝ) (hKA : 0 ≤ KA) (hCB : 0 ≤ CB)
    (hAw : ∀ u ∈ Set.Icc (lo / D) hi,
      Aw x Pz u ≤ KA * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))))
    (hBw : ∀ u ∈ Set.Icc (lo / D) hi,
      Bw x Pz u ≤ CB * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ))
    (hL1 : 1 ≤ Real.log (x : ℝ))
    (hR : Real.log hi - Real.log (lo / D) ≤ 2 * Real.log (x : ℝ)) :
    (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m *
        |∑ b₁ ∈ s1F Pz D, (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ 2 * Real.sqrt (KA * CB) * (AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ))) := by
  have hÃnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg' x
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL1
  have hhi_pos : 0 < hi := lt_of_lt_of_le hlo_pos hlo_le_hi
  have hloD_pos : 0 < lo / D := div_pos hlo_pos hDpos
  have hwcnn : ∀ m : ℕ, 0 ≤ wc m := fun m => wc_nonneg m
  -- (1) pointwise triangle inequality
  have h1 : ∀ t : ℝ, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|)
      ≤ ∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
          wc m * |Xf x Pz (m * b₁) (t / b₁)| := by
    intro t
    calc (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
          (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|)
        ≤ ∑ m ∈ Finset.Icc 1 x, wc m * (∑ b₁ ∈ s1F Pz D,
            |(ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) :=
          Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left
            (Finset.abs_sum_le_sum_abs _ _) (hwcnn m))
      _ = ∑ m ∈ Finset.Icc 1 x, ∑ b₁ ∈ s1F Pz D,
            wc m * |(ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)| :=
          Finset.sum_congr rfl (fun m _ => by rw [Finset.mul_sum])
      _ = ∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
            wc m * |(ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)| :=
          Finset.sum_comm
      _ ≤ ∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
            wc m * |Xf x Pz (m * b₁) (t / b₁)| := by
          refine Finset.sum_le_sum (fun b₁ _ => Finset.sum_le_sum (fun m _ => ?_))
          have hμ : |(ArithmeticFunction.moebius b₁ : ℝ)| ≤ 1 := by
            have h := ArithmeticFunction.abs_moebius_le_one (n := b₁)
            exact_mod_cast h
          calc wc m * |(ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|
              = wc m * (|(ArithmeticFunction.moebius b₁ : ℝ)| *
                  |Xf x Pz (m * b₁) (t / b₁)|) := by rw [abs_mul]
            _ ≤ wc m * |Xf x Pz (m * b₁) (t / b₁)| :=
                mul_le_mul_of_nonneg_left
                  (by nlinarith [abs_nonneg (Xf x Pz (m * b₁) (t / b₁))]) (hwcnn m)
  -- (2) integrating the pointwise bound
  have h2 : (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ ∫ t in lo..hi, (∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
          wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t :=
    intervalIntegral.integral_mono_on hlo_le_hi
      (integrable_G1 x Pz D hlo_pos hlo_le_hi)
      (integrable_double_div x Pz (s1F Pz D) hlo_pos hlo_le_hi)
      (fun t ht => div_le_div_of_nonneg_right (h1 t) (le_trans hlo_pos.le ht.1))
  -- (3) exchange, substitute `u = t/b₁`, extend the range to `[lo/D, hi]`
  have h3a : (∫ t in lo..hi, (∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
        wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t)
      = ∑ b₁ ∈ s1F Pz D, ∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x,
          wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t := by
    rw [show (fun t : ℝ => (∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
          wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t)
        = fun t => ∑ b₁ ∈ s1F Pz D, (∑ m ∈ Finset.Icc 1 x,
            wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t from by
      funext t; rw [Finset.sum_div]]
    exact intervalIntegral.integral_finsetSum
      (fun b₁ _ => integrable_sum_wc_Xf_div x Pz b₁ hlo_pos hlo_le_hi)
  have h3b : (∑ b₁ ∈ s1F Pz D, ∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x,
        wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ ∫ u in lo / D..hi, (∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
          wc m * |Xf x Pz (m * b₁) u|) / u := by
    calc (∑ b₁ ∈ s1F Pz D, ∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x,
          wc m * |Xf x Pz (m * b₁) (t / b₁)|) / t)
        ≤ ∑ b₁ ∈ s1F Pz D, ∫ u in lo / D..hi, (∑ m ∈ Finset.Icc 1 x,
            wc m * |Xf x Pz (m * b₁) u|) / u := by
          refine Finset.sum_le_sum (fun b₁ hb₁ => ?_)
          have hb₁d : b₁ ∈ (ProdP Pz).divisors := (Finset.mem_filter.mp hb₁).1
          have hb₁D : (b₁ : ℝ) ≤ D := (Finset.mem_filter.mp hb₁).2
          have hb₁posN : 0 < b₁ :=
            Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb₁d).1 (ProdP_pos Pz)
          have hb₁pos : 0 < (b₁ : ℝ) := by exact_mod_cast hb₁posN
          have hb₁1 : (1 : ℝ) ≤ (b₁ : ℝ) := by exact_mod_cast hb₁posN
          rw [integral_div_comp_div'
            (fun u => ∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) u|) hb₁pos.ne']
          refine integral_mono_range' ?_ ?_ ?_ ?_
            (integrable_sum_wc_Xf x Pz b₁ hloD_pos hloD_le_hi)
          · rw [div_le_div_iff₀ hDpos hb₁pos]
            exact mul_le_mul_of_nonneg_left hb₁D hlo_pos.le
          · exact div_le_div_of_nonneg_right hlo_le_hi hb₁pos.le
          · rw [div_le_iff₀ hb₁pos]
            nlinarith [hhi_pos, hb₁1]
          · intro u hu
            exact div_nonneg
              (Finset.sum_nonneg (fun m _ => mul_nonneg (hwcnn m) (abs_nonneg _)))
              (le_trans hloD_pos.le hu.1)
      _ = ∫ u in lo / D..hi, (∑ b₁ ∈ s1F Pz D, (∑ m ∈ Finset.Icc 1 x,
            wc m * |Xf x Pz (m * b₁) u|) / u) :=
          (intervalIntegral.integral_finsetSum (μ := volume) (a := lo / D) (b := hi)
            (f := fun b₁ u => (∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) u|) / u)
            (fun b₁ _ => integrable_sum_wc_Xf x Pz b₁ hloD_pos hloD_le_hi)).symm
      _ = ∫ u in lo / D..hi, (∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
            wc m * |Xf x Pz (m * b₁) u|) / u := by
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          rw [Finset.sum_div]
  -- (4) the `τ³`-grouping
  have h4 : (∫ u in lo / D..hi, (∑ b₁ ∈ s1F Pz D, ∑ m ∈ Finset.Icc 1 x,
        wc m * |Xf x Pz (m * b₁) u|) / u)
      ≤ ∫ u in lo / D..hi, (∑ c ∈ Finset.Icc 1 x,
          ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u|) / u :=
    intervalIntegral.integral_mono_on hloD_le_hi
      (integrable_Xf_sum x Pz (s1F Pz D) hloD_pos hloD_le_hi)
      (integrable_tau_cub_sum x Pz hloD_pos hloD_le_hi)
      (fun u hu => div_le_div_of_nonneg_right (tau_grouping_s1F x Pz D u)
        (le_trans hloD_pos.le hu.1))
  -- (5) pointwise Cauchy–Schwarz
  have h5 : (∫ u in lo / D..hi, (∑ c ∈ Finset.Icc 1 x,
        ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u|) / u)
      ≤ ∫ u in lo / D..hi, (Real.sqrt (KA * CB) * AcountAtilC x
          * (Real.log (x : ℝ)) ^ (-(12 : ℤ))) / u := by
    refine intervalIntegral.integral_mono_on hloD_le_hi
      (integrable_tau_cub_sum x Pz hloD_pos hloD_le_hi)
      (integrable_const_div _ (by positivity) hloD_pos hloD_le_hi) (fun u hu => ?_)
    have hcs := sum_tau_cub_sq_le x Pz u
    have hSnn : 0 ≤ ∑ c ∈ Finset.Icc 1 x,
        ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u| :=
      Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity) (abs_nonneg _))
    have hKAnn : 0 ≤ KA * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) :=
      mul_nonneg (mul_nonneg hKA hÃnn) (Real.rpow_nonneg hLpos.le _)
    have hsq : ((∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u|)) ^ 2
        ≤ (Real.sqrt (KA * CB) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(12 : ℤ))) ^ 2 :=
      hcs.trans ((mul_le_mul (hAw u hu) (hBw u hu) (Bw_nonneg x Pz u) hKAnn).trans
        (awbw_exp_bound KA CB (AcountAtilC x) (Real.log (x : ℝ)) hKA hCB hÃnn hL1))
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hSnn, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)] at hsqrt
    exact div_le_div_of_nonneg_right hsqrt (le_trans hloD_pos.le hu.1)
  -- (6) the constant integral
  have h6 : (∫ u in lo / D..hi, (Real.sqrt (KA * CB) * AcountAtilC x
        * (Real.log (x : ℝ)) ^ (-(12 : ℤ))) / u)
      ≤ 2 * Real.sqrt (KA * CB) * (AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ))) := by
    have hCst : 0 ≤ Real.sqrt (KA * CB) * AcountAtilC x
        * (Real.log (x : ℝ)) ^ (-(12 : ℤ)) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hÃnn) (zpow_nonneg hLpos.le _)
    rw [show (∫ u in lo / D..hi, (Real.sqrt (KA * CB) * AcountAtilC x
            * (Real.log (x : ℝ)) ^ (-(12 : ℤ))) / u)
        = (Real.sqrt (KA * CB) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(12 : ℤ)))
            * ∫ u in lo / D..hi, u⁻¹ from by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun u _ => by rw [div_eq_mul_inv])]
    rw [integral_inv_of_pos hloD_pos hhi_pos]
    have hlog : Real.log (hi / (lo / D)) ≤ 2 * Real.log (x : ℝ) := by
      rw [Real.log_div hhi_pos.ne' hloD_pos.ne']
      exact hR
    calc (Real.sqrt (KA * CB) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(12 : ℤ)))
          * Real.log (hi / (lo / D))
        ≤ (Real.sqrt (KA * CB) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(12 : ℤ)))
            * (2 * Real.log (x : ℝ)) := mul_le_mul_of_nonneg_left hlog hCst
      _ = Real.sqrt (KA * CB) * AcountAtilC x
            * ((Real.log (x : ℝ)) ^ (-(12 : ℤ)) * (2 * Real.log (x : ℝ))) := by ring
      _ ≤ Real.sqrt (KA * CB) * AcountAtilC x
            * (2 * (Real.log (x : ℝ)) ^ (-(4 : ℤ))) :=
          mul_le_mul_of_nonneg_left (log_zpow_absorb _ hL1)
            (mul_nonneg (Real.sqrt_nonneg _) hÃnn)
      _ = 2 * Real.sqrt (KA * CB) * (AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ))) := by
          ring
  exact h2.trans (h3a.le.trans (h3b.trans (h4.trans (h5.trans h6))))

end

end Work.FIChain
