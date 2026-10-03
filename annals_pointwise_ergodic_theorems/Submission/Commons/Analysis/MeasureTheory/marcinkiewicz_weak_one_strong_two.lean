import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Marcinkiewicz interpolation: weak (1,1) + strong (2,2) implies strong (p,p)

This file proves the classical Marcinkiewicz interpolation theorem in the form needed for the
theorem `annals_pointwise_ergodic_theorems`: a subadditive (here additive) operator `T` which is
weak-type `(1,1)` with constant `A₀` and strong-type `(2,2)` with constant `A₁` is strong-type
`(p,p)` for `1 < p < 2`, with constant `C A₀^{2/p-1} A₁^{2-2/p}`.

The proof follows the standard truncation argument.  Since the functions involved are not assumed
measurable, the bookkeeping of the `L¹`/`L²` sizes of the truncations is done in terms of the
"inner tail" of a (possibly non-measurable) function `W`, i.e. the supremum of the measures of the
measurable subsets of the level sets `{W > u}`.
-/

open MeasureTheory Measure Filter Set
open scoped ENNReal

namespace Commons.Analysis.MeasureTheory

/-! ## Power integrals on rays

We record the values of `∫⁻ t in (0,X], t^q` and `∫⁻ t in (X,∞), t^q` (for suitable exponents),
which are used to evaluate the one-dimensional integrals appearing in the proof. -/

/-- The Lebesgue integral of `t^q` over `(0,X]`, for `q > -1`. -/
lemma lintegral_Ioc_ofReal_rpow {X q : ℝ} (hq : -1 < q) (hX : 0 ≤ X) :
    ∫⁻ t in Set.Ioc (0 : ℝ) X, ENNReal.ofReal (t ^ q)
      = ENNReal.ofReal (X ^ (q + 1) / (q + 1)) := by
  have hq0 : q + 1 ≠ 0 := by linarith
  have hInt : IntegrableOn (fun t : ℝ => t ^ q) (Set.Ioc (0 : ℝ) X) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := X) hq)
  have hval : ∫ t in Set.Ioc (0 : ℝ) X, t ^ q = X ^ (q + 1) / (q + 1) := by
    rw [← intervalIntegral.integral_of_le hX, integral_rpow (Or.inl hq),
      Real.zero_rpow hq0, sub_zero]
  have hmain : ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) X, t ^ q)
      = ∫⁻ t in Set.Ioc (0 : ℝ) X, ENNReal.ofReal (t ^ q) := by
    apply ofReal_integral_eq_lintegral_ofReal hInt
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg (mem_Ioc.1 ht).1.le q
  rw [← hval, hmain]

/-- The Lebesgue integral of `t^q` over `(X,∞)`, for `q < -1`. -/
lemma lintegral_Ioi_ofReal_rpow {X q : ℝ} (hq : q < -1) (hX : 0 < X) :
    ∫⁻ t in Set.Ioi X, ENNReal.ofReal (t ^ q)
      = ENNReal.ofReal (-(X ^ (q + 1) / (q + 1))) := by
  have hInt : IntegrableOn (fun t : ℝ => t ^ q) (Set.Ioi X) :=
    integrableOn_Ioi_rpow_of_lt hq hX
  have hval : ∫ t in Set.Ioi X, t ^ q = -(X ^ (q + 1) / (q + 1)) := by
    rw [integral_Ioi_rpow_of_lt hq hX, neg_div]
  have hmain : ENNReal.ofReal (∫ t in Set.Ioi X, t ^ q)
      = ∫⁻ t in Set.Ioi X, ENNReal.ofReal (t ^ q) := by
    apply ofReal_integral_eq_lintegral_ofReal hInt
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (hX.trans (mem_Ioi.1 ht))) q
  rw [← hval, hmain]

/-! ## The inner tail of a function

For a (possibly non-measurable) function `W : α → ℝ≥0∞` and a level `u : ℝ`, the "inner tail"
`innerTail μ W u` is the supremum of `μ E` over the measurable sets `E ⊆ {x | u < W x}`.  For a
measurable `W` this is exactly `μ {x | u < W x}`; for a general `W` it is the correct
"measurable size" of the level set, and it is the quantity that the sizes of the truncations of an
arbitrary function can be controlled by. -/

/-- The inner tail of `W`: the supremum of `μ E` over measurable subsets `E` of the level set
`{x | u < W x}`. -/
noncomputable def innerTail {α : Type*} [MeasurableSpace α] (μ : Measure α) (W : α → ℝ≥0∞)
    (u : ℝ) : ℝ≥0∞ :=
  ⨆ (E : {E : Set α // MeasurableSet E ∧ E ⊆ {x | ENNReal.ofReal u < W x}}), μ E.1

lemma innerTail_antitone {α : Type*} [MeasurableSpace α] (μ : Measure α) (W : α → ℝ≥0∞) :
    Antitone (innerTail μ W) := by
  intro u v huv
  refine iSup_le fun E => le_iSup_of_le ⟨E.1, E.2.1, fun x hx => ?_⟩ le_rfl
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal huv) (E.2.2 hx)

lemma le_innerTail {α : Type*} [MeasurableSpace α] {μ : Measure α} {W : α → ℝ≥0∞}
    {u : ℝ} {E : Set α} (hE : MeasurableSet E) (hsub : E ⊆ {x | ENNReal.ofReal u < W x}) :
    μ E ≤ innerTail μ W u :=
  le_iSup (fun E : {E : Set α // MeasurableSet E ∧ E ⊆ {x | ENNReal.ofReal u < W x}} => μ E.1)
    ⟨E, hE, hsub⟩

lemma innerTail_measurable {α : Type*} [MeasurableSpace α] (μ : Measure α) (W : α → ℝ≥0∞) :
    Measurable (innerTail μ W) :=
  (innerTail_antitone μ W).measurable

/-- Chebyshev-type bound for the inner tail: `u ^ p * innerTail μ W u ≤ ∫⁻ W ^ p`. -/
lemma pow_mul_innerTail_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {W : α → ℝ≥0∞}
    {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    ENNReal.ofReal u ^ p * innerTail μ W u ≤ ∫⁻ x, (W x) ^ p ∂μ := by
  rw [innerTail, ENNReal.mul_iSup]
  refine iSup_le fun E => ?_
  have h1 : ENNReal.ofReal u ^ p * μ E.1 =
      ∫⁻ x, (ENNReal.ofReal u) ^ p * E.1.indicator (fun _ => 1) x ∂μ := by
    rw [lintegral_const_mul'' _ ((measurable_const.indicator E.2.1).aemeasurable),
      lintegral_indicator E.2.1, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
  rw [h1]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ E.1
  · rw [Set.indicator_of_mem hx, mul_one]
    exact ENNReal.rpow_le_rpow (le_of_lt (E.2.2 hx)) hp
  · rw [Set.indicator_of_notMem hx, mul_zero]
    exact bot_le

/-! ## The test-function construction

Given levels `v i ≥ 0` and coefficients `c i ≥ 0` such that the numerical inequality
`∑ cᵢ 1_{vᵢ < w} ≤ w ^ p` holds for every `w`, and measurable sets `Eᵢ ⊆ {vᵢ < W}`, the weighted
sum `∑ cᵢ μ(Eᵢ)` is bounded by `∫⁻ W ^ p`.  This is the basic "duality" step of the
interpolation argument: the concrete numerical inequality is what makes the truncation argument
work. -/

/-- Telescoping inequality for a monotone sequence in `ℝ≥0∞`. -/
lemma sum_range_tsub_add (a : ℕ → ℝ≥0∞) (ha : Monotone a) (n : ℕ) :
    (∑ i ∈ Finset.range n, (a (i + 1) - a i)) + a 0 = a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, add_comm (a (n + 1) - a n) (a 0), ← add_assoc, ih]
    exact add_tsub_cancel_of_le (ha (Nat.le_succ n))

/-- The numerical inequality satisfied by the increments of `v ^ p` over an increasing sequence
`v`: for every `w`, `∑_{i<n} (v (i+1)^p - v i^p) 1_{v (i+1) < w} ≤ w^p`. -/
lemma numerical_core {n : ℕ} {v : ℕ → ℝ} (hv : Monotone v) (hv0 : ∀ i, 0 ≤ v i) {p : ℝ}
    (hp : 0 < p) (w : ℝ≥0∞) :
    (∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) *
        Set.indicator (Set.Ioi (ENNReal.ofReal (v (i + 1)))) (fun _ => 1) w) ≤ w ^ p := by
  classical
  set A := (Finset.range n).filter (fun i => ENNReal.ofReal (v (i + 1)) < w) with hA
  have hsum_eq : (∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) *
        Set.indicator (Set.Ioi (ENNReal.ofReal (v (i + 1)))) (fun _ => 1) w)
      = ∑ i ∈ A, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Set.indicator_apply]
    by_cases hc : ENNReal.ofReal (v (i + 1)) < w
    · rw [if_pos hc, if_pos (show w ∈ Set.Ioi (ENNReal.ofReal (v (i + 1))) from hc), mul_one]
    · rw [if_neg hc, if_neg (show ¬ w ∈ Set.Ioi (ENNReal.ofReal (v (i + 1))) from hc), mul_zero]
  rw [hsum_eq]
  rcases A.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Finset.sum_empty]; exact bot_le
  · have hmA : A.max' hne ∈ A := Finset.max'_mem A hne
    have hmval : ENNReal.ofReal (v (A.max' hne + 1)) < w := (Finset.mem_filter.1 hmA).2
    have hle : A ⊆ Finset.range (A.max' hne + 1) := by
      intro i hi
      rw [Finset.mem_range]
      have := Finset.le_max' A i hi
      omega
    set a : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (v i ^ p) with ha_def
    have hamon : Monotone a := fun i j hij =>
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hv0 i) (hv hij) hp.le)
    calc ∑ i ∈ A, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
        ≤ ∑ i ∈ Finset.range (A.max' hne + 1), ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) :=
          Finset.sum_le_sum_of_subset_of_nonneg hle (fun i _ _ => bot_le)
      _ = ∑ i ∈ Finset.range (A.max' hne + 1), (a (i + 1) - a i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          simp only [ha_def]
          rw [ENNReal.ofReal_sub (v (i + 1) ^ p) (Real.rpow_nonneg (hv0 i) p)]
      _ ≤ a (A.max' hne + 1) := by
          have hte := sum_range_tsub_add a hamon (A.max' hne + 1)
          have h0 : (0 : ℝ≥0∞) ≤ a 0 := bot_le
          calc ∑ i ∈ Finset.range (A.max' hne + 1), (a (i + 1) - a i)
              ≤ (∑ i ∈ Finset.range (A.max' hne + 1), (a (i + 1) - a i)) + a 0 := le_add_right le_rfl
            _ ≤ a (A.max' hne + 1) := le_of_eq hte
      _ ≤ w ^ p := by
          simp only [ha_def]
          rw [← ENNReal.ofReal_rpow_of_nonneg (hv0 _) hp.le]
          exact ENNReal.rpow_le_rpow hmval.le hp.le

/-- Existence of a measurable subset of a level set realising the inner tail up to a factor `2`. -/
lemma exists_measurable_subset_two_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {u : ℝ} (hlt : innerTail μ W u < ∞) :
    ∃ E : Set α, MeasurableSet E ∧ E ⊆ {x | ENNReal.ofReal u < W x} ∧
      innerTail μ W u ≤ 2 * μ E := by
  by_cases h0 : innerTail μ W u = 0
  · exact ⟨∅, MeasurableSet.empty, by simp, by rw [h0]; simp⟩
  · have h := ENNReal.half_lt_self h0 hlt.ne
    rw [innerTail] at h
    obtain ⟨E, hE⟩ := lt_iSup_iff.1 h
    refine ⟨E.1, E.2.1, E.2.2, ?_⟩
    have hcancel : (2 : ℝ≥0∞) * (innerTail μ W u / 2) = innerTail μ W u :=
      ENNReal.mul_div_cancel (by norm_num) (by norm_num)
    rw [← hcancel]
    exact mul_le_mul' le_rfl hE.le

/-- The test-function construction: for coefficients `c i` and levels `v i` satisfying the numerical
bound `∑ cᵢ 1_{vᵢ < w} ≤ w^p` for every `w`, and measurable sets `Eᵢ ⊆ {vᵢ < W}`, the weighted sum
`∑ cᵢ μ(Eᵢ)` is bounded by `∫⁻ W^p`. -/
lemma weighted_sum_meas_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) {c : ι → ℝ≥0∞} {v : ι → ℝ} {W : α → ℝ≥0∞} {p : ℝ} {E : ι → Set α}
    (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hsub : ∀ i ∈ s, E i ⊆ {x | ENNReal.ofReal (v i) < W x})
    (hnum : ∀ w : ℝ≥0∞, (∑ i ∈ s, c i *
        Set.indicator (Set.Ioi (ENNReal.ofReal (v i))) (fun _ => 1) w) ≤ w ^ p) :
    (∑ i ∈ s, c i * μ (E i)) ≤ ∫⁻ x, (W x) ^ p ∂μ := by
  have hψ : ∫⁻ x, (∑ i ∈ s, Set.indicator (E i) (fun _ => c i) x) ∂μ
      ≤ ∫⁻ x, (W x) ^ p ∂μ := by
    refine lintegral_mono fun x => ?_
    refine le_trans (Finset.sum_le_sum fun i hi => ?_) (hnum (W x))
    by_cases hx : x ∈ E i
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_Ioi.2 (hsub i hi hx)), mul_one]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hval : ∫⁻ x, (∑ i ∈ s, Set.indicator (E i) (fun _ => c i) x) ∂μ
      = ∑ i ∈ s, c i * μ (E i) := by
    rw [lintegral_finsetSum' s (f := fun i x => Set.indicator (E i) (fun _ => c i) x)]
    · exact Finset.sum_congr rfl fun i hi => lintegral_indicator_const (hE i hi) (c i)
    · intro i hi
      exact (measurable_const.indicator (hE i hi)).aemeasurable
  rw [← hval]
  exact hψ

/-- Weighted sums of inner tails are bounded by twice the `p`-th power integral. -/
lemma weighted_sum_innerTail_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    {s : Finset ι} {c : ι → ℝ≥0∞} {v : ι → ℝ} {W : α → ℝ≥0∞} {p : ℝ} (hp : 0 < p)
    (hv : ∀ i ∈ s, 0 < v i)
    (hnum : ∀ w : ℝ≥0∞, (∑ i ∈ s, c i *
        Set.indicator (Set.Ioi (ENNReal.ofReal (v i))) (fun _ => 1) w) ≤ w ^ p) :
    (∑ i ∈ s, c i * innerTail μ W (v i)) ≤ 2 * ∫⁻ x, (W x) ^ p ∂μ := by
  by_cases hA : ∫⁻ x, (W x) ^ p ∂μ = ∞
  · rw [hA, ENNReal.mul_top', if_neg (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
    exact le_top
  · classical
    have hAc : ∫⁻ x, (W x) ^ p ∂μ < ∞ := lt_top_iff_ne_top.2 hA
    have hfin : ∀ i ∈ s, innerTail μ W (v i) < ∞ := by
      intro i hi
      have hvi : ENNReal.ofReal (v i) ^ p * innerTail μ W (v i) ≤ ∫⁻ x, (W x) ^ p ∂μ :=
        pow_mul_innerTail_le (le_of_lt (hv i hi)) hp.le
      have hlt : ENNReal.ofReal (v i) ^ p * innerTail μ W (v i) < ∞ := lt_of_le_of_lt hvi hAc
      have hpos : ENNReal.ofReal (v i) ^ p ≠ 0 :=
        ne_of_gt (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.2 (hv i hi)) hp.le)
      rcases ENNReal.mul_lt_top_iff.mp hlt with ⟨-, hb⟩ | h | h
      · exact hb
      · exact absurd h hpos
      · rw [h]; exact ENNReal.zero_lt_top
    let E : ι → Set α := fun i => if hi : i ∈ s then
      Classical.choose (exists_measurable_subset_two_mul (hfin i hi)) else ∅
    have hE : ∀ i ∈ s, MeasurableSet (E i) := fun i hi => by
      simp only [E, dif_pos hi]
      exact (Classical.choose_spec (exists_measurable_subset_two_mul (hfin i hi))).1
    have hsub : ∀ i ∈ s, E i ⊆ {x | ENNReal.ofReal (v i) < W x} := fun i hi => by
      simp only [E, dif_pos hi]
      exact (Classical.choose_spec (exists_measurable_subset_two_mul (hfin i hi))).2.1
    have hbig : ∀ i ∈ s, innerTail μ W (v i) ≤ 2 * μ (E i) := fun i hi => by
      simp only [E, dif_pos hi]
      exact (Classical.choose_spec (exists_measurable_subset_two_mul (hfin i hi))).2.2
    calc (∑ i ∈ s, c i * innerTail μ W (v i))
        ≤ ∑ i ∈ s, c i * (2 * μ (E i)) :=
          Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (hbig i hi)
      _ = 2 * ∑ i ∈ s, c i * μ (E i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 2 * ∫⁻ x, (W x) ^ p ∂μ :=
          mul_le_mul' le_rfl (weighted_sum_meas_le s hE hsub hnum)

/-! ## The staircase (Riemann-sum) comparison

For an antitone function `f` on `ℝ` and a monotone sequence of break-points `v`, the integral of
`f` against a weight `g` over `(v 0, v n]` is sandwiched between the two Riemann-type sums
obtained by evaluating `f` at the endpoints of the cells.  The difference between the two sums is
controlled by the "jump" estimate, which telescopes because `f` is monotone. -/

/-- Majorant staircase: evaluating an antitone function at the left endpoints of the cells
over-estimates the weighted integral. -/
lemma lintegral_Ioc_le_sum_mul {f g : ℝ → ℝ≥0∞} (hg : Measurable g) (hf : Antitone f)
    {v : ℕ → ℝ} (hv : Monotone v) (n : ℕ) :
    ∫⁻ u in Set.Ioc (v 0) (v n), g u * f u ≤
      ∑ i ∈ Finset.range n, (∫⁻ u in Set.Ioc (v i) (v (i + 1)), g u) * f (v i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hsplit : Set.Ioc (v 0) (v (n + 1)) =
        Set.Ioc (v 0) (v n) ∪ Set.Ioc (v n) (v (n + 1)) :=
      (Set.Ioc_union_Ioc_eq_Ioc (a := v 0) (b := v n) (c := v (n + 1))
        (hv (Nat.zero_le n)) (hv (Nat.le_succ n))).symm
    have hdisj : Disjoint (Set.Ioc (v 0) (v n)) (Set.Ioc (v n) (v (n + 1))) := by
      rw [Set.disjoint_left]
      intro u hu1 hu2
      exact absurd (lt_of_le_of_lt hu1.2 hu2.1) (lt_irrefl u)
    rw [hsplit, lintegral_union measurableSet_Ioc hdisj]
    refine add_le_add ih ?_
    have hcell : ∫⁻ u in Set.Ioc (v n) (v (n + 1)), g u * f u
        ≤ ∫⁻ u in Set.Ioc (v n) (v (n + 1)), g u * f (v n) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc)] with u hu
      exact mul_le_mul' le_rfl (hf hu.1.le)
    rwa [lintegral_mul_const (f (v n)) hg] at hcell

/-- Minorant staircase: evaluating an antitone function at the right endpoints of the cells
under-estimates the weighted integral. -/
lemma sum_mul_le_lintegral_Ioc {f g : ℝ → ℝ≥0∞} (hg : Measurable g) (hf : Antitone f)
    {v : ℕ → ℝ} (hv : Monotone v) (n : ℕ) :
    (∑ i ∈ Finset.range n, (∫⁻ u in Set.Ioc (v i) (v (i + 1)), g u) * f (v (i + 1)))
      ≤ ∫⁻ u in Set.Ioc (v 0) (v n), g u * f u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hsplit : Set.Ioc (v 0) (v (n + 1)) =
        Set.Ioc (v 0) (v n) ∪ Set.Ioc (v n) (v (n + 1)) :=
      (Set.Ioc_union_Ioc_eq_Ioc (a := v 0) (b := v n) (c := v (n + 1))
        (hv (Nat.zero_le n)) (hv (Nat.le_succ n))).symm
    have hdisj : Disjoint (Set.Ioc (v 0) (v n)) (Set.Ioc (v n) (v (n + 1))) := by
      rw [Set.disjoint_left]
      intro u hu1 hu2
      exact absurd (lt_of_le_of_lt hu1.2 hu2.1) (lt_irrefl u)
    rw [hsplit, lintegral_union measurableSet_Ioc hdisj]
    refine add_le_add ih ?_
    have hcell : (∫⁻ u in Set.Ioc (v n) (v (n + 1)), g u) * f (v (n + 1))
        ≤ ∫⁻ u in Set.Ioc (v n) (v (n + 1)), g u * f u := by
      rw [← lintegral_mul_const (f (v (n + 1))) hg]
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc)] with u hu
      exact mul_le_mul' le_rfl (hf hu.2)
    exact hcell

/-- Telescoping of the successive differences of a monotone sequence in `ℝ≥0∞`. -/
lemma sum_range_tsub_telescope {a : ℕ → ℝ≥0∞} (ha : Antitone a) (n : ℕ) :
    (∑ i ∈ Finset.range n, (a i - a (i + 1))) + a n = a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, tsub_add_cancel_of_le (ha (Nat.le_succ n))]
    exact ih

/-- The jump estimate: the difference between the two staircases is bounded by the total variation
of `f`, here controlled by the initial value. -/
lemma sum_range_mul_tsub_le {f : ℝ → ℝ≥0∞} (hf : Antitone f) {v : ℕ → ℝ} (hv : Monotone v)
    (n : ℕ) {G : ℕ → ℝ≥0∞} {C : ℝ≥0∞} (hG : ∀ i, i < n → G i ≤ C) :
    (∑ i ∈ Finset.range n, G i * (f (v i) - f (v (i + 1)))) ≤ C * f (v 0) := by
  have htel := sum_range_tsub_telescope (a := fun i => f (v i)) (fun i j hij => hf (hv hij)) n
  have hsum : (∑ i ∈ Finset.range n, (f (v i) - f (v (i + 1)))) ≤ f (v 0) :=
    le_of_le_of_eq (le_add_right le_rfl) htel
  calc (∑ i ∈ Finset.range n, G i * (f (v i) - f (v (i + 1))))
      ≤ ∑ i ∈ Finset.range n, C * (f (v i) - f (v (i + 1))) :=
        Finset.sum_le_sum fun i hi => mul_le_mul' (hG i (Finset.mem_range.1 hi)) le_rfl
    _ = C * ∑ i ∈ Finset.range n, (f (v i) - f (v (i + 1))) := by rw [Finset.mul_sum]
    _ ≤ C * f (v 0) := mul_le_mul' le_rfl hsum

/-! ## Layer-cake bounds for the truncations

The sizes of the two truncations of a function `W` are controlled by the inner tail
`innerTail μ W`.  These are the estimates which replace the use of the measurability of `W`. -/

/-- The Lebesgue integral of `t^q` over `(a,b]` for `a ≥ 0` and `q > -1`. -/
lemma lintegral_Ioc_ofReal_rpow' {a b q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hq : -1 < q) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (t ^ q)
      = ENNReal.ofReal ((b ^ (q + 1) - a ^ (q + 1)) / (q + 1)) := by
  have hsplit : Set.Ioc (0 : ℝ) b = Set.Ioc (0 : ℝ) a ∪ Set.Ioc a b :=
    (Set.Ioc_union_Ioc_eq_Ioc (a := (0:ℝ)) (b := a) (c := b) ha hab).symm
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    exact absurd (lt_of_le_of_lt hu1.2 hu2.1) (lt_irrefl u)
  have hsum := lintegral_union (μ := volume) (f := fun t : ℝ => ENNReal.ofReal (t ^ q))
    measurableSet_Ioc hdisj
  rw [← hsplit] at hsum
  rw [lintegral_Ioc_ofReal_rpow hq ha, lintegral_Ioc_ofReal_rpow hq (ha.trans hab)] at hsum
  have hsum' : (∫⁻ (t : ℝ) in Set.Ioc a b, ENNReal.ofReal (t ^ q))
      + ENNReal.ofReal (a ^ (q + 1) / (q + 1)) = ENNReal.ofReal (b ^ (q + 1) / (q + 1)) := by
    rw [add_comm]
    exact hsum.symm
  have hsub : ∫⁻ (t : ℝ) in Set.Ioc a b, ENNReal.ofReal (t ^ q)
      = ENNReal.ofReal (b ^ (q + 1) / (q + 1)) - ENNReal.ofReal (a ^ (q + 1) / (q + 1)) :=
    ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsum'
  rw [hsub, ← ENNReal.ofReal_sub _ (div_nonneg (Real.rpow_nonneg ha _) (by linarith))]
  congr 1
  rw [sub_div]

/-- Layer-cake comparison: a measurable minorant `H` of `W` whose support lies above the level `a`
(in the sense that `H x > 0 → a < W x`) is controlled by the inner tails above the level `a`. -/
lemma lintegral_le_integral_innerTail_max {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {a : ℝ} {H : α → ℝ≥0∞} (hH : Measurable H)
    (hHW : ∀ x, H x ≤ W x) (hWfin : ∀ x, W x ≠ ∞)
    (ha : ∀ x, 0 < H x → ENNReal.ofReal a < W x) :
    ∫⁻ x, H x ∂μ ≤ ∫⁻ s in Set.Ioi (0 : ℝ), innerTail μ W (max a s) := by
  have hfin : ∀ x, H x ≠ ∞ := fun x => ne_top_of_le_ne_top (hWfin x) (hHW x)
  have hcongr : (fun x => H x) = fun x => ENNReal.ofReal ((H x).toReal) := by
    funext x; exact (ENNReal.ofReal_toReal (hfin x)).symm
  rw [hcongr, lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall fun x => ENNReal.toReal_nonneg)
    (hH.ennreal_toReal.aemeasurable)]
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  refine le_innerTail ?_ ?_
  · exact measurableSet_lt measurable_const hH.ennreal_toReal
  · intro x hx
    have hxpos : 0 < (H x).toReal := lt_trans hs hx
    have hHx : ENNReal.ofReal (H x).toReal = H x := ENNReal.ofReal_toReal (hfin x)
    have h1 : ENNReal.ofReal a < W x := ha x (by rw [← hHx]; exact ENNReal.ofReal_pos.2 hxpos)
    have h2 : ENNReal.ofReal s < W x := by
      have h2' : ENNReal.ofReal s < ENNReal.ofReal (H x).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.le).2 hx
      rw [hHx] at h2'
      exact h2'.trans_le (hHW x)
    rw [ENNReal.ofReal_max]
    exact max_lt h1 h2

/-- Splitting the layer-cake integral at the level `a`. -/
lemma lintegral_Ioi_innerTail_max {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {a : ℝ} (ha : 0 < a) :
    ∫⁻ s in Set.Ioi (0 : ℝ), innerTail μ W (max a s)
      = ENNReal.ofReal a * innerTail μ W a + ∫⁻ s in Set.Ioi a, innerTail μ W s := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) a ∪ Set.Ioi a :=
    (Set.Ioc_union_Ioi_eq_Ioi ha.le).symm
  rw [hsplit, lintegral_union measurableSet_Ioi]
  · congr 1
    · have hconst : ∫⁻ s in Set.Ioc (0 : ℝ) a, innerTail μ W (max a s)
          = ∫⁻ _ in Set.Ioc (0 : ℝ) a, innerTail μ W a := by
        refine lintegral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
        rw [max_eq_left hs.2]
      rw [hconst, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_Ioc, sub_zero, mul_comm]
    · refine lintegral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [max_eq_right hs.le]
  · rw [Set.disjoint_left]
    intro u hu1 hu2
    exact absurd (lt_of_le_of_lt hu1.2 hu2) (lt_irrefl u)

/-- The bound `a * tail a ≤ 2 ∫_{a/2}^{a} tail` used to get rid of the level term. -/
lemma ofReal_mul_innerTail_le_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * innerTail μ W a
      ≤ 2 * ∫⁻ s in Set.Ioc (a / 2) a, innerTail μ W s := by
  have hmono : ∫⁻ s in Set.Ioc (a / 2) a, innerTail μ W a
      ≤ ∫⁻ s in Set.Ioc (a / 2) a, innerTail μ W s := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    exact innerTail_antitone μ W hs.2
  have hval : ∫⁻ s in Set.Ioc (a / 2) a, innerTail μ W a
      = ENNReal.ofReal (a / 2) * innerTail μ W a := by
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
      show a - a / 2 = a / 2 by ring, mul_comm]
  have h2 : ENNReal.ofReal a = 2 * ENNReal.ofReal (a / 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  calc ENNReal.ofReal a * innerTail μ W a
      = 2 * (ENNReal.ofReal (a / 2) * innerTail μ W a) := by rw [h2, mul_assoc]
    _ = 2 * ∫⁻ s in Set.Ioc (a / 2) a, innerTail μ W a := by rw [hval]
    _ ≤ 2 * ∫⁻ s in Set.Ioc (a / 2) a, innerTail μ W s := mul_le_mul' le_rfl hmono

/-- The weight integral `∫_{(a,b]} 2u` in the form needed for the `L²` part. -/
lemma lintegral_Ioc_two_mul {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (2 * u) = ENNReal.ofReal (b ^ (2:ℝ) - a ^ (2:ℝ)) := by
  have hmul : (fun u : ℝ => ENNReal.ofReal (2 * u))
      = fun u : ℝ => ENNReal.ofReal 2 * ENNReal.ofReal u := by
    funext u; rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hstep : ∫⁻ u in Set.Ioc a b, ENNReal.ofReal 2 * ENNReal.ofReal u
      = ENNReal.ofReal 2 * ∫⁻ u in Set.Ioc a b, ENNReal.ofReal u :=
    lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top
  have hpow : ∫⁻ u in Set.Ioc a b, ENNReal.ofReal u
      = ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (u ^ (1:ℝ)) := by
    refine lintegral_congr fun u => ?_
    rw [Real.rpow_one]
  rw [hmul, hstep, hpow, lintegral_Ioc_ofReal_rpow' ha hab (by norm_num : (-1:ℝ) < 1)]
  rw [show ((1:ℝ) + 1) = 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-- The weight integral `∫_{(a,b]} p u^{p-1}` in the form needed for the `L^p` part. -/
lemma lintegral_Ioc_mul_rpow {a b p : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (p * u ^ (p - 1)) = ENNReal.ofReal (b ^ p - a ^ p) := by
  have hmul : (fun u : ℝ => ENNReal.ofReal (p * u ^ (p - 1)))
      = fun u : ℝ => ENNReal.ofReal p * ENNReal.ofReal (u ^ (p - 1)) := by
    funext u; rw [ENNReal.ofReal_mul (le_of_lt (by linarith : (0:ℝ) < p))]
  have hstep : ∫⁻ u in Set.Ioc a b, ENNReal.ofReal p * ENNReal.ofReal (u ^ (p - 1))
      = ENNReal.ofReal p * ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (u ^ (p - 1)) :=
    lintegral_const_mul' (ENNReal.ofReal p) _ ENNReal.ofReal_ne_top
  rw [hmul, hstep, lintegral_Ioc_ofReal_rpow' ha hab (by linarith : (-1:ℝ) < p - 1)]
  rw [show (p - 1) + 1 = p by ring, ← ENNReal.ofReal_mul (le_of_lt (by linarith : (0:ℝ) < p))]
  exact congrArg ENNReal.ofReal
    (by field_simp : p * ((b ^ p - a ^ p) / p) = b ^ p - a ^ p)

/-- Elementary arithmetic fact used to assemble the high-part estimate. -/
lemma add_le_three_mul {x y M : ℝ≥0∞} (hx : x ≤ 2 * M) (hy : y ≤ M) : x + y ≤ 3 * M := by
  calc x + y ≤ 2 * M + M := add_le_add hx hy
    _ = 3 * M := by simp only [show (3 : ℝ≥0∞) = 2 + 1 by norm_num, add_mul, one_mul]

/-- The high truncation at level `a` is bounded by three times the tail integral above `a/2`. -/
lemma lintegral_indicator_high_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} (hWfin : ∀ x, W x ≠ ∞) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal a < W x} W x ∂μ
      ≤ 3 * ∫⁻ s in Set.Ioi (a / 2), innerTail μ W s := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral (μ := μ)
    (f := fun x => Set.indicator {x : α | ENNReal.ofReal a < W x} W x)]
  refine iSup_le fun H => iSup_le fun hH => iSup_le fun hle => ?_
  have hHW : ∀ x, H x ≤ W x := fun x => (hle x).trans (Set.indicator_le_self _ _ x)
  have haH : ∀ x, 0 < H x → ENNReal.ofReal a < W x := by
    intro x hx
    by_contra hcon
    have h0 : H x ≤ 0 := by
      have hmem : x ∉ {x : α | ENNReal.ofReal a < W x} := hcon
      have hx' := hle x
      simp only [Set.indicator_of_notMem hmem] at hx'
      exact hx'
    exact absurd (le_antisymm h0 bot_le) hx.ne'
  have h1 : ∫⁻ s in Set.Ioc (a / 2) a, innerTail μ W s ≤ ∫⁻ s in Set.Ioi (a / 2), innerTail μ W s :=
    lintegral_mono_set Set.Ioc_subset_Ioi_self
  have h2 : ∫⁻ s in Set.Ioi a, innerTail μ W s ≤ ∫⁻ s in Set.Ioi (a / 2), innerTail μ W s :=
    lintegral_mono_set (Set.Ioi_subset_Ioi (by linarith))
  calc ∫⁻ x, H x ∂μ
      ≤ ∫⁻ s in Set.Ioi (0 : ℝ), innerTail μ W (max a s) :=
        lintegral_le_integral_innerTail_max (μ := μ) (W := W) hH hHW hWfin haH
    _ = ENNReal.ofReal a * innerTail μ W a + ∫⁻ s in Set.Ioi a, innerTail μ W s :=
        lintegral_Ioi_innerTail_max (μ := μ) (W := W) ha
    _ ≤ 3 * ∫⁻ s in Set.Ioi (a / 2), innerTail μ W s :=
        add_le_three_mul
          ((ofReal_mul_innerTail_le_two (μ := μ) (W := W) ha).trans (mul_le_mul' le_rfl h1)) h2

/-! ## Eliminating a vanishing error term -/

/-- If an inequality `x ≤ y + c/n` holds for all `n`, then `x ≤ y`. -/
lemma le_of_forall_ofReal_div_add_le {x y : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n : ℕ, x ≤ y + ENNReal.ofReal (c / (n + 1))) : x ≤ y := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (c / (ε : ℝ))
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0] at hn; simp at hn; linarith [show (0:ℝ) ≤ c / (ε:ℝ) by positivity]
    · exact_mod_cast hpos
  have hεpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have h2 : c < (n : ℝ) * (ε : ℝ) := (div_lt_iff₀ hεpos).mp hn
  have h3 : c / ((n : ℝ) + 1) ≤ (ε : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
    nlinarith
  calc x ≤ y + ENNReal.ofReal (c / ((n : ℝ) + 1)) := h n
    _ ≤ y + ENNReal.ofReal (ε : ℝ) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal h3)
    _ = y + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]

/-- `⨆ n, min a n = a` in `ℝ≥0∞`. -/
lemma iSup_min_natCast (a : ℝ≥0∞) : (⨆ n : ℕ, min a (n : ℝ≥0∞)) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  rcases eq_or_ne a ⊤ with h | h
  · rw [h]
    rw [show (⨆ n : ℕ, min (⊤ : ℝ≥0∞) (n : ℝ≥0∞)) = ⨆ n : ℕ, (n : ℝ≥0∞) from
      iSup_congr (fun n => by simp), ENNReal.iSup_natCast]
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
    exact le_iSup_of_le n (by rw [min_eq_left hn.le])

/-- Weighted sums of inner tails along an increasing sequence, in the form produced by the
numerical bound. -/
lemma sum_range_rpow_sub_mul_innerTail_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {p : ℝ} (hp : 0 < p) {v : ℕ → ℝ} (hv : Monotone v) (hv0 : ∀ i, 0 ≤ v i)
    (n : ℕ) (hpos : ∀ i, i < n → 0 < v (i + 1)) :
    (∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) *
        innerTail μ W (v (i + 1))) ≤ 2 * ∫⁻ x, (W x) ^ p ∂μ := by
  refine weighted_sum_innerTail_le (s := Finset.range n)
    (c := fun i => ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)) (v := fun i => v (i + 1))
    (W := W) (p := p) hp (fun i hi => hpos i (Finset.mem_range.1 hi)) (fun w => ?_)
  exact numerical_core hv hv0 hp w

lemma mul_le_mul_add_mul_tsub {a x y : ℝ≥0∞} : a * x ≤ a * y + a * (x - y) := by
  rcases le_total y x with h | h
  · rw [← mul_add, add_comm y (x - y), tsub_add_cancel_of_le h]
  · exact le_trans (mul_le_mul' le_rfl h) (le_add_right le_rfl)

/-- Staircase comparison for the `p`-th power weight: the integral of `p u^{p-1} × (truncated
inner tail)` over `(0,X]` is bounded by the corresponding Riemann sum over a partition with
break-points `v`, plus the error term coming from the jumps. -/
lemma sum_rpow_sub_mul_min_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {W : α → ℝ≥0∞}
    {p X : ℝ} {M C : ℝ≥0∞} (hp : 1 < p) (hX : 0 < X) {v : ℕ → ℝ} (n : ℕ) (hn : 0 < n)
    (hvmono : Monotone v) (hv0 : v 0 = 0) (hvn : v n = X) (hvpos : ∀ i, 0 ≤ v i)
    (hG : ∀ i, i < n → ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) ≤ C) :
    ∫⁻ u in Set.Ioc (0 : ℝ) X,
        ENNReal.ofReal (p * u ^ (p - 1)) * min (innerTail μ W u) M
      ≤ (∑ i ∈ Finset.range n,
          ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * innerTail μ W (v (i + 1)))
        + C * M := by
  have hanti : Antitone (fun u : ℝ => min (innerTail μ W u) M) :=
    fun a b hab => min_le_min (innerTail_antitone μ W hab) le_rfl
  have hS1 := lintegral_Ioc_le_sum_mul (f := fun u : ℝ => min (innerTail μ W u) M)
    (g := fun u : ℝ => ENNReal.ofReal (p * u ^ (p - 1)))
    (by measurability) hanti hvmono n
  rw [hv0, hvn] at hS1
  have hcell : ∀ i, i < n → (∫⁻ u in Set.Ioc (v i) (v (i + 1)), ENNReal.ofReal (p * u ^ (p - 1)))
      = ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) := fun i hi =>
    lintegral_Ioc_mul_rpow hp (hvpos i) (hvmono (Nat.le_succ i))
  have hS1' : ∫⁻ u in Set.Ioc (0 : ℝ) X, ENNReal.ofReal (p * u ^ (p - 1)) * min (innerTail μ W u) M
      ≤ ∑ i ∈ Finset.range n,
          ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * min (innerTail μ W (v i)) M := by
    refine hS1.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hcell i (Finset.mem_range.1 hi)]
  -- decompose each term into the right-endpoint value plus the jump
  have hpoint : ∀ i, i < n → ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * min (innerTail μ W (v i)) M
      ≤ ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * min (innerTail μ W (v (i + 1))) M
        + ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M) :=
    fun i hi => mul_le_mul_add_mul_tsub
  have hsplit : (∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
        * min (innerTail μ W (v i)) M)
      ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          * min (innerTail μ W (v (i + 1))) M)
        + ∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i hi => hpoint i (Finset.mem_range.1 hi)
  -- the jump sum
  have hjump := sum_range_mul_tsub_le (f := fun u : ℝ => min (innerTail μ W u) M)
    (fun a b hab => min_le_min (innerTail_antitone μ W hab) le_rfl) hvmono n
    (G := fun i => ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)) (C := C) hG
  rw [hv0] at hjump
  have hfinal : ∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
        * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M)
      ≤ C * M :=
    hjump.trans (mul_le_mul' le_rfl (min_le_right _ _))
  calc ∫⁻ u in Set.Ioc (0 : ℝ) X, ENNReal.ofReal (p * u ^ (p - 1)) * min (innerTail μ W u) M
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          * min (innerTail μ W (v i)) M := hS1'
    _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          * min (innerTail μ W (v (i + 1))) M)
        + ∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M) := hsplit
    _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          * innerTail μ W (v (i + 1)))
        + C * M := by
        refine add_le_add (Finset.sum_le_sum fun i hi => ?_) hfinal
        exact mul_le_mul' le_rfl (min_le_left _ _)

/-- The basic tail integral bound: `p ∫ u^{p-1} tail u ≤ 2 ∫ W^p`. -/
lemma rpow_mul_innerTail_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal p * ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u
      ≤ 2 * ∫⁻ x, (W x) ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  set A : ℝ≥0∞ := ∫⁻ x, (W x) ^ p ∂μ with hA
  have hmain : ∀ X : ℝ, 0 < X → ∀ m : ℕ,
      ENNReal.ofReal p * ∫⁻ u in Set.Ioc (0 : ℝ) X,
        ENNReal.ofReal (u ^ (p - 1)) * min (innerTail μ W u) (m : ℝ≥0∞) ≤ 2 * A := by
    intro X hX m
    have hmul : ENNReal.ofReal p * ∫⁻ u in Set.Ioc (0 : ℝ) X,
        ENNReal.ofReal (u ^ (p - 1)) * min (innerTail μ W u) (m : ℝ≥0∞)
        = ∫⁻ u in Set.Ioc (0 : ℝ) X,
          ENNReal.ofReal (p * u ^ (p - 1)) * min (innerTail μ W u) (m : ℝ≥0∞) := by
      rw [← lintegral_const_mul' (ENNReal.ofReal p) _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun u => ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hp0)]
    rw [hmul]
    have hstair : ∀ n : ℕ, ∫⁻ u in Set.Ioc (0 : ℝ) X,
          ENNReal.ofReal (p * u ^ (p - 1)) * min (innerTail μ W u) (m : ℝ≥0∞)
        ≤ 2 * A + ENNReal.ofReal (X ^ p * (m : ℝ) / (n + 1)) := by
      intro n
      set v : ℕ → ℝ := fun i => X * (((i : ℝ) / ((n : ℝ) + 1)) ^ (1 / p)) with hv
      have hv0 : v 0 = 0 := by
        simp only [v, Nat.cast_zero, zero_div, Real.zero_rpow (ne_of_gt (one_div_pos.2 hp0)),
          mul_zero]
      have hvn : v (n + 1) = X := by
        simp only [v, Nat.cast_add, Nat.cast_one]
        rw [div_self (by positivity : ((n:ℝ) + 1) ≠ 0), Real.one_rpow, mul_one]
      have hvcast : ∀ i : ℕ, v (i + 1) = X * ((((i:ℝ) + 1) / ((n:ℝ) + 1)) ^ (1 / p)) := fun i => by
        simp only [v, Nat.cast_add, Nat.cast_one]
      have hvmono : Monotone v := by
        intro i j hij
        simp only [v]
        have h1 : ((i : ℝ) / ((n : ℝ) + 1)) ^ (1 / p) ≤ ((j : ℝ) / ((n : ℝ) + 1)) ^ (1 / p) := by
          have hi0 : (0:ℝ) ≤ (i : ℝ) / ((n : ℝ) + 1) := by positivity
          have hle : (i : ℝ) / ((n : ℝ) + 1) ≤ (j : ℝ) / ((n : ℝ) + 1) :=
            div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
          exact Real.rpow_le_rpow hi0 hle (le_of_lt (one_div_pos.2 hp0))
        exact mul_le_mul_of_nonneg_left h1 hX.le
      have hvpos : ∀ i, 0 ≤ v i := by
        intro i
        simp only [v]
        exact mul_nonneg hX.le (Real.rpow_nonneg (by positivity) _)
      have hpow : ∀ i : ℕ, (v i) ^ p = X ^ p * ((i : ℝ) / ((n : ℝ) + 1)) := by
        intro i
        simp only [v]
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
          one_div_mul_cancel (by linarith : p ≠ 0), Real.rpow_one]
      have hG : ∀ i, i < n + 1 → ENNReal.ofReal (v (i + 1) ^ p - v i ^ p)
          ≤ ENNReal.ofReal (X ^ p / ((n : ℝ) + 1)) := by
        intro i hi
        rw [hpow i, hpow (i + 1), ← mul_sub,
          show ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) - (i : ℝ) / ((n : ℝ) + 1)
            = 1 / ((n : ℝ) + 1) by rw [← sub_div]; norm_num]
        rw [mul_one_div]
      have hst := sum_rpow_sub_mul_min_le (μ := μ) (W := W) (p := p) (X := X)
        (M := (m : ℝ≥0∞)) (C := ENNReal.ofReal (X ^ p / ((n : ℝ) + 1)))
        hp hX (n + 1) (Nat.succ_pos n) hvmono hv0 hvn hvpos hG
      have hsum : (∑ i ∈ Finset.range (n + 1),
            ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * innerTail μ W (v (i + 1))) ≤ 2 * A := by
        have h := sum_range_rpow_sub_mul_innerTail_le (μ := μ) (W := W) (p := p) hp0
          hvmono hvpos (n + 1) (fun i hi => by
            rw [hvcast i]
            positivity)
        simpa only [hA] using h
      refine hst.trans (add_le_add hsum (le_of_eq ?_))
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    exact le_of_forall_ofReal_div_add_le (by positivity) fun n => hstair n
  have hM : ∀ X : ℝ, 0 < X → ENNReal.ofReal p * ∫⁻ u in Set.Ioc (0 : ℝ) X,
        ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u ≤ 2 * A := by
    intro X hX
    have hmeas : Measurable fun u : ℝ => ENNReal.ofReal (u ^ (p - 1)) := by measurability
    have hconv : (⨆ m : ℕ, ∫⁻ u in Set.Ioc (0 : ℝ) X,
          ENNReal.ofReal (u ^ (p - 1)) * min (innerTail μ W u) (m : ℝ≥0∞))
        = ∫⁻ u in Set.Ioc (0 : ℝ) X, ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u := by
      rw [← lintegral_iSup]
      · refine lintegral_congr fun u => ?_
        rw [← ENNReal.mul_iSup]
        congr 1
        exact iSup_min_natCast (innerTail μ W u)
      · exact fun m => hmeas.mul ((innerTail_measurable μ W).min measurable_const)
      · exact fun i j hij u => mul_le_mul' le_rfl (min_le_min le_rfl (by exact_mod_cast hij))
    calc ENNReal.ofReal p * ∫⁻ u in Set.Ioc (0 : ℝ) X,
            ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u
        = ENNReal.ofReal p * ⨆ m : ℕ, ∫⁻ u in Set.Ioc (0 : ℝ) X,
            ENNReal.ofReal (u ^ (p - 1)) * min (innerTail μ W u) (m : ℝ≥0∞) := by rw [hconv]
      _ = ⨆ m : ℕ, ENNReal.ofReal p * ∫⁻ u in Set.Ioc (0 : ℝ) X,
            ENNReal.ofReal (u ^ (p - 1)) * min (innerTail μ W u) (m : ℝ≥0∞) :=
          ENNReal.mul_iSup _ _
      _ ≤ 2 * A := iSup_le fun m => hmain X hX m
  have hX' : (⨆ X : ℕ, ∫⁻ u in Set.Ioc (0 : ℝ) X,
        ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u)
      = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u := by
    have hmeas1 : Measurable fun u : ℝ => ENNReal.ofReal (u ^ (p - 1)) :=
      Measurable.ennreal_ofReal (by measurability)
    have hmeas : Measurable fun u : ℝ => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u :=
      hmeas1.mul (innerTail_measurable μ W)
    have h1 : ∀ X : ℕ, ∫⁻ u in Set.Ioc (0 : ℝ) X, ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u
        = ∫⁻ u, Set.indicator (Set.Ioc (0 : ℝ) X)
            (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u ∂volume :=
      fun X => (lintegral_indicator measurableSet_Ioc _).symm
    have h2 : ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u
        = ∫⁻ u, Set.indicator (Set.Ioi (0 : ℝ))
            (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u ∂volume :=
      (lintegral_indicator measurableSet_Ioi _).symm
    rw [h2]
    simp only [h1]
    rw [← lintegral_iSup]
    · refine lintegral_congr fun u => ?_
      refine le_antisymm (iSup_le fun X => ?_) ?_
      · show Set.indicator (Set.Ioc (0:ℝ) (X:ℝ))
            (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u
          ≤ Set.indicator (Set.Ioi (0:ℝ))
            (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u
        by_cases h : u ∈ Set.Ioc (0 : ℝ) (X:ℝ)
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_Ioi.2 h.1)]
        · rw [Set.indicator_of_notMem h]; exact bot_le
      · show Set.indicator (Set.Ioi (0:ℝ))
            (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u
          ≤ ⨆ X : ℕ, Set.indicator (Set.Ioc (0:ℝ) (X:ℝ))
            (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u
        by_cases h : u ∈ Set.Ioi (0:ℝ)
        · obtain ⟨X, hX⟩ := exists_nat_gt u
          refine le_iSup_of_le X ?_
          show Set.indicator (Set.Ioi (0:ℝ)) _ u ≤ Set.indicator (Set.Ioc (0:ℝ) (X:ℝ)) _ u
          rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show u ∈ Set.Ioc (0:ℝ) (X:ℝ) from ⟨h, hX.le⟩)]
        · rw [Set.indicator_of_notMem h]; exact bot_le
    · exact fun X => hmeas.indicator measurableSet_Ioc
    · intro i j hij u
      show Set.indicator (Set.Ioc (0:ℝ) (i:ℝ))
          (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u
        ≤ Set.indicator (Set.Ioc (0:ℝ) (j:ℝ))
          (fun u => ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u) u
      by_cases h : u ∈ Set.Ioc (0 : ℝ) (i:ℝ)
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show u ∈ Set.Ioc (0:ℝ) (j:ℝ) from
            ⟨h.1, h.2.trans (by exact_mod_cast hij)⟩)]
      · rw [Set.indicator_of_notMem h]
        exact bot_le
  calc ENNReal.ofReal p * ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u
      = ENNReal.ofReal p * ⨆ X : ℕ, ∫⁻ u in Set.Ioc (0 : ℝ) X,
          ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u := by rw [hX']
    _ = ⨆ X : ℕ, ENNReal.ofReal p * ∫⁻ u in Set.Ioc (0 : ℝ) X,
          ENNReal.ofReal (u ^ (p - 1)) * innerTail μ W u := ENNReal.mul_iSup _ _
    _ ≤ 2 * A := iSup_le fun X => by
        rcases Nat.eq_zero_or_pos X with h | h
        · subst h
          simp
        · exact hM X (by exact_mod_cast h)

lemma mul_le_mul_add_mul_tsub' {a x y : ℝ≥0∞} : a * x ≤ a * y + a * (x - y) :=
  mul_le_mul_add_mul_tsub

/-- Staircase comparison for the weight `s^((p-2)/2)` against `tail (√s)`: the integral over
`(0,X²]` is bounded by the Riemann sum over the partition whose `p`-th powers of the square roots
are equally spaced. -/
lemma sum_rpow_sqrt_min_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {W : α → ℝ≥0∞}
    {p X : ℝ} {M : ℝ≥0∞} (hp : 1 < p) (hX : 0 < X) {v : ℕ → ℝ} (n : ℕ) (hn : 0 < n)
    (hvmono : Monotone v) (hv0 : v 0 = 0) (hvn : v n = X) (hvpos : ∀ i, 0 ≤ v i)
    (hG : ∀ i, i < n → ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
      ≤ ENNReal.ofReal (2 * X ^ p / (p * n))) :
    ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) M
      ≤ (∑ i ∈ Finset.range n,
          ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p) * innerTail μ W (v (i + 1)))
        + ENNReal.ofReal (2 * X ^ p / (p * n)) * M := by
  have hanti : Antitone (fun s : ℝ => min (innerTail μ W (Real.sqrt s)) M) := fun a b hab =>
    min_le_min (innerTail_antitone μ W (Real.sqrt_le_sqrt hab)) le_rfl
  have hcell0 : ∀ i, i < n → (∫⁻ s in Set.Ioc ((v i) ^ 2) ((v (i + 1)) ^ 2),
      ENNReal.ofReal (s ^ ((p - 2) / 2)))
      = ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p) := by
    intro i hi
    have hq : (-1 : ℝ) < (p - 2) / 2 := by linarith
    have ha : (0:ℝ) ≤ (v i) ^ 2 := sq_nonneg _
    have hab : (v i) ^ 2 ≤ (v (i + 1)) ^ 2 := by
      exact pow_le_pow_left₀ (hvpos i) (hvmono (Nat.le_succ i)) 2
    rw [lintegral_Ioc_ofReal_rpow' ha hab hq]
    congr 1
    have h1 : ((v (i + 1)) ^ 2) ^ ((p - 2) / 2 + 1) = (v (i + 1)) ^ p := by
      rw [← Real.rpow_two, ← Real.rpow_mul (hvpos (i + 1))]
      ring_nf
    have h2 : ((v i) ^ 2) ^ ((p - 2) / 2 + 1) = (v i) ^ p := by
      rw [← Real.rpow_two, ← Real.rpow_mul (hvpos i)]
      ring_nf
    rw [h1, h2, show (p - 2) / 2 + 1 = p / 2 by ring]
    field_simp
  have hS1 := lintegral_Ioc_le_sum_mul (f := fun s : ℝ => min (innerTail μ W (Real.sqrt s)) M)
    (g := fun s : ℝ => ENNReal.ofReal (s ^ ((p - 2) / 2)))
    (by measurability) hanti (show Monotone (fun i : ℕ => (v i) ^ 2) from fun i j hij =>
      pow_le_pow_left₀ (hvpos i) (hvmono hij) 2) n
  rw [hv0] at hS1
  simp only [Nat.cast_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), hvn] at hS1
  have hS1' : ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) M
      ≤ ∑ i ∈ Finset.range n,
          ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p) * min (innerTail μ W (v i)) M := by
    refine hS1.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hcell0 i (Finset.mem_range.1 hi), Real.sqrt_sq_eq_abs, abs_of_nonneg (hvpos i)]
  have hpoint : ∀ i, i < n → ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
        * min (innerTail μ W (v i)) M
      ≤ ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p) * min (innerTail μ W (v (i + 1))) M
        + ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M) :=
    fun i hi => mul_le_mul_add_mul_tsub
  have hsplit : (∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
        * min (innerTail μ W (v i)) M)
      ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          * min (innerTail μ W (v (i + 1))) M)
        + ∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i hi => hpoint i (Finset.mem_range.1 hi)
  have hjump := sum_range_mul_tsub_le (f := fun u : ℝ => min (innerTail μ W u) M)
    (fun a b hab => min_le_min (innerTail_antitone μ W hab) le_rfl) hvmono n
    (G := fun i => ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p))
    (C := ENNReal.ofReal (2 * X ^ p / (p * n))) hG
  rw [hv0] at hjump
  have hfinal : ∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
        * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M)
      ≤ ENNReal.ofReal (2 * X ^ p / (p * n)) * M :=
    hjump.trans (mul_le_mul' le_rfl (min_le_right _ _))
  calc ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) M
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          * min (innerTail μ W (v i)) M := hS1'
    _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          * min (innerTail μ W (v (i + 1))) M)
        + ∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          * (min (innerTail μ W (v i)) M - min (innerTail μ W (v (i + 1))) M) := hsplit
    _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          * innerTail μ W (v (i + 1)))
        + ENNReal.ofReal (2 * X ^ p / (p * n)) * M := by
        refine add_le_add (Finset.sum_le_sum fun i hi => ?_) hfinal
        exact mul_le_mul' le_rfl (min_le_left _ _)

/-- The multiplicative identity used to remove the factor `p`. -/
lemma ofReal_mul_div_mul {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (T : ℝ≥0∞) :
    ENNReal.ofReal p * (ENNReal.ofReal (2 * a / p) * T) = 2 * (ENNReal.ofReal a * T) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hp
  rw [ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
  rw [← mul_assoc (ENNReal.ofReal p) (ENNReal.ofReal 2 * ENNReal.ofReal a / ENNReal.ofReal p) T,
    ENNReal.mul_div_cancel hp0 ENNReal.ofReal_ne_top, mul_assoc]

/-- The tail integral with the weight `s^((p-2)/2)` against `tail (√s)` is bounded by `4/p` times
the `p`-th power integral. -/
lemma sqrt_innerTail_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal p * ∫⁻ s in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)
      ≤ 4 * ∫⁻ x, (W x) ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  set A : ℝ≥0∞ := ∫⁻ x, (W x) ^ p ∂μ with hA
  have hmain : ∀ X : ℝ, 0 < X → ∀ m : ℕ,
      ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) (m : ℝ≥0∞)
        ≤ 4 * A := by
    intro X hX m
    have hstair : ∀ n : ℕ, ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) (m : ℝ≥0∞)
        ≤ 4 * A + ENNReal.ofReal (2 * X ^ p * (m : ℝ) / (n + 1)) := by
      intro n
      set v : ℕ → ℝ := fun i => X * (((i : ℝ) / ((n : ℝ) + 1)) ^ (1 / p)) with hv
      have hv0 : v 0 = 0 := by
        simp only [v, Nat.cast_zero, zero_div, Real.zero_rpow (ne_of_gt (one_div_pos.2 hp0)),
          mul_zero]
      have hvn : v (n + 1) = X := by
        simp only [v, Nat.cast_add, Nat.cast_one]
        rw [div_self (by positivity : ((n:ℝ) + 1) ≠ 0), Real.one_rpow, mul_one]
      have hvmono : Monotone v := by
        intro i j hij
        simp only [v]
        have h1 : ((i : ℝ) / ((n : ℝ) + 1)) ^ (1 / p) ≤ ((j : ℝ) / ((n : ℝ) + 1)) ^ (1 / p) := by
          have hi0 : (0:ℝ) ≤ (i : ℝ) / ((n : ℝ) + 1) := by positivity
          have hle : (i : ℝ) / ((n : ℝ) + 1) ≤ (j : ℝ) / ((n : ℝ) + 1) :=
            div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
          exact Real.rpow_le_rpow hi0 hle (le_of_lt (one_div_pos.2 hp0))
        exact mul_le_mul_of_nonneg_left h1 hX.le
      have hvpos : ∀ i, 0 ≤ v i := by
        intro i
        simp only [v]
        exact mul_nonneg hX.le (Real.rpow_nonneg (by positivity) _)
      have hpow : ∀ i : ℕ, (v i) ^ p = X ^ p * ((i : ℝ) / ((n : ℝ) + 1)) := by
        intro i
        simp only [v]
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
          one_div_mul_cancel (by linarith : p ≠ 0), Real.rpow_one]
      have hG : ∀ i, i < n + 1 → ENNReal.ofReal (2 * (v (i + 1) ^ p - v i ^ p) / p)
          ≤ ENNReal.ofReal (2 * X ^ p / (p * ((n + 1 : ℕ) : ℝ))) := by
        intro i hi
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        rw [hpow i, hpow (i + 1), ← mul_sub,
          show ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) - (i : ℝ) / ((n : ℝ) + 1)
            = 1 / ((n : ℝ) + 1) by rw [← sub_div]; norm_num, mul_one_div]
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
      have hst := sum_rpow_sqrt_min_le (μ := μ) (W := W) (p := p) (X := X) (M := (m : ℝ≥0∞))
        (v := v) hp hX (n + 1) (Nat.succ_pos n) hvmono hv0 hvn hvpos hG
      have hsum : (∑ i ∈ Finset.range (n + 1),
            ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * innerTail μ W (v (i + 1))) ≤ 2 * A := by
        have h := sum_range_rpow_sub_mul_innerTail_le (μ := μ) (W := W) (p := p) hp0
          hvmono hvpos (n + 1) (fun i hi => by
            simp only [v, Nat.cast_add, Nat.cast_one]
            exact mul_pos hX (Real.rpow_pos_of_pos (by positivity) _))
        simpa only [hA] using h
      -- multiply the staircase bound by `p`
      have hpst : ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
            ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) (m : ℝ≥0∞)
          ≤ 2 * (∑ i ∈ Finset.range (n + 1),
              ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * innerTail μ W (v (i + 1)))
            + ENNReal.ofReal p *
              (ENNReal.ofReal (2 * X ^ p / (p * ((n + 1 : ℕ) : ℝ))) * (m : ℝ≥0∞)) := by
        have hnn : ∀ i, i < n + 1 → (0:ℝ) ≤ v (i + 1) ^ p - v i ^ p := by
          intro i hi
          rw [hpow i, hpow (i + 1), ← mul_sub,
            show ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) - (i : ℝ) / ((n : ℝ) + 1)
              = 1 / ((n : ℝ) + 1) by rw [← sub_div]; norm_num, mul_one_div]
          positivity
        have h := mul_le_mul' (le_refl (ENNReal.ofReal p)) hst
        rw [mul_add, Finset.mul_sum] at h
        refine h.trans (le_of_eq ?_)
        rw [Finset.sum_congr rfl (fun i hi =>
          ofReal_mul_div_mul hp0 (hnn i (Finset.mem_range.1 hi)) _), ← Finset.mul_sum]
      have hfinal : ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
            ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) (m : ℝ≥0∞)
          ≤ 4 * A + ENNReal.ofReal (2 * X ^ p * (m : ℝ) / (n + 1)) := by
        refine hpst.trans ?_
        have h2 : ENNReal.ofReal p *
              (ENNReal.ofReal (2 * X ^ p / (p * ((n + 1 : ℕ) : ℝ))) * (m : ℝ≥0∞))
            = ENNReal.ofReal (2 * X ^ p * (m : ℝ) / (n + 1)) := by
          rw [show 2 * X ^ p / (p * ((n + 1 : ℕ) : ℝ)) = 2 * (X ^ p / ((n + 1 : ℕ) : ℝ)) / p by
            ring]
          rw [ofReal_mul_div_mul hp0 (by positivity : (0:ℝ) ≤ X ^ p / ((n + 1 : ℕ) : ℝ))
            (m : ℝ≥0∞)]
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
            show ENNReal.ofReal 2 * (ENNReal.ofReal (X ^ p / ((n + 1 : ℕ) : ℝ)) * (m : ℝ≥0∞))
              = ENNReal.ofReal 2 * ENNReal.ofReal (X ^ p / ((n + 1 : ℕ) : ℝ)) * (m : ℝ≥0∞) from by
              rw [mul_assoc],
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            show (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) from (ENNReal.ofReal_natCast m).symm,
            ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤
              2 * (X ^ p / ((n + 1 : ℕ) : ℝ)))]
          congr 1
          rw [Nat.cast_add, Nat.cast_one]
          ring
        rw [h2]
        refine add_le_add ?_ le_rfl
        calc 2 * (∑ i ∈ Finset.range (n + 1),
              ENNReal.ofReal (v (i + 1) ^ p - v i ^ p) * innerTail μ W (v (i + 1)))
            ≤ 2 * (2 * A) := mul_le_mul' le_rfl hsum
          _ = 4 * A := by rw [show (2:ℝ≥0∞) * (2 * A) = 4 * A by ring]
      simpa only [Nat.cast_add, Nat.cast_one] using hfinal
    exact le_of_forall_ofReal_div_add_le (c := 2 * X ^ p * (m : ℝ)) (by positivity) hstair
  have hM : ∀ X : ℝ, 0 < X → ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s) ≤ 4 * A := by
    intro X hX
    have hmeas1 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ ((p - 2) / 2)) :=
      Measurable.ennreal_ofReal (by measurability)
    have hmeas : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s) :=
      hmeas1.mul ((innerTail_measurable μ W).comp (by measurability))
    have hconv : (⨆ m : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) (m : ℝ≥0∞))
        = ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s) := by
      rw [← lintegral_iSup]
      · refine lintegral_congr fun s => ?_
        rw [← ENNReal.mul_iSup]
        congr 1
        exact iSup_min_natCast (innerTail μ W (Real.sqrt s))
      · exact fun m => hmeas1.mul (((innerTail_measurable μ W).comp (by measurability)).min
          measurable_const)
      · exact fun i j hij s => mul_le_mul' le_rfl (min_le_min le_rfl (by exact_mod_cast hij))
    calc ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
            ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)
        = ENNReal.ofReal p * ⨆ m : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
            ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) (m : ℝ≥0∞) := by
          rw [hconv]
      _ = ⨆ m : ℕ, ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) (X ^ 2),
            ENNReal.ofReal (s ^ ((p - 2) / 2)) * min (innerTail μ W (Real.sqrt s)) (m : ℝ≥0∞) :=
          ENNReal.mul_iSup _ _
      _ ≤ 4 * A := iSup_le fun m => hmain X hX m
  have hX' : (⨆ X : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) ((X:ℝ) ^ 2),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s))
      = ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s) := by
    have hmeas1 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ ((p - 2) / 2)) :=
      Measurable.ennreal_ofReal (by measurability)
    have hmeas : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s) :=
      hmeas1.mul ((innerTail_measurable μ W).comp (by measurability))
    have h1 : ∀ X : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) ((X:ℝ) ^ 2),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)
        = ∫⁻ s, Set.indicator (Set.Ioc (0 : ℝ) ((X:ℝ) ^ 2))
            (fun s => ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)) s ∂volume :=
      fun X => (lintegral_indicator measurableSet_Ioc _).symm
    have h2 : ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)
        = ∫⁻ s, Set.indicator (Set.Ioi (0 : ℝ))
            (fun s => ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)) s ∂volume :=
      (lintegral_indicator measurableSet_Ioi _).symm
    rw [h2]
    simp only [h1]
    rw [← lintegral_iSup]
    · refine lintegral_congr fun s => ?_
      refine le_antisymm (iSup_le fun X => ?_) ?_
      · show Set.indicator (Set.Ioc (0:ℝ) ((X:ℝ) ^ 2))
            (fun s => ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)) s
          ≤ Set.indicator (Set.Ioi (0 : ℝ))
            (fun s => ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)) s
        by_cases h : s ∈ Set.Ioc (0 : ℝ) ((X:ℝ) ^ 2)
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_Ioi.2 h.1)]
        · rw [Set.indicator_of_notMem h]; exact bot_le
      · show Set.indicator (Set.Ioi (0 : ℝ))
            (fun s => ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)) s
          ≤ ⨆ X : ℕ, Set.indicator (Set.Ioc (0:ℝ) ((X:ℝ) ^ 2))
            (fun s => ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)) s
        by_cases h : s ∈ Set.Ioi (0:ℝ)
        · obtain ⟨X, hX⟩ := exists_nat_gt (Real.sqrt s)
          refine le_iSup_of_le X ?_
          rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show s ∈ Set.Ioc (0:ℝ) ((X:ℝ) ^ 2) from
              ⟨h, by rw [← Real.sq_sqrt h.le]; exact pow_le_pow_left₀ (Real.sqrt_nonneg s) hX.le 2⟩)]
        · rw [Set.indicator_of_notMem h]; exact bot_le
    · exact fun X => hmeas.indicator measurableSet_Ioc
    · intro i j hij s
      show Set.indicator (Set.Ioc (0:ℝ) ((i:ℝ) ^ 2)) _ s
        ≤ Set.indicator (Set.Ioc (0:ℝ) ((j:ℝ) ^ 2)) _ s
      by_cases h : s ∈ Set.Ioc (0 : ℝ) ((i:ℝ) ^ 2)
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show s ∈ Set.Ioc (0:ℝ) ((j:ℝ) ^ 2) from
            ⟨h.1, le_trans h.2 (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hij) 2)⟩)]
      · rw [Set.indicator_of_notMem h]; exact bot_le
  calc ENNReal.ofReal p * ∫⁻ s in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s)
      = ENNReal.ofReal p * ⨆ X : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) ((X:ℝ) ^ 2),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s) := by rw [hX']
    _ = ⨆ X : ℕ, ENNReal.ofReal p * ∫⁻ s in Set.Ioc (0 : ℝ) ((X:ℝ) ^ 2),
          ENNReal.ofReal (s ^ ((p - 2) / 2)) * innerTail μ W (Real.sqrt s) := ENNReal.mul_iSup _ _
    _ ≤ 4 * A := iSup_le fun X => by
        rcases Nat.eq_zero_or_pos X with h | h
        · subst h
          simp
        · exact hM X (by exact_mod_cast h)

/-- The low truncation at level `a` is bounded by the tail integral of `tail (√s)` over
`(0,a²)`. -/
lemma lintegral_indicator_low_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ≥0∞} {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, Set.indicator {x : α | W x ≤ ENNReal.ofReal a} (fun x => (W x) ^ 2) x ∂μ
      ≤ ∫⁻ s in Set.Ioc (0 : ℝ) (a ^ 2), innerTail μ W (Real.sqrt s) := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral (μ := μ)
    (f := fun x => Set.indicator {x : α | W x ≤ ENNReal.ofReal a} (fun x => (W x) ^ 2) x)]
  refine iSup_le fun H => iSup_le fun hH => iSup_le fun hle => ?_
  have hH2 : ∀ x, H x ≤ (W x) ^ 2 := fun x => (hle x).trans (Set.indicator_le_self _ _ x)
  have hWle : ∀ x, 0 < H x → W x ≤ ENNReal.ofReal a := by
    intro x hx
    by_contra hcon
    have hmem : x ∉ {x : α | W x ≤ ENNReal.ofReal a} := hcon
    have hx' := hle x
    simp only [Set.indicator_of_notMem hmem] at hx'
    exact absurd (le_antisymm hx' bot_le) hx.ne'
  have hHtop : ∀ x, H x ≤ ENNReal.ofReal (a ^ 2) := by
    intro x
    by_cases hx : H x = 0
    · rw [hx]; exact bot_le
    · refine (hH2 x).trans ?_
      rw [ENNReal.ofReal_pow ha.le]
      exact pow_le_pow_left' (hWle x (pos_iff_ne_zero.2 hx)) 2
  have hfin : ∀ x, H x ≠ ∞ := fun x => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hHtop x)
  have hcongr : (fun x => H x) = fun x => ENNReal.ofReal ((H x).toReal) := by
    funext x; exact (ENNReal.ofReal_toReal (hfin x)).symm
  set g : ℝ → ℝ≥0∞ := fun s => μ {x | s < (H x).toReal} with hg
  have hgmeas : Measurable g := by
    rw [hg]
    exact Antitone.measurable (fun s t hst => measure_mono (fun x hx => lt_of_le_of_lt hst hx))
  rw [hcongr, lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall fun x => ENNReal.toReal_nonneg)
    (hH.ennreal_toReal.aemeasurable)]
  have hgoal : ∫⁻ t in Set.Ioi (0 : ℝ), g t
      = ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | t < (H x).toReal} := by
    rw [hg]
  rw [← hgoal]
  have hzero : ∫⁻ t in Set.Ioi (a ^ 2), g t = 0 := by
    rw [← lintegral_indicator measurableSet_Ioi,
      lintegral_eq_zero_iff (hgmeas.indicator measurableSet_Ioi)]
    filter_upwards with t
    show (Set.Ioi (a ^ 2)).indicator g t = 0
    by_cases ht : t ∈ Set.Ioi (a ^ 2)
    · have hset : {x | t < (H x).toReal} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
        have h2 : (H x).toReal ≤ a ^ 2 := by
          have h2' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hHtop x)
          rwa [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ a ^ 2)] at h2'
        exact absurd (lt_of_lt_of_le hx h2) (not_lt.2 (le_of_lt ht))
      rw [Set.indicator_of_mem ht, hg]
      show μ {x | t < (H x).toReal} = 0
      rw [hset, measure_empty]
    · rw [Set.indicator_of_notMem ht]

  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) (a ^ 2) ∪ Set.Ioi (a ^ 2) :=
    (Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0:ℝ) ≤ a ^ 2)).symm
  rw [hsplit, lintegral_union measurableSet_Ioi, hzero, add_zero]
  · refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    refine le_innerTail (measurableSet_lt measurable_const hH.ennreal_toReal) ?_
    intro x hx
    have hs0 : 0 < s := hs.1
    rcases eq_or_ne (W x) ∞ with hWtop | hWtop
    · simpa [hWtop] using (ENNReal.ofReal_lt_top : ENNReal.ofReal (Real.sqrt s) < ∞)
    · have h1 : s < ((W x).toReal) ^ 2 := by
        have h2 : (H x).toReal ≤ ((W x).toReal) ^ 2 := by
          have h2' := ENNReal.toReal_mono (ENNReal.pow_ne_top hWtop) (hH2 x)
          rwa [show ((W x) ^ 2).toReal = ((W x).toReal) ^ 2 from ENNReal.toReal_pow _ _] at h2'
        exact lt_of_lt_of_le hx h2
      have hWpos : 0 < (W x).toReal := by
        by_contra hcon
        have hz : (W x).toReal = 0 := le_antisymm (not_lt.1 hcon) ENNReal.toReal_nonneg
        rw [hz] at h1
        norm_num at h1
        exact absurd h1 (not_lt.2 hs0.le)
      have h3 : Real.sqrt s < (W x).toReal := (Real.sqrt_lt' hWpos).2 h1
      have h4 : ENNReal.ofReal (Real.sqrt s) < ENNReal.ofReal ((W x).toReal) :=
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg s) |>.2 h3
      rwa [ENNReal.ofReal_toReal hWtop] at h4
  · rw [Set.disjoint_left]
    intro u hu1 hu2
    exact absurd (lt_of_le_of_lt hu1.2 hu2) (lt_irrefl u)

/-- The pointwise identity relating an indicator and a product. -/
lemma indicator_one_mul {α : Type*} {s : Set α} (f : α → ℝ≥0∞) (a : α) :
    Set.indicator s (fun _ => (1 : ℝ≥0∞)) a * f a = Set.indicator s f a := by
  by_cases h : a ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- Swapping the two integrals when the inner `s`-integral is taken over `(c t/2, ∞)`. -/
lemma lintegral_Ioi_mul_Ioi_half {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Set.Ioi (0 : ℝ), f t * (∫⁻ s in Set.Ioi (c * t / 2), g s)
      = ∫⁻ s in Set.Ioi (0 : ℝ), g s * (∫⁻ t in Set.Ioo (0 : ℝ) (2 * s / c), f t) := by
  -- (i) rewrite the inner integral using an indicator
  have hA : ∫⁻ t in Set.Ioi (0 : ℝ), f t * (∫⁻ s in Set.Ioi (c * t / 2), g s)
      = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ s in Set.Ioi (0 : ℝ),
          f t * (g s * Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1 : ℝ≥0∞)) s) := by
    refine lintegral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [show (∫⁻ s in Set.Ioi (c * t / 2), g s)
        = ∫⁻ s, Set.indicator (Set.Ioi (c * t / 2)) g s from
      (lintegral_indicator measurableSet_Ioi g).symm]
    rw [← lintegral_const_mul'' (f t) (hg.indicator measurableSet_Ioi).aemeasurable]
    rw [← lintegral_indicator measurableSet_Ioi
      (fun s => f t * (g s * Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1:ℝ≥0∞)) s))]
    refine lintegral_congr fun s => ?_
    by_cases h2 : s ∈ Set.Ioi (c * t / 2)
    · rw [Set.indicator_of_mem h2 g,
        Set.indicator_of_mem (Set.mem_Ioi.2 (lt_trans
          (div_pos (mul_pos hc (Set.mem_Ioi.1 ht)) (by norm_num)) h2))
          (fun s => f t * (g s * Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1:ℝ≥0∞)) s)),
        Set.indicator_of_mem h2 (fun _ => (1:ℝ≥0∞)), mul_one]
    · rw [Set.indicator_of_notMem h2 g, mul_zero]
      by_cases h3 : s ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem h3
            (fun s => f t * (g s * Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1:ℝ≥0∞)) s)),
          Set.indicator_of_notMem h2 (fun _ => (1:ℝ≥0∞)), mul_zero, mul_zero]
      · rw [Set.indicator_of_notMem h3
            (fun s => f t * (g s * Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1:ℝ≥0∞)) s))]
  rw [hA]
  -- (ii) Tonelli
  have hmeasure : AEMeasurable (Function.uncurry fun t s : ℝ =>
        f t * (g s * Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1 : ℝ≥0∞)) s))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    refine AEMeasurable.mul ?_ ?_
    · exact (hf.comp measurable_fst).aemeasurable
    · refine AEMeasurable.mul ?_ ?_
      · exact (hg.comp measurable_snd).aemeasurable
      · refine Measurable.aemeasurable ?_
        refine Measurable.indicator measurable_const ?_
        exact measurableSet_lt ((measurable_fst.const_mul c).div_const 2) measurable_snd
  rw [lintegral_lintegral_swap hmeasure]
  -- (iii) evaluate the inner `t`-integral
  refine lintegral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hset : ∀ t : ℝ, 0 < t →
      Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1 : ℝ≥0∞)) s
        = Set.indicator (Set.Ioo (0 : ℝ) (2 * s / c)) (fun _ => (1 : ℝ≥0∞)) t := by
    intro t ht
    simp only [Set.indicator_apply]
    by_cases h2 : c * t / 2 < s
    · rw [if_pos (Set.mem_Ioi.2 h2), if_pos (show t ∈ Set.Ioo (0:ℝ) (2*s/c) from
        ⟨ht, by rw [lt_div_iff₀ hc]; nlinarith [h2]⟩)]
    · rw [if_neg (fun h => h2 (Set.mem_Ioi.1 h)),
        if_neg (show ¬(t ∈ Set.Ioo (0:ℝ) (2*s/c)) from fun h => h2 (by
          have h3 : t < 2 * s / c := h.2
          rw [lt_div_iff₀ hc] at h3
          nlinarith [h3]))]
  have hcongr : (fun t : ℝ => f t *
        (g s * Set.indicator (Set.Ioi (c * t / 2)) (fun _ => (1:ℝ≥0∞)) s))
      =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      fun t : ℝ => g s * (f t * Set.indicator (Set.Ioo (0:ℝ) (2*s/c)) (fun _ => (1:ℝ≥0∞)) t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [hset t ht]; ring
  rw [lintegral_congr_ae hcongr]
  rw [lintegral_const_mul'' (g s)
    (f := fun a => f a * Set.indicator (Set.Ioo (0:ℝ) (2 * s / c)) (fun _ => (1:ℝ≥0∞)) a)
    (hf.mul ((measurable_const (a := (1:ℝ≥0∞))).indicator
      (measurableSet_Ioo : MeasurableSet (Set.Ioo (0:ℝ) (2 * s / c))))).aemeasurable]
  congr 1
  trans ∫⁻ a in Set.Ioi (0:ℝ), Set.indicator (Set.Ioo (0:ℝ) (2*s/c)) f a
  · refine lintegral_congr fun a => ?_
    rw [mul_comm (f a) (Set.indicator (Set.Ioo (0:ℝ) (2*s/c)) (fun _ => (1:ℝ≥0∞)) a)]
    exact indicator_one_mul f a
  · rw [← lintegral_indicator measurableSet_Ioi (Set.indicator (Set.Ioo (0:ℝ) (2*s/c)) f),
        ← lintegral_indicator measurableSet_Ioo f]
    refine lintegral_congr fun a => ?_
    by_cases hI : a ∈ Set.Ioo (0:ℝ) (2*s/c)
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hI.1)]
    · rw [Set.indicator_of_notMem hI]
      by_cases h2 : a ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem hI]
      · rw [Set.indicator_of_notMem h2]

/-- `Ioo 0 X` and `Ioc 0 X` agree almost everywhere. -/
lemma Ioo_ae_Ioc (X : ℝ) : Set.Ioo (0:ℝ) X =ᵐ[volume] Set.Ioc (0:ℝ) X := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun t ht => ?_) measure_empty
    obtain ⟨h1, h2⟩ := ht
    simp only [Set.mem_Ioo] at h1
    simp only [Set.mem_Ioc, not_and] at h2
    exact h2 h1.1 h1.2.le
  · refine measure_mono_null (fun t ht => ?_) (by simp : volume ({X} : Set ℝ) = 0)
    obtain ⟨h1, h2⟩ := ht
    simp only [Set.mem_Ioc] at h1
    simp only [Set.mem_Ioo, not_and] at h2
    simp only [Set.mem_singleton_iff]
    exact le_antisymm h1.2 (le_of_not_gt (h2 h1.1))

/-! ## Measurability of `x ↦ x ^ q` and auxiliary pointwise identities -/

/-- The map `x ↦ x ^ q` is measurable for every real exponent `q`. -/
lemma measurable_rpow_const (q : ℝ) : Measurable (fun x : ℝ => x ^ q) := by
  have hA : Measurable (fun x : ℝ => Real.exp (Real.log x * q)) :=
    Real.measurable_exp.comp (Real.measurable_log.mul_const q)
  have hg : Measurable (fun x : ℝ =>
      if 0 < x then Real.exp (Real.log x * q)
      else if x = 0 then (if q = 0 then (1:ℝ) else 0)
      else Real.exp (Real.log x * q) * Real.cos (q * Real.pi)) := by
    refine Measurable.ite measurableSet_Ioi hA ?_
    refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    exact hA.mul measurable_const
  have hEq : (fun x : ℝ => x ^ q) = (fun x : ℝ =>
      if 0 < x then Real.exp (Real.log x * q)
      else if x = 0 then (if q = 0 then (1:ℝ) else 0)
      else Real.exp (Real.log x * q) * Real.cos (q * Real.pi)) := by
    funext x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [if_neg (not_lt.2 hx.le), if_neg hx.ne, Real.rpow_def_of_neg hx]
    · subst hx
      rw [if_neg (lt_irrefl 0), if_pos rfl]
      by_cases hq : q = 0
      · subst hq; simp
      · rw [if_neg hq, Real.zero_rpow hq]
    · rw [if_pos hx, Real.rpow_def_of_pos hx]
  rw [hEq]
  exact hg

/-- The `enorm` of a `ℂ`-valued function multiplied by an indicator. -/
lemma enorm_indicator_one {α : Type*} (s : Set α) (x : α) :
    ‖Set.indicator s (fun _ => (1:ℂ)) x‖ₑ = Set.indicator s (fun _ => (1:ℝ≥0∞)) x := by
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

/-- Squaring a truncated `enorm`. -/
lemma trunc_sq {α : Type*} (W : α → ℝ≥0∞) (s : Set α) (x : α) :
    (W x * Set.indicator s (fun _ => (1:ℝ≥0∞)) x) ^ (2:ℝ)
      = Set.indicator s (fun x => (W x) ^ 2) x := by
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    norm_num
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]

/-- `x ^ 2` for the real power on `ℝ≥0∞`. -/
lemma rpow_two_eq (x : ℝ≥0∞) : x ^ (2:ℝ) = x ^ 2 := ENNReal.rpow_natCast x 2

/-- The second power of a nonnegative real, inside `ofReal`. -/
lemma ofReal_sq (a : ℝ) (ha : 0 ≤ a) : (ENNReal.ofReal a) ^ (2:ℝ) = ENNReal.ofReal (a^2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg ha (by norm_num)]
  congr 1
  norm_num

/-- The integral over `Ioi 0` of `s.indicator f` equals the integral of `f` over `s`. -/
lemma lintegral_Ioi_indicator_eq {f : ℝ → ℝ≥0∞} {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioi (0:ℝ)) :
    ∫⁻ a in Set.Ioi (0:ℝ), Set.indicator s f a = ∫⁻ a in s, f a := by
  rw [← lintegral_indicator measurableSet_Ioi (Set.indicator s f), ← lintegral_indicator hs f]
  refine lintegral_congr fun a => ?_
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem (hsub ha)]
  · rw [Set.indicator_of_notMem ha]
    by_cases h2 : a ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem ha]
    · rw [Set.indicator_of_notMem h2]

/-- The power integral over `Ioo 0 X`. -/
lemma lintegral_Ioo_ofReal_rpow {X q : ℝ} (hq : -1 < q) (hX : 0 ≤ X) :
    ∫⁻ s in Set.Ioo (0:ℝ) X, ENNReal.ofReal (s ^ q) = ENNReal.ofReal (X ^ (q+1) / (q+1)) := by
  rw [Measure.restrict_congr_set (Ioo_ae_Ioc X)]
  exact lintegral_Ioc_ofReal_rpow hq hX

/-- Swapping the two integrals when the inner `s`-integral is taken over `(0, (c t)^2)`. -/
lemma lintegral_Ioi_mul_Ioc_sq {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Set.Ioi (0:ℝ), f t * (∫⁻ s in Set.Ioc (0:ℝ) ((c*t)^2), g s)
      = ∫⁻ s in Set.Ioi (0:ℝ), g s * (∫⁻ t in Set.Ioi (Real.sqrt s / c), f t) := by
  have hIoo : ∀ X : ℝ, ∫⁻ s in Set.Ioc (0:ℝ) X, g s = ∫⁻ s in Set.Ioo (0:ℝ) X, g s := by
    intro X
    rw [← Measure.restrict_congr_set (μ := volume) (Ioo_ae_Ioc X)]
  simp_rw [hIoo]
  have hA : ∫⁻ t in Set.Ioi (0:ℝ), f t * (∫⁻ s in Set.Ioo (0:ℝ) ((c*t)^2), g s)
      = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ s in Set.Ioi (0:ℝ),
          f t * Set.indicator (Set.Ioo (0:ℝ) ((c*t)^2)) g s := by
    refine lintegral_congr fun t => ?_
    have h1 : (∫⁻ s in Set.Ioo (0:ℝ) ((c*t)^2), g s)
        = ∫⁻ s in Set.Ioi (0:ℝ), Set.indicator (Set.Ioo (0:ℝ) ((c*t)^2)) g s := by
      rw [(lintegral_Ioi_indicator_eq measurableSet_Ioo (fun x hx => hx.1) (f := g)).symm]
    rw [h1, ← lintegral_const_mul'' (f t)
      (f := fun s => Set.indicator (Set.Ioo (0:ℝ) ((c*t)^2)) g s)
      ((hg.indicator measurableSet_Ioo).aemeasurable)]
  rw [hA]
  have hmeasure : AEMeasurable (Function.uncurry fun t s : ℝ =>
        f t * Set.indicator (Set.Ioo (0:ℝ) ((c*t)^2)) g s)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    refine AEMeasurable.mul ?_ ?_
    · exact (hf.comp measurable_fst).aemeasurable
    · refine Measurable.aemeasurable ?_
      refine Measurable.indicator (hg.comp measurable_snd) ?_
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd ((measurable_fst.const_mul c).pow_const 2))
  rw [lintegral_lintegral_swap hmeasure]
  refine lintegral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hsub : (0:ℝ) < Real.sqrt s / c := div_pos (Real.sqrt_pos.2 hs) hc
  have hiff : ∀ t : ℝ, 0 < t → (s ∈ Set.Ioo (0:ℝ) ((c*t)^2) ↔ t ∈ Set.Ioi (Real.sqrt s / c)) := by
    intro t ht
    rw [Set.mem_Ioo, Set.mem_Ioi]
    constructor
    · intro h2
      have h3 : Real.sqrt s < c * t := (Real.sqrt_lt' (mul_pos hc ht)).2 h2.2
      rw [div_lt_iff₀ hc]
      linarith [h3]
    · intro h2
      refine ⟨hs, ?_⟩
      have h3 : Real.sqrt s < c * t := by
        rw [div_lt_iff₀ hc] at h2
        linarith [h2]
      exact (Real.sqrt_lt' (mul_pos hc ht)).1 h3
  have hset : ∀ t : ℝ, 0 < t →
      Set.indicator (Set.Ioo (0:ℝ) ((c*t)^2)) g s
        = Set.indicator (Set.Ioi (Real.sqrt s / c)) (fun _ => (1 : ℝ≥0∞)) t * g s := by
    intro t ht
    by_cases h2 : s ∈ Set.Ioo (0:ℝ) ((c*t)^2)
    · rw [Set.indicator_of_mem h2, Set.indicator_of_mem ((hiff t ht).1 h2), one_mul]
    · rw [Set.indicator_of_notMem h2,
        Set.indicator_of_notMem (fun h => h2 ((hiff t ht).2 h)), zero_mul]
  have hcongr : (fun t : ℝ => f t * Set.indicator (Set.Ioo (0:ℝ) ((c*t)^2)) g s)
      =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      fun t : ℝ => g s * (f t * Set.indicator (Set.Ioi (Real.sqrt s / c)) (fun _ => (1:ℝ≥0∞)) t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [hset t ht]; ring
  rw [lintegral_congr_ae hcongr]
  rw [lintegral_const_mul'' (g s)
    (f := fun a => f a * Set.indicator (Set.Ioi (Real.sqrt s / c)) (fun _ => (1:ℝ≥0∞)) a)
    (hf.mul ((measurable_const (a := (1:ℝ≥0∞))).indicator measurableSet_Ioi)).aemeasurable]
  congr 1
  trans ∫⁻ a in Set.Ioi (0:ℝ), Set.indicator (Set.Ioi (Real.sqrt s / c)) f a
  · refine lintegral_congr fun a => ?_
    rw [mul_comm (f a) (Set.indicator (Set.Ioi (Real.sqrt s / c)) (fun _ => (1:ℝ≥0∞)) a)]
    exact indicator_one_mul f a
  · exact lintegral_Ioi_indicator_eq measurableSet_Ioi (fun x hx => lt_trans hsub (Set.mem_Ioi.1 hx))

/-- Specialisation of the swap to `c = 1`, half line. -/
lemma lintegral_Ioi_mul_Ioi_half_one {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ t in Set.Ioi (0:ℝ), f t * (∫⁻ s in Set.Ioi (t/2), g s)
      = ∫⁻ s in Set.Ioi (0:ℝ), g s * (∫⁻ t in Set.Ioo (0:ℝ) (2*s), f t) := by
  simpa only [one_mul, div_one] using lintegral_Ioi_mul_Ioi_half hf hg (c := 1) (by norm_num)

/-- Specialisation of the swap to `c = 1`, squares. -/
lemma lintegral_Ioi_mul_Ioc_sq_one {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ t in Set.Ioi (0:ℝ), f t * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), g s)
      = ∫⁻ s in Set.Ioi (0:ℝ), g s * (∫⁻ t in Set.Ioi (Real.sqrt s), f t) := by
  simpa only [one_mul, div_one] using lintegral_Ioi_mul_Ioc_sq hf hg (c := 1) (by norm_num)

/-- Splitting a function into the part where `‖f‖ₑ > ofReal t` and its complement. -/
lemma mul_indicator_add_compl {α : Type*} {s : Set α} (f : α → ℂ) :
    (fun x => f x * Set.indicator s (fun _ => (1:ℂ)) x)
      + (fun x => f x * Set.indicator sᶜ (fun _ => (1:ℂ)) x) = f := by
  funext x
  rw [Pi.add_apply]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx),
      mul_one, mul_zero, add_zero]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx),
      mul_zero, mul_one, zero_add]

/-- The tail set at level `t` is contained in the union of the tails of the truncations. -/
lemma tail_subset {α : Type*} {β : Type*} [MeasurableSpace β] (T : (α → ℂ) → (β → ℂ))
    (hadd : ∀ f g : α → ℂ, T (f + g) = T f + T g) (t : ℝ) (ht : 0 < t)
    (f g h : α → ℂ) (hsum : g + h = f) :
    {a : β | t < ‖T f a‖} ⊆ {a : β | t/2 < ‖T g a‖} ∪ {a : β | t/2 < ‖T h a‖} := by
  intro a ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  rcases le_or_gt (‖T g a‖) (t/2) with h1 | h1
  · right
    change t / 2 < ‖T h a‖
    by_contra hcon
    push_neg at hcon
    have h3 : ‖T f a‖ ≤ t := by
      calc ‖T f a‖ = ‖T (g + h) a‖ := by rw [← congrArg T hsum]
        _ = ‖(T g + T h) a‖ := by rw [hadd g h]
        _ ≤ ‖T g a‖ + ‖T h a‖ := norm_add_le _ _
        _ ≤ t / 2 + t / 2 := add_le_add h1 hcon
        _ = t := by ring
    linarith
  · left
    exact h1

/-! ## Pointwise bounds for the two truncations -/

/-- The weak-type bound for the high truncation, at level `t/2`, multiplied by `t^(p-1)`. -/
lemma high_pointwise {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {A0 : ℝ} (hA0 : 0 < A0) {p : ℝ} (hp1 : 1 < p)
    {T : (α → ℂ) → (β → ℂ)} {f : α → ℂ} (hfm : AEStronglyMeasurable f μ)
    (hweak : ∀ (g : α → ℂ) (lam : ℝ), 0 < lam →
      ν {x : β | lam < ‖T g x‖} ≤ ENNReal.ofReal (A0 / lam) * eLpNorm g 1 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      ν {a : β | t / 2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℂ)) x) a‖}
      ≤ ENNReal.ofReal (6 * A0 * t ^ (p - 2)) *
          (∫⁻ s in Set.Ioi (t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := by
  set g : α → ℂ := fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℂ)) x with hg
  have h1 : ν {a : β | t / 2 < ‖T g a‖} ≤ ENNReal.ofReal (A0 / (t/2)) * eLpNorm g 1 μ :=
    hweak g (t/2) (by positivity)
  have h2 : eLpNorm g 1 μ
      = ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
    have hF : Measurable (fun z : ℂ =>
        z * Set.indicator {z : ℂ | ENNReal.ofReal t < ‖z‖ₑ} (fun _ => (1:ℂ)) z) :=
      measurable_id.mul (measurable_const.indicator (measurableSet_lt measurable_const measurable_enorm))
    have hgm : AEStronglyMeasurable g μ := (hF.comp_aemeasurable hfm.aemeasurable).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hgm]
    refine lintegral_congr fun x => ?_
    have h3 : ‖g x‖ₑ
        = ‖f x‖ₑ * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℝ≥0∞)) x := by
      show ‖f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℂ)) x‖ₑ = _
      rw [enorm_mul, enorm_indicator_one]
    rw [h3, mul_comm (‖f x‖ₑ) (Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℝ≥0∞)) x)]
    exact indicator_one_mul (fun x => ‖f x‖ₑ) x
  have h4 : (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ)
      ≤ 3 * ∫⁻ s in Set.Ioi (t / 2), innerTail μ (fun x => ‖f x‖ₑ) s :=
    lintegral_indicator_high_le (fun x => enorm_ne_top) ht
  have hreal : t ^ (p - 1) * (A0 / (t / 2)) = 2 * A0 * t ^ (p - 2) := by
    have htp1 : t ^ (p-1) = t ^ (p-2) * t := by
      nth_rewrite 3 [← Real.rpow_one t]
      rw [← Real.rpow_add ht (p-2) 1, show p - 2 + 1 = p - 1 by ring]
    rw [htp1]
    have hstep : t * (A0 / (t/2)) = 2 * A0 := by field_simp
    calc t ^ (p-2) * t * (A0 / (t / 2)) = t ^ (p-2) * (t * (A0 / (t / 2))) := by ring
      _ = t ^ (p-2) * (2 * A0) := by rw [hstep]
      _ = 2 * A0 * t ^ (p - 2) := by ring
  have h5 : ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (A0 / (t / 2))
      = ENNReal.ofReal (2 * A0 * t ^ (p - 2)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (p-1)), hreal]
  have h6 : ENNReal.ofReal (2 * A0 * t ^ (p - 2)) * 3 = ENNReal.ofReal (6 * A0 * t ^ (p - 2)) := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (t ^ (p - 1)) * ν {a : β | t / 2 < ‖T g a‖}
      ≤ ENNReal.ofReal (t ^ (p - 1)) *
          (ENNReal.ofReal (A0 / (t/2)) * eLpNorm g 1 μ) := mul_le_mul_right h1 _
    _ = ENNReal.ofReal (t ^ (p - 1)) *
          (ENNReal.ofReal (A0 / (t/2)) *
            ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ) := by
        rw [h2]
    _ = (ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (A0 / (t/2))) *
            ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (2 * A0 * t ^ (p - 2)) *
            ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
        rw [h5]
    _ ≤ ENNReal.ofReal (2 * A0 * t ^ (p - 2)) *
          (3 * ∫⁻ s in Set.Ioi (t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := mul_le_mul_right h4 _
    _ = ENNReal.ofReal (6 * A0 * t ^ (p - 2)) *
          (∫⁻ s in Set.Ioi (t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := by
        rw [← mul_assoc, h6]

/-- The strong-type bound for the low truncation, at level `t/2`, multiplied by `t^(p-1)`. -/
lemma low_pointwise {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {A1 : ℝ} (hA1 : 0 < A1) {p : ℝ} (hp1 : 1 < p)
    {T : (α → ℂ) → (β → ℂ)} {f : α → ℂ} (hfm : AEStronglyMeasurable f μ)
    (hmeas : ∀ g : α → ℂ, AEMeasurable (T g) ν)
    (hstrong : ∀ g : α → ℂ, eLpNorm (T g) 2 ν ≤ ENNReal.ofReal A1 * eLpNorm g 2 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      ν {a : β | t / 2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℂ)) x) a‖}
      ≤ ENNReal.ofReal (4 * A1 ^ 2 * t ^ (p - 3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t ^ 2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
  set h : α → ℂ := fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℂ)) x with hh
  have h2t : (2:ℝ≥0∞).toReal = (2:ℝ) := by norm_num
  have hcheb := mul_meas_ge_le_pow_eLpNorm' (p := (2:ℝ≥0∞)) ν (by norm_num) (by norm_num)
      (f := T h) (ENNReal.ofReal (t/2))
  simp_rw [h2t] at hcheb
  have hmono : ν {a : β | t / 2 < ‖T h a‖} ≤ ν {a : β | ENNReal.ofReal (t/2) ≤ ‖T h a‖ₑ} := by
    refine measure_mono fun a ha => ?_
    rw [Set.mem_setOf_eq] at ha ⊢
    rw [← ofReal_norm (T h a)]
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 ha)
  have heLph : (eLpNorm h 2 μ) ^ (2:ℝ) = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by
    have hF : Measurable (fun z : ℂ =>
        z * Set.indicator {z : ℂ | ENNReal.ofReal t < ‖z‖ₑ}ᶜ (fun _ => (1:ℂ)) z) :=
      measurable_id.mul (measurable_const.indicator
        (measurableSet_lt measurable_const measurable_enorm).compl)
    have hhm : AEStronglyMeasurable h μ := (hF.comp_aemeasurable hfm.aemeasurable).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hhm]
    simp_rw [h2t]
    rw [← ENNReal.rpow_mul, show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hL : (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)
      = ∫⁻ x, Set.indicator {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal t} (fun x => ‖f x‖ₑ ^ 2) x ∂μ := by
    refine lintegral_congr fun x => ?_
    have hset : {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ = {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal t} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have h1 : ‖h x‖ₑ
        = ‖f x‖ₑ * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℝ≥0∞)) x := by
      show ‖f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℂ)) x‖ₑ = _
      rw [enorm_mul, enorm_indicator_one]
    rw [h1, hset]
    exact trunc_sq (fun x => ‖f x‖ₑ) _ x
  have hlow := lintegral_indicator_low_le (μ := μ) (W := fun x => ‖f x‖ₑ) ht
  have hsquare : ENNReal.ofReal (t/2) ^ (2:ℝ) = ENNReal.ofReal ((t/2)^2) := by
    rw [rpow_two_eq, ← ENNReal.ofReal_pow (by positivity)]
  have hne0 : ENNReal.ofReal ((t/2)^2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hnetop : ENNReal.ofReal ((t/2)^2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hcheb' : ENNReal.ofReal ((t/2)^2) * ν {a : β | ENNReal.ofReal (t/2) ≤ ‖T h a‖ₑ}
      ≤ eLpNorm (T h) 2 ν ^ (2:ℝ) := by
    rw [← hsquare]; exact hcheb
  have hstrong' : (eLpNorm (T h) 2 ν) ^ (2:ℝ)
      ≤ ENNReal.ofReal (A1^2) * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by
    calc (eLpNorm (T h) 2 ν) ^ (2:ℝ) ≤ (ENNReal.ofReal A1 * eLpNorm h 2 μ) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (hstrong h) (by norm_num)
      _ = (ENNReal.ofReal A1) ^ (2:ℝ) * (eLpNorm h 2 μ) ^ (2:ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by rw [heLph, ofReal_sq A1 hA1.le]
  have hmain : ν {a : β | t / 2 < ‖T h a‖}
      ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
          (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by
    have hkey : ENNReal.ofReal ((t/2)^2) * ν {a : β | t / 2 < ‖T h a‖}
        ≤ ENNReal.ofReal ((t/2)^2) *
            ((ENNReal.ofReal ((t/2)^2))⁻¹ *
              (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := by
      calc ENNReal.ofReal ((t/2)^2) * ν {a : β | t / 2 < ‖T h a‖}
          ≤ ENNReal.ofReal ((t/2)^2) * ν {a : β | ENNReal.ofReal (t/2) ≤ ‖T h a‖ₑ} :=
            mul_le_mul_right hmono _
        _ ≤ ENNReal.ofReal (A1^2) * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := hcheb'.trans hstrong'
        _ = ENNReal.ofReal ((t/2)^2) *
              ((ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := by
            nth_rewrite 1 [← mul_assoc]
            rw [ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
    calc ν {a : β | t / 2 < ‖T h a‖}
        = (ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal ((t/2)^2) * ν {a : β | t / 2 < ‖T h a‖}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
      _ ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal ((t/2)^2) *
              ((ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ))) :=
          mul_le_mul_right hkey _
      _ = _ := by
          nth_rewrite 1 [← mul_assoc]
          rw [ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
  have hcoef : ENNReal.ofReal (t ^ (p-1)) * (ENNReal.ofReal ((t/2)^2))⁻¹
      = ENNReal.ofReal (4 * t ^ (p-3)) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ((t/2)^2)⁻¹ = 4 * t^(-2:ℝ) := by
      have ha : t^(-2:ℝ) = (t^(2:ℝ))⁻¹ := by
        rw [show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg ht.le]
      have hb : t^(2:ℝ) = t^2 := by norm_num
      rw [ha, hb]
      field_simp
      ring
    rw [h1]
    have h2 : t ^ (p-1) * t^(-2:ℝ) = t^(p-3) := by
      rw [← Real.rpow_add ht (p-1) (-2), show p - 1 + (-2) = p - 3 by ring]
    calc t ^ (p-1) * (4 * t^(-2:ℝ)) = 4 * (t^(p-1) * t^(-2:ℝ)) := by ring
      _ = 4 * t^(p-3) := by rw [h2]
  have hcoef2 : ENNReal.ofReal (4 * t ^ (p-3)) * ENNReal.ofReal (A1^2)
      = ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (t ^ (p - 1)) * ν {a : β | t / 2 < ‖T h a‖}
      ≤ ENNReal.ofReal (t ^ (p-1)) *
          ((ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := mul_le_mul_right hmain _
    _ = (ENNReal.ofReal (t ^ (p-1)) * (ENNReal.ofReal ((t/2)^2))⁻¹) *
          (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by rw [mul_assoc]
    _ = (ENNReal.ofReal (4 * t ^ (p-3)) * ENNReal.ofReal (A1^2)) *
          ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by rw [hcoef, mul_assoc]
    _ = ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) *
          ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by rw [hcoef2]
    _ = ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) *
          (∫⁻ x, Set.indicator {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal t} (fun x => ‖f x‖ₑ ^ 2) x ∂μ) := by
        rw [hL]
    _ ≤ ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t ^ 2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) :=
        mul_le_mul_right hlow _

/-! ## Rescalings inside `ofReal` -/

lemma ofReal_rpow_scale {s e d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    ENNReal.ofReal ((2*s)^e/d) = ENNReal.ofReal (2^e/d) * ENNReal.ofReal (s^e) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hmul : (2*s)^e = 2^e * s^e := Real.mul_rpow h2.le hs
  rw [hmul, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos hd]
  ring

lemma ofReal_sqrt_rpow {s p : ℝ} (hs : 0 ≤ s) (hp : p < 2) :
    ENNReal.ofReal ((Real.sqrt s)^(p-2)/(2-p))
      = ENNReal.ofReal (1/(2-p)) * ENNReal.ofReal (s^((p-2)/2)) := by
  have hd : (0:ℝ) < 2 - p := by linarith
  have hpow : (Real.sqrt s)^(p-2) = s^((p-2)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs]
    congr 1
    ring
  rw [hpow, div_eq_mul_inv, one_div,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hd]
  ring

/-! ## Measurability of the parametric integrals -/

lemma measurable_lintegral_Ioi_half {T : ℝ → ℝ≥0∞} (hT : Measurable T) :
    Measurable (fun t : ℝ => ∫⁻ s in Set.Ioi (t/2), T s) := by
  rw [show (fun t : ℝ => ∫⁻ s in Set.Ioi (t/2), T s)
      = fun t : ℝ => ∫⁻ s, Set.indicator (Set.Ioi (t/2)) T s from
      funext fun t => (lintegral_indicator measurableSet_Ioi T).symm]
  have h1 : Measurable (Function.uncurry (fun t s : ℝ => Set.indicator (Set.Ioi (t/2)) T s)) := by
    have he : (Function.uncurry fun t s : ℝ => Set.indicator (Set.Ioi (t/2)) T s)
        = fun p : ℝ × ℝ => Set.indicator (Set.Ioi (p.1/2)) T p.2 := rfl
    rw [he]
    exact Measurable.indicator (hT.comp measurable_snd)
      (measurableSet_lt (measurable_fst.div_const 2) measurable_snd)
  exact h1.lintegral_prod_right (ν := volume)

lemma measurable_lintegral_Ioc_sq {T : ℝ → ℝ≥0∞} (hT : Measurable T) :
    Measurable (fun t : ℝ => ∫⁻ s in Set.Ioc (0:ℝ) (t^2), T (Real.sqrt s)) := by
  rw [show (fun t : ℝ => ∫⁻ s in Set.Ioc (0:ℝ) (t^2), T (Real.sqrt s))
      = fun t : ℝ => ∫⁻ s, Set.indicator (Set.Ioc (0:ℝ) (t^2)) (fun s => T (Real.sqrt s)) s from
      funext fun t => (lintegral_indicator measurableSet_Ioc (fun s => T (Real.sqrt s))).symm]
  have h1 : Measurable (Function.uncurry (fun t s : ℝ =>
      Set.indicator (Set.Ioc (0:ℝ) (t^2)) (fun s => T (Real.sqrt s)) s)) := by
    have he : (Function.uncurry fun t s : ℝ =>
        Set.indicator (Set.Ioc (0:ℝ) (t^2)) (fun s => T (Real.sqrt s)) s)
        = fun p : ℝ × ℝ => Set.indicator (Set.Ioc (0:ℝ) (p.1^2)) (fun s => T (Real.sqrt s)) p.2 := rfl
    rw [he]
    refine Measurable.indicator ((hT.comp Real.continuous_sqrt.measurable).comp measurable_snd) ?_
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.pow_const 2))
  exact h1.lintegral_prod_right (ν := volume)

lemma measurable_ofReal_mul_rpow {c q : ℝ} :
    Measurable (fun t : ℝ => ENNReal.ofReal (c * t ^ q)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_rpow_const q))


theorem marcinkiewicz_weak_one_strong_two {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} (T : (α → ℂ) → (β → ℂ))
    (hadd : ∀ f g : α → ℂ, T (f + g) = T f + T g)
    (hmeas : ∀ f : α → ℂ, AEMeasurable (T f) ν)
    {A0 A1 : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1)
    (hweak : ∀ (f : α → ℂ) (lam : ℝ), 0 < lam →
      ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) * MeasureTheory.eLpNorm f 1 μ)
    (hstrong : ∀ f : α → ℂ,
      MeasureTheory.eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f 2 μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : α → ℂ,
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
        ≤ ENNReal.ofReal (C * A0 ^ (2 / p - 1) * A1 ^ (2 - 2 / p))
            * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp1pos : 0 < p - 1 := by linarith
  have h2p : 0 < 2 - p := by linarith
  set K : ℝ := 12 * A0 * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 < 12 * A0 * 2 ^ (p - 1) / (p - 1) := by positivity
    have h2 : 0 < 16 * A1 ^ 2 / (2 - p) := by positivity
    linarith
  refine ⟨K ^ (1/p) / (A0 ^ (2/p - 1) * A1 ^ (2 - 2/p)), ?_, ?_⟩
  · have h1 : 0 < K ^ (1/p) := Real.rpow_pos_of_pos hKpos _
    have h2 : 0 < A0 ^ (2/p - 1) * A1 ^ (2 - 2/p) :=
      mul_pos (Real.rpow_pos_of_pos hA0 _) (Real.rpow_pos_of_pos hA1 _)
    exact div_pos h1 h2
  intro f
  by_cases hfm : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hfm, ENNReal.mul_top]
    · exact le_top
    · have hK' : 0 < K ^ (1/p) := Real.rpow_pos_of_pos hKpos _
      have hA : 0 < A0 ^ (2/p - 1) * A1 ^ (2 - 2/p) :=
        mul_pos (Real.rpow_pos_of_pos hA0 _) (Real.rpow_pos_of_pos hA1 _)
      refine (ENNReal.ofReal_pos.mpr ?_).ne'
      rw [mul_assoc]
      exact mul_pos (div_pos hK' hA) hA
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hTf : eLpNorm (T f) (ENNReal.ofReal p) ν = (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      (hmeas f).aestronglyMeasurable, htoReal]
  have hf : eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hfm, htoReal]
  rw [hTf, hf]
  have hmain : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤ ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    have hmeas_norm : AEMeasurable (fun x : β => ‖T f x‖) ν := (hmeas f).norm
    have hlayer : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν
        = ENNReal.ofReal p *
            ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t^(p-1)) := by
      rw [← lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := fun x : β => ‖T f x‖)
        (Eventually.of_forall fun (x : β) => norm_nonneg (T f x)) hmeas_norm hp0]
      refine lintegral_congr fun x => ?_
      rw [← ofReal_norm (T f x)]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (T f x)) hp0.le
    rw [hlayer]
    have htail : ∀ t : ℝ, 0 < t → ν {a : β | t < ‖T f a‖}
        ≤ ν {a : β | t / 2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℂ)) x) a‖}
        + ν {a : β | t / 2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℂ)) x) a‖} := by
      intro t ht
      have hsum : (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℂ)) x)
          + (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℂ)) x) = f :=
        mul_indicator_add_compl f
      exact le_trans (measure_mono (tail_subset T hadd t ht f _ _ hsum)) (measure_union_le _ _)
    have hmaj : ∀ t : ℝ, 0 < t →
        ν {a : β | t < ‖T f a‖} * ENNReal.ofReal (t^(p-1))
          ≤ ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
          + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
      intro t ht
      have h3 := high_pointwise (A0 := A0) (p := p) (T := T) (f := f) hA0 hp1 hfm hweak ht
      have h4 := low_pointwise (A1 := A1) (p := p) (T := T) (f := f) hA1 hp1 hfm hmeas hstrong ht
      calc ν {a : β | t < ‖T f a‖} * ENNReal.ofReal (t^(p-1))
          ≤ (ν {a : β | t/2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℂ)) x) a‖}
              + ν {a : β | t/2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℂ)) x) a‖})
              * ENNReal.ofReal (t^(p-1)) :=
            mul_le_mul_left (htail t ht) _
        _ = ENNReal.ofReal (t^(p-1)) * ν {a : β | t/2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun _ => (1:ℂ)) x) a‖}
              + ENNReal.ofReal (t^(p-1)) * ν {a : β | t/2 < ‖T (fun x => f x * Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun _ => (1:ℂ)) x) a‖} := by
            ring
        _ ≤ _ := add_le_add h3 h4
    have hInt : ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t^(p-1))
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
            + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hmaj t ht
    have hMA : Measurable (fun t : ℝ => ENNReal.ofReal (6 * A0 * t^(p-2)) *
        (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)) :=
      (measurable_ofReal_mul_rpow (c := 6 * A0) (q := p-2)).mul
        (measurable_lintegral_Ioi_half (innerTail_measurable μ _))
    have hML : Measurable (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
        (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) :=
      (measurable_ofReal_mul_rpow (c := 4 * A1^2) (q := p-3)).mul
        (measurable_lintegral_Ioc_sq (innerTail_measurable μ _))
    have hsplit := lintegral_add_left' (μ := volume.restrict (Set.Ioi (0:ℝ))) hMA.aemeasurable
        (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)))
    -- HIGH chain
    have hHigh : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) *
          (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
        ≤ ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))) := by
      have hT : Measurable (innerTail μ (fun x => ‖f x‖ₑ)) := innerTail_measurable μ _
      have hc : Measurable (fun t : ℝ => ENNReal.ofReal (6 * A0 * t^(p-2))) :=
        measurable_ofReal_mul_rpow (c := 6 * A0) (q := p-2)
      calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) *
            (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
          = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (6 * A0 * t^(p-2))) :=
            lintegral_Ioi_mul_Ioi_half_one hc hT
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * ∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (t^(p-2))) := by
            refine lintegral_congr fun s => ?_
            congr 1
            rw [show (∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (6 * A0 * t^(p-2)))
                = ∫⁻ t in Set.Ioo (0:ℝ) (2*s), ENNReal.ofReal (6 * A0) * ENNReal.ofReal (t^(p-2)) from
                lintegral_congr fun t =>
                  ENNReal.ofReal_mul (p := 6 * A0) (q := t^(p-2)) (by positivity),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2*s)^(p-1)/(p-1))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1
            congr 1
            rw [lintegral_Ioo_ofReal_rpow (X := 2*s) (q := p-2) (by linarith)
                (mul_nonneg (by norm_num) (le_of_lt (Set.mem_Ioi.1 hs))),
              show p - 2 + 1 = p - 1 by ring]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * (ENNReal.ofReal (2^(p-1)/(p-1)) * ENNReal.ofReal (s^(p-1)))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            rw [ofReal_rpow_scale (le_of_lt hs) hp1pos]
        _ = ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))) := by
            refine Eq.trans (lintegral_congr fun s => ?_)
              (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
            ring
        _ ≤ _ := le_rfl
    -- LOW chain
    have hLow : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))
        ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
      have hT : Measurable (innerTail μ (fun x => ‖f x‖ₑ)) := innerTail_measurable μ _
      have hTs : Measurable (fun s : ℝ => innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) :=
        hT.comp Real.continuous_sqrt.measurable
      have hc : Measurable (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3))) :=
        measurable_ofReal_mul_rpow (c := 4 * A1^2) (q := p-3)
      calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
            (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))
          = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (4 * A1^2 * t^(p-3))) :=
            lintegral_Ioi_mul_Ioc_sq_one hc hTs
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * ∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (t^(p-3))) := by
            refine lintegral_congr fun s => ?_
            congr 1
            rw [show (∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (4 * A1^2 * t^(p-3)))
                = ∫⁻ t in Set.Ioi (Real.sqrt s), ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (t^(p-3)) from
                lintegral_congr fun t =>
                  ENNReal.ofReal_mul (p := 4 * A1^2) (q := t^(p-3)) (by positivity),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal ((Real.sqrt s)^(p-2)/(2-p))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1
            congr 1
            rw [lintegral_Ioi_ofReal_rpow (X := Real.sqrt s) (q := p-3) (by linarith) (Real.sqrt_pos.2 hs)]
            rw [show p - 3 + 1 = p - 2 by ring]
            congr 1
            rw [← div_neg, show (-(p-2)) = 2 - p by ring]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * (ENNReal.ofReal (1/(2-p)) * ENNReal.ofReal (s^((p-2)/2)))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            rw [ofReal_sqrt_rpow (le_of_lt hs) hp2]
        _ = ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
            refine Eq.trans (lintegral_congr fun s => ?_)
              (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
            ring
        _ ≤ _ := le_rfl
    -- the two tail integrals against `∫⁻ W ^ p`
    have hWT : ENNReal.ofReal p *
          (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))
        ≤ 2 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      rw [show (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))
          = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^(p-1)) * innerTail μ (fun x => ‖f x‖ₑ) s from
          lintegral_congr fun s => mul_comm _ _]
      exact rpow_mul_innerTail_integral_le (μ := μ) (W := fun x => ‖f x‖ₑ) hp1
    have hST : ENNReal.ofReal p *
          (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
        ≤ 4 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      rw [show (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
          = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^((p-2)/2)) * innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) from
          lintegral_congr fun s => mul_comm _ _]
      exact sqrt_innerTail_integral_le (μ := μ) (W := fun x => ‖f x‖ₑ) hp1
    -- constants
    have hCH : ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) * 2
        = ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6 * A0),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6 * A0 * (2^(p-1)/(p-1)))]
      congr 1
      ring
    have hCL : ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) * 4
        = ENNReal.ofReal (16 * A1^2/(2-p)) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * A1^2),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * A1^2 * (1/(2-p)))]
      congr 1
      ring
    have hHighB : ENNReal.ofReal p *
          (ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))))
        ≤ ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      calc ENNReal.ofReal p *
            (ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))))
          = ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) *
              (ENNReal.ofReal p *
                (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))) := by
            ring
        _ ≤ ENNReal.ofReal (6 * A0) * ENNReal.ofReal (2^(p-1)/(p-1)) * (2 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :=
            mul_le_mul_right hWT _
        _ = ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
            rw [← hCH]; ring
    have hLowB : ENNReal.ofReal p *
          (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
        ≤ ENNReal.ofReal (16 * A1^2/(2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      calc ENNReal.ofReal p *
            (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
          = ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) *
              (ENNReal.ofReal p *
                (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))) := by
            ring
        _ ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (1/(2-p)) * (4 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :=
            mul_le_mul_right hST _
        _ = ENNReal.ofReal (16 * A1^2/(2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
            rw [← hCL]; ring
    calc ENNReal.ofReal p *
          (∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t^(p-1)))
        ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
            + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)))) :=
          mul_le_mul_right hInt _
      _ = ENNReal.ofReal p * ((∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s))
            + ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
          rw [hsplit]
      _ = ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s))
            + ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
          rw [mul_add]
      _ ≤ ENNReal.ofReal (12 * A0 * 2^(p-1)/(p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ
            + ENNReal.ofReal (16 * A1^2/(2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
          add_le_add ((mul_le_mul_right hHigh _).trans hHighB) ((mul_le_mul_right hLow _).trans hLowB)
      _ = ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), ← hK]
  calc (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p)
      ≤ (ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (ENNReal.ofReal K) ^ (1/p) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal (K ^ (1/p)) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hKpos.le (by positivity)]
    _ = ENNReal.ofReal (K ^ (1/p) / (A0 ^ (2/p - 1) * A1 ^ (2 - 2/p)) * A0 ^ (2/p - 1) * A1 ^ (2 - 2/p))
          * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
        congr 1
        rw [show K ^ (1/p) / (A0 ^ (2/p - 1) * A1 ^ (2 - 2/p)) * A0 ^ (2/p - 1) * A1 ^ (2 - 2/p) = K ^ (1/p) by
          have hX : A0 ^ (2/p - 1) * A1 ^ (2 - 2/p) ≠ 0 :=
            mul_ne_zero (Real.rpow_pos_of_pos hA0 _).ne' (Real.rpow_pos_of_pos hA1 _).ne'
          field_simp]

end Commons.Analysis.MeasureTheory