/-
# `Submission.Work.FIChain.s3MainLevelAux` — auxiliary definitions/lemmas for
`Work.FIChain.s3MainPlus_eq_levelSum`

This module contains

* the un-merged summand `s3MPF` of `Work.FIChain.s3MainPlus` (with the outer index `ℓ`),
* the level summand `s3MPPhi` (with the outer index `ℓ = b·e` split and the `Ã`-difference
  replaced by its `n`-summand),
* three pure-`Mathlib` lemmas used in the reindexing: the floor-membership identity for
  `Icc (⌊max⌋₊+1) (⌊min⌋₊)`, the integral-range collapse for `(Iio t).indicator`, and the
  interval integrability of `(Iio t).indicator (fun v ↦ (Σ_{d ≤ ⌊v⌋₊} c d)/v)`,
* the telescoping `Work.FIChain.AcountAtilC_sub_eq`.

Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.FIChain.s3MainLevelDefs
import Submission.Work.FIChain.sum_divisors_reindex

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The two summands -/

/-- The un-merged summand of `s3MainPlus`: the `ℓ`-th term with the divisor weight removed and the
`λ⁺`-inner sum kept in its `Ã(m₁) − Ã(m₂)` form. -/
def s3MPF (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ) : ℝ :=
  if ((ℓ : ℝ) * z ≤ (x : ℝ)) then
    Submission.ASP.rhoOf lam ℓ *
      ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
        (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
          Submission.ASP.FIgtil (ℓ * d) *
          (AcountAtilC ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊
            - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u
  else 0

/-- The `(b,e,n)`-summand: the `Ã`-difference replaced by the `n`-summand. -/
def s3MPPhi (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (n b e : ℕ) : ℝ :=
  if ((b : ℝ) * (e : ℝ) * z ≤ (x : ℝ)) then
    Submission.ASP.rhoOf lam (b * e) *
      ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / (((b * e : ℕ) : ℝ) * (Cm : ℝ)))),
        (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
          Submission.ASP.FIgtil ((b * e) * d) *
          (if n ∈ Finset.Icc (⌊max (((b * e : ℕ) : ℝ) * z)
                (((b * e : ℕ) : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
              (⌊min (((b * e : ℕ) : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)) / u
  else 0

/-! ## 2. Pure-`Mathlib` lemmas -/

/-- **The `(1.7)`-levels membership identity.**  For `n ∈ ℕ`,
`n ∈ Icc (⌊max (ℓz) (ℓ·Cm·u)⌋₊ + 1) ⌊min (ℓ·sz) x⌋₊` holds iff the three real inequalities of the
`(1.7)` block hold. -/
lemma mem_Icc_floor_max_min (n ℓ x : ℕ) (u z sz : ℝ) (Cm : ℕ) (hz : 0 ≤ z) (hsz : 0 ≤ sz) :
    n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
          ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊
      ↔ ((ℓ : ℝ) * z < (n : ℝ) ∧ (ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)
          ∧ (n : ℝ) ≤ (ℓ : ℝ) * sz ∧ n ≤ x) := by
  rw [Finset.mem_Icc]
  have hmax0 : 0 ≤ max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u) :=
    le_trans (by positivity) (le_max_left _ _)
  have hmin0 : 0 ≤ min ((ℓ : ℝ) * sz) ((x : ℝ)) := le_min (by positivity) (by positivity)
  constructor
  · rintro ⟨h1, h2⟩
    have hmaxlt : max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u) < (n : ℝ) :=
      (Nat.floor_lt hmax0).mp (by omega)
    have hnm : (n : ℝ) ≤ min ((ℓ : ℝ) * sz) ((x : ℝ)) :=
      le_trans (by exact_mod_cast h2) (Nat.floor_le hmin0)
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hmaxlt,
      lt_of_le_of_lt (le_max_right _ _) hmaxlt,
      le_trans hnm (min_le_left _ _),
      by exact_mod_cast (le_trans hnm (min_le_right _ _))⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_⟩
    · have : ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ < n :=
        (Nat.floor_lt hmax0).mpr (max_lt h1 h2)
      omega
    · apply Nat.le_floor
      exact le_min h3 (by exact_mod_cast h4)

/-- **The integral-range collapse.**  The indicator of `(Iio t)` cuts the integral over `1..B` down
to the integral over `1..min B (x/c)` as soon as `t ≤ x/c` and `1 ≤ B`. -/
lemma integral_range_Iio_indicator (w : ℝ → ℝ) {B U x c t : ℝ}
    (hB : 1 ≤ B) (hU : U = min B (x / c)) (ht : t ≤ x / c) :
    ∫ u in (1 : ℝ)..U, (Set.Iio t).indicator w u
      = ∫ u in (1 : ℝ)..B, (Set.Iio t).indicator w u := by
  have hUB : U ≤ B := by rw [hU]; exact min_le_left _ _
  have hUx : U ≤ x / c := by rw [hU]; exact min_le_right _ _
  by_cases hU1 : 1 ≤ U
  · rw [intervalIntegral.integral_of_le hU1, intervalIntegral.integral_of_le hB,
      MeasureTheory.setIntegral_indicator measurableSet_Iio,
      MeasureTheory.setIntegral_indicator measurableSet_Iio]
    have hset : Set.Ioc 1 U ∩ Set.Iio t = Set.Ioc 1 B ∩ Set.Iio t := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, le_trans h2 hUB⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, by rw [hU]; exact le_min h2 (le_of_lt (lt_of_lt_of_le h3 ht))⟩, h3⟩
    rw [hset]
  · have hU1' : U < 1 := lt_of_not_ge hU1
    have hUx' : U = x / c := by
      rcases min_cases B (x / c) with h | h
      · rw [hU, h.1] at hU1'; exact absurd hU1' (not_lt.mpr hB)
      · rw [hU, h.1]
    rw [intervalIntegral.integral_of_ge hU1'.le, intervalIntegral.integral_of_le hB,
      MeasureTheory.setIntegral_indicator (s := Set.Ioc U 1) measurableSet_Iio,
      MeasureTheory.setIntegral_indicator (s := Set.Ioc 1 B) measurableSet_Iio]
    have hE1 : Set.Ioc U 1 ∩ Set.Iio t = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro u ⟨⟨hu1, hu2⟩, hu3⟩
      simp only [Set.mem_Iio] at hu3
      have : t ≤ U := ht.trans_eq hUx'.symm
      linarith
    have hE2 : Set.Ioc 1 B ∩ Set.Iio t = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro u ⟨⟨hu1, hu2⟩, hu3⟩
      simp only [Set.mem_Iio] at hu3
      have : t < 1 := lt_of_le_of_lt (ht.trans_eq hUx'.symm) hU1'
      linarith
    rw [hE1, hE2]
    simp

/-- **Interval integrability of the level integrand.**  The step function
`u ↦ (Iio t).indicator (fun v ↦ (Σ_{d ≤ ⌊v⌋₊} c d)/v) u` is interval integrable on any interval
whose endpoints are positive. -/
lemma intervalIntegrable_indicator_floorSum_div (c : ℕ → ℝ) (t a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => (Set.Iio t).indicator
      (fun v : ℝ => (∑ d ∈ Finset.Icc 1 ⌊v⌋₊, c d) / v) u) volume a b := by
  have key : ∀ {a b : ℝ}, 0 < a → 0 < b → a ≤ b →
      IntervalIntegrable (fun u : ℝ => (Set.Iio t).indicator
        (fun v : ℝ => (∑ d ∈ Finset.Icc 1 ⌊v⌋₊, c d) / v) u) volume a b := by
    intro a b ha hb hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (measure_Ioc_lt_top (a := a) (b := b)).ne ?_
      (M := (∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d|) / a) ?_
    · exact (((measurable_of_countable
          (fun k : ℕ => ∑ d ∈ Finset.Icc 1 k, c d)).comp Nat.measurable_floor).div
        measurable_id).indicator measurableSet_Iio |>.aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => ?_)
      have hfu : ⌊u⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hu.2
      have h2 : ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, |c d| ≤ ∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hfu)
          (fun i _ _ => abs_nonneg _)
      have hu0 : 0 < u := lt_trans ha hu.1
      rw [Real.norm_eq_abs]
      have hle : |(Set.Iio t).indicator (fun v => (∑ d ∈ Finset.Icc 1 ⌊v⌋₊, c d) / v) u|
          ≤ |(∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d) / u| := by
        by_cases h : u ∈ Set.Iio t
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, abs_zero]; exact abs_nonneg _
      refine le_trans hle ?_
      rw [abs_div, abs_of_pos hu0]
      rw [div_le_div_iff₀ hu0 ha]
      have ha0 : 0 ≤ a := le_of_lt ha
      calc |∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d| * a
          ≤ (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, |c d|) * a :=
            mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) ha0
        _ ≤ (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, |c d|) * u :=
            mul_le_mul_of_nonneg_left hu.1.le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
        _ ≤ (∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d|) * u := mul_le_mul_of_nonneg_right h2 hu0.le
  rcases le_total a b with hab | hab
  · exact key ha hb hab
  · exact (key hb ha hab).symm

/-- `AcountAtilC m₁ - AcountAtilC m₂ = Σ_{m₂ < n ≤ m₁} ã(n)` for `m₂ ≤ m₁`. -/
lemma AcountAtilC_sub_eq {m₂ m₁ : ℕ} (hm : m₂ ≤ m₁) :
    AcountAtilC m₁ - AcountAtilC m₂ = ∑ n ∈ Finset.Icc (m₂ + 1) m₁, atilc n := by
  rw [← sum_atilc_Icc_eq, ← sum_atilc_Icc_eq]
  have h := Finset.sum_Ico_consecutive atilc (m := 1) (n := m₂ + 1) (k := m₁ + 1)
    (by omega) (by omega)
  rw [Finset.Ico_add_one_right_eq_Icc, Finset.Ico_add_one_right_eq_Icc,
      Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- `(if P ∧ Q then 1 else 0) = (if P then 1 else 0) * (if Q then 1 else 0)` over `ℝ`. -/
lemma ite_and_one_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- **Collapsing the `n`-indicator to the `Ã`-difference.**  For `m₂ ≤ m₁ ≤ x`, the `n`-sum of
`ã(n)` against the indicator of `Icc (m₂+1) m₁` is the difference of the counting function. -/
lemma sum_atilc_indicator_eq_sub {m₂ m₁ x : ℕ} (hm : m₂ ≤ m₁) (hm1 : m₁ ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, atilc n * (if n ∈ Finset.Icc (m₂ + 1) m₁ then 1 else 0)
      = AcountAtilC m₁ - AcountAtilC m₂ := by
  have hsub : Finset.Icc (m₂ + 1) m₁ ⊆ Finset.Icc 1 x := by
    intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
  rw [AcountAtilC_sub_eq hm]
  rw [← Finset.sum_subset (f := fun n => atilc n * (if n ∈ Finset.Icc (m₂ + 1) m₁ then 1 else 0))
        hsub (fun n hn hns => by rw [if_neg hns, mul_zero])]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [if_pos hn, mul_one]

/-- **The level `max ≤ min`.**  Under `z ≤ sz`, `Cm ≤ z` and `ℓz ≤ x`, for `u ∈ [1, min (sz/Cm)
(x/(ℓ·Cm))]` the upper level `max (ℓz) (ℓ·Cm·u)` of the `(1.7)`-block is dominated by the lower
level `min (ℓ·sz) x`. -/
lemma floor_max_le_floor_min (x ℓ Cm : ℕ) (z sz u : ℝ) (hCm : 1 ≤ Cm) (hzsz : z ≤ sz)
    (hCmz : (Cm : ℝ) ≤ z) (hP : (ℓ : ℝ) * z ≤ (x : ℝ)) (hu1 : 1 ≤ u)
    (hu2 : u ≤ min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))) :
    ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ ≤ ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊ := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast hCm
  have huA : u ≤ sz / (Cm : ℝ) := le_trans hu2 (min_le_left _ _)
  have huB : u ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := le_trans hu2 (min_le_right _ _)
  have hpos : 0 < (ℓ : ℝ) * (Cm : ℝ) := by
    have hne : (ℓ : ℝ) * (Cm : ℝ) ≠ 0 := by
      intro h0
      have hz : (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) = 0 := by rw [h0, div_zero]
      linarith [hu1, huB, hz]
    have hge : (1 : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by
      have hnat : (1 : ℕ) ≤ ℓ * Cm := by
        by_contra h
        have h0 : ℓ * Cm = 0 := by omega
        exact hne (by rw [← Nat.cast_mul, h0]; simp)
      calc (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
        _ ≤ ((ℓ * Cm : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (ℓ : ℝ) * (Cm : ℝ) := by push_cast; ring
    linarith
  apply Nat.floor_mono
  refine max_le (le_min ?_ hP) (le_min ?_ ?_)
  · nlinarith [(show (0:ℝ) ≤ (ℓ:ℝ) by positivity), hzsz]
  · have hle : (Cm : ℝ) * u ≤ sz := by
      rw [le_div_iff₀ hCmpos] at huA; linarith
    nlinarith [hle, (show (0:ℝ) ≤ (ℓ:ℝ) by positivity)]
  · have hle : (ℓ : ℝ) * (Cm : ℝ) * u ≤ (x : ℝ) := by
      rw [le_div_iff₀ hpos] at huB; linarith
    linarith

/-- The `0/1`-indicator of the `(1.7)`-level membership is the product of the four individual
`0/1`-indicators of the defining inequalities. -/
lemma ite_mem_Icc_eq_prod (n ℓ x : ℕ) (u z sz : ℝ) (Cm : ℕ) (hz : 0 ≤ z) (hsz : 0 ≤ sz) :
    (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
        (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then (1 : ℝ) else 0)
      = (if ((ℓ : ℝ) * z < (n : ℝ)) then 1 else 0)
        * (if ((ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then 1 else 0)
        * ((if ((n : ℝ) ≤ (ℓ : ℝ) * sz) then 1 else 0) * (if (n ≤ x) then 1 else 0)) := by
  have h := mem_Icc_floor_max_min n ℓ x u z sz Cm hz hsz
  have h1 : (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
        (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then (1 : ℝ) else 0)
      = (if (((ℓ : ℝ) * z < (n : ℝ)) ∧ ((ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ))
          ∧ ((n : ℝ) ≤ (ℓ : ℝ) * sz) ∧ (n ≤ x)) then 1 else 0) := by
    by_cases hc : n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
        (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊)
    · rw [if_pos hc, if_pos (h.mp hc)]
    · rw [if_neg hc, if_neg (fun hh => hc (h.mpr hh))]
  rw [h1]
  conv_lhs => rw [ite_and_one_mul, ite_and_one_mul, ite_and_one_mul]
  ring

/-- **Interval integrability of a level summand.**  If `F` is measurable and bounded by `1`, then
`u ↦ C·(1/u)·(Σ_{d ≤ ⌊u⌋₊} c d)·F u` is interval integrable on any interval with positive
endpoints. -/
lemma intervalIntegrable_mul_bdd_mul_floorSum_div (c : ℕ → ℝ) (F : ℝ → ℝ) (C a b : ℝ)
    (hFmeas : Measurable F) (hFbdd : ∀ u, |F u| ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u => C * (1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d) * F u)
      volume a b := by
  have hmeas : Measurable
      (fun u : ℝ => C * (1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d) * F u) :=
    ((measurable_const.mul (measurable_const.div measurable_id)).mul
      ((measurable_of_countable (fun k : ℕ => ∑ d ∈ Finset.Icc 1 k, c d)).comp
        Nat.measurable_floor)).mul hFmeas
  have key : ∀ {a b : ℝ}, 0 < a → 0 < b → a ≤ b → IntervalIntegrable
      (fun u => C * (1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d) * F u) volume a b := by
    intro a b ha hb hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (measure_Ioc_lt_top (a := a) (b := b)).ne hmeas.aestronglyMeasurable
      (M := |C| * ((∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d|) / a)) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => ?_)
    have hfu : ⌊u⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hu.2
    have h2 : ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, |c d| ≤ ∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hfu)
        (fun i _ _ => abs_nonneg _)
    have hu0 : 0 < u := lt_trans ha hu.1
    have hS0 : 0 ≤ ∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    rw [Real.norm_eq_abs]
    calc |C * (1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d) * F u|
        = |C| * (1 / u) * |∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d| * |F u| := by
          rw [abs_mul, abs_mul, abs_mul, abs_div, abs_one, abs_of_pos hu0]
      _ ≤ |C| * (1 / a) * (∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d|) * 1 := by
          gcongr
          · exact hu.1.le
          · exact le_trans (Finset.abs_sum_le_sum_abs _ _) h2
          · exact hFbdd u
      _ = |C| * ((∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |c d|) / a) := by
          rw [div_eq_mul_inv]; ring
  rcases le_total a b with hab | hab
  · exact key ha hb hab
  · exact (key hb ha hab).symm

/-- **The `Ã`-difference as an `n`-sum, integrated.**  Replacing `Ã(m₁) − Ã(m₂)` by
`Σ_{m₂ < n ≤ m₁} ã(n)` inside the `u`-integral, and swapping the (finite) `n`-sum out of the
integral. -/
lemma integral_AcountAtilC_diff_eq (x : ℕ) (ℓ Cm : ℕ) (z sz U : ℝ) (c : ℕ → ℝ)
    (hx : 1 ≤ x) (hCm : 1 ≤ Cm) (hzsz : z ≤ sz) (hCmz : (Cm : ℝ) ≤ z)
    (hP : (ℓ : ℝ) * z ≤ (x : ℝ))
    (hU : U = min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))) (hU1 : 1 ≤ U) :
    ∫ u in (1 : ℝ)..U, (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d *
        (AcountAtilC ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊
          - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u
      = ∑ n ∈ Finset.Icc 1 x, atilc n * ∫ u in (1 : ℝ)..U, (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d *
          (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
              (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)) / u := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast hCm
  have hz1 : (1 : ℝ) ≤ z := le_trans (by exact_mod_cast hCm) hCmz
  have hz0 : 0 ≤ z := by linarith
  have hsz0 : 0 ≤ sz := le_trans hz0 hzsz
  have hm1x : ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊ ≤ x := by
    calc ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊ ≤ ⌊(x : ℝ)⌋₊ := Nat.floor_mono (min_le_right _ _)
      _ = x := Nat.floor_natCast x
  have hpoint : ∀ u ∈ Set.uIcc (1 : ℝ) U,
      (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d *
        (AcountAtilC ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊
          - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u
      = ∑ n ∈ Finset.Icc 1 x, atilc n * ((∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d *
          (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
              (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)) / u) := by
    intro u hu
    rw [Set.uIcc_of_le hU1] at hu
    obtain ⟨hu1, huU⟩ := hu
    have hu2 : u ≤ min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) := by
      rw [← hU]; exact huU
    have hm2 : ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
        ≤ ⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊ :=
      floor_max_le_floor_min x ℓ Cm z sz u hCm hzsz hCmz hP hu1 hu2
    rw [← sum_atilc_indicator_eq_sub (x := x) hm2 hm1x]
    rw [show (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d *
            (∑ n ∈ Finset.Icc 1 x, atilc n *
              (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
                  (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)))
          = ∑ n ∈ Finset.Icc 1 x, atilc n *
              (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d *
                (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
                    (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)) from by
        calc ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d *
              (∑ n ∈ Finset.Icc 1 x, atilc n * (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1) (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0))
            = ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, ∑ n ∈ Finset.Icc 1 x, c d * (atilc n * (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1) (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)) := by
              refine Finset.sum_congr rfl (fun d _ => ?_); rw [Finset.mul_sum]
          _ = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d * (atilc n * (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1) (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)) := Finset.sum_comm
          _ = ∑ n ∈ Finset.Icc 1 x, atilc n * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d * (if n ∈ Finset.Icc (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ + 1) (⌊min ((ℓ : ℝ) * sz) ((x : ℝ))⌋₊) then 1 else 0)) := by
              refine Finset.sum_congr rfl (fun n _ => ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun d _ => ?_)
              ring]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_div_assoc]
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [intervalIntegral.integral_const_mul]
  · intro n _
    have hFmeas : Measurable
        (fun u : ℝ => if ((ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then (1 : ℝ) else 0) := by
      have hs : MeasurableSet {u : ℝ | (ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)} :=
        (continuous_const.mul continuous_id).measurable measurableSet_Iio
      exact Measurable.ite hs measurable_const measurable_const
    have hFbdd : ∀ u : ℝ,
        |(if ((ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then (1 : ℝ) else 0)| ≤ 1 := by
      intro u
      by_cases h : ((ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)) <;> simp [h]
    have hUpos : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU1
    refine (intervalIntegrable_mul_bdd_mul_floorSum_div c
      (fun u : ℝ => if ((ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then (1 : ℝ) else 0)
      (atilc n * (if ((ℓ : ℝ) * z < (n : ℝ)) then 1 else 0)
        * (if ((n : ℝ) ≤ (ℓ : ℝ) * sz) then 1 else 0) * (if n ≤ x then 1 else 0))
      (1 : ℝ) U hFmeas hFbdd (by norm_num) hUpos).congr (fun u _ => ?_)
    rw [ite_mem_Icc_eq_prod n ℓ x u z sz Cm hz0 hsz0]
    set IA : ℝ := (if ((ℓ : ℝ) * z < (n : ℝ)) then 1 else 0) with hIA
    set IB : ℝ := (if ((ℓ : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then 1 else 0) with hIB
    set IC : ℝ := (if ((n : ℝ) ≤ (ℓ : ℝ) * sz) then 1 else 0) with hIC
    set ID : ℝ := (if (n ≤ x) then 1 else 0) with hID
    rw [show (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d * (IA * IB * (IC * ID)))
          = (IA * IB * (IC * ID)) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, c d) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by ring)]
    ring

/-- **The `n`-expansion of the un-merged summand.**  `s3MPF (b·e)` is the `n`-sum of its level
summands `s3MPPhi n b e`. -/
lemma s3MPF_be_eq_sum_Phi (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (b e : ℕ)
    (hb : 1 ≤ b) (he : 1 ≤ e) (hx : 1 ≤ x) (hCm : 1 ≤ Cm) (hz : 1 ≤ z) (hzsz : z ≤ sz)
    (hCmsz : (Cm : ℝ) ≤ sz) (hCmz : (Cm : ℝ) ≤ z) :
    s3MPF lam x z sz Cm (b * e)
      = ∑ n ∈ Finset.Icc 1 x, atilc n * s3MPPhi lam x z sz Cm n b e := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast hCm
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hcast : ((b * e : ℕ) : ℝ) = (b : ℝ) * (e : ℝ) := by push_cast; ring
  have hszCm1 : 1 ≤ sz / (Cm : ℝ) := by rw [le_div_iff₀ hCmpos]; simpa using hCmsz
  simp only [s3MPF, s3MPPhi, hcast]
  by_cases hP : (b : ℝ) * (e : ℝ) * z ≤ (x : ℝ)
  · simp only [if_pos hP]
    set U : ℝ := min (sz / (Cm : ℝ)) ((x : ℝ) / (((b : ℝ) * (e : ℝ)) * (Cm : ℝ))) with hUdef
    have hbeCmp : (0 : ℝ) < ((b : ℝ) * (e : ℝ)) * (Cm : ℝ) := by positivity
    have hU1 : 1 ≤ U := by
      rw [hUdef]
      refine le_min hszCm1 ?_
      rw [le_div_iff₀ hbeCmp]
      have h1 : (b : ℝ) * (e : ℝ) * (Cm : ℝ) ≤ (b : ℝ) * (e : ℝ) * z :=
        mul_le_mul_of_nonneg_left hCmz (by positivity)
      linarith
    have hU' : U = min (sz / (Cm : ℝ)) ((x : ℝ) / (((b * e : ℕ) : ℝ) * (Cm : ℝ))) := by
      rw [hUdef, hcast]
    have hP' : (((b * e : ℕ) : ℝ)) * z ≤ (x : ℝ) := by rw [hcast]; exact hP
    have hcore := integral_AcountAtilC_diff_eq x (b * e) Cm z sz U
      (fun d => (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b * e) * d))
      hx hCm hzsz hCmz hP' hU' hU1
    simp only [hcast] at hcore
    rw [hcore, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  · simp only [if_neg hP]
    simp

/-! ## 3. The comparison integrands -/

/-- The `(b,e,u)`-integrand after the `n`-expansion: the level summand with the `Ã`-difference
replaced by its `n`-indicator and the integral extended to `[1, sz/Cm]`. -/
def s3MPT (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (n b e : ℕ) (u : ℝ) : ℝ :=
  (if ((b : ℝ) * (e : ℝ) * z ≤ (x : ℝ)) then (1 : ℝ) else 0)
  * (if ((b : ℝ) * (e : ℝ) * z < (n : ℝ)) then (1 : ℝ) else 0)
  * (if ((n : ℝ) ≤ (b : ℝ) * (e : ℝ) * sz) then (1 : ℝ) else 0)
  * (if (n ≤ x) then (1 : ℝ) else 0)
  * Submission.ASP.rhoOf lam (b * e)
  * ((1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
      (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b * e) * d)))
  * (if ((b : ℝ) * (e : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then (1 : ℝ) else 0)

/-- The `u`-integrand of the level sum `K(n)`. -/
def s3MPLevelSum (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
    (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
      * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)

/-- `s3MainLevelSum` is the integral of `(1/u)·s3MPLevelSum`. -/
lemma s3MainLevelSum_eq_integral (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) :
    s3MainLevelSum lam x z sz Cm sy n
      = ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), (1 / u) * s3MPLevelSum lam x z sz Cm sy n u := rfl

/-- The `0/1`-indicator of the `(1.7)`-level membership, with the index `b·e` split. -/
lemma ite_mem_Icc_eq_prod' (n b e x : ℕ) (u z sz : ℝ) (Cm : ℕ) (hz : 0 ≤ z) (hsz : 0 ≤ sz) :
    (if n ∈ Finset.Icc (⌊max ((b : ℝ) * (e : ℝ) * z) ((b : ℝ) * (e : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
        (⌊min ((b : ℝ) * (e : ℝ) * sz) ((x : ℝ))⌋₊) then (1 : ℝ) else 0)
      = (if ((b : ℝ) * (e : ℝ) * z < (n : ℝ)) then 1 else 0)
        * (if ((b : ℝ) * (e : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then 1 else 0)
        * ((if ((n : ℝ) ≤ (b : ℝ) * (e : ℝ) * sz) then 1 else 0) * (if (n ≤ x) then 1 else 0)) := by
  have hcast : ((b * e : ℕ) : ℝ) = (b : ℝ) * (e : ℝ) := by push_cast; ring
  have h := ite_mem_Icc_eq_prod n (b * e) x u z sz Cm hz hsz
  simpa only [hcast] using h

/-- The integral-range collapse for the raw indicator `[c·u < n]`. -/
lemma integral_range_lt_mul (w : ℝ → ℝ) {B U x c n : ℝ} (hc : 0 < c) (hB : 1 ≤ B)
    (hU : U = min B (x / c)) (hn : n ≤ x) :
    ∫ u in (1 : ℝ)..U, (if c * u < n then w u else 0)
      = ∫ u in (1 : ℝ)..B, (if c * u < n then w u else 0) := by
  have h1 : (fun u : ℝ => (if c * u < n then w u else 0)) = (Set.Iio (n / c)).indicator w := by
    funext u
    by_cases h : c * u < n
    · rw [if_pos h, Set.indicator_of_mem (by rw [Set.mem_Iio, lt_div_iff₀ hc]; linarith)]
    · rw [if_neg h, Set.indicator_of_notMem (fun hh => by
        rw [Set.mem_Iio, lt_div_iff₀ hc] at hh; linarith)]
  rw [h1]
  exact integral_range_Iio_indicator w hB hU (div_le_div_of_nonneg_right hn hc.le)

end

end Work.FIChain
