/-
# `Submission.Work.FIChain.BpWinAux` — auxiliary lemmas for the integrated `(B′)`-window

Infrastructure for `Work.FIChain.BprimeWindowIntegrated` (the `Π`-removal of the companion
paper's §10, Theorem 3, in the integrated form used by the `(B′)`-window):

* `AcountAtilC_eq`, `abs_Xf_le_Acount`, `abs_Xsum_le_Acount` — crude domination of the window
  sums by `Ã(x)` (used only for integrability);
* `intervalIntegrable_div_of_bounded'`, `integrable_Xf_sum`, `integrable_tau_cub_sum`,
  `integrable_Xsum_sum`, `integrable_const_div` — interval-integrability of the window
  integrands on `[a,b]`, `0 < a ≤ b`;
* `integral_div_comp_div'` — the substitution `∫_{lo}^{hi} f(t/b)/t dt = ∫_{lo/b}^{hi/b} f(u)/u du`;
* `integral_mono_range'` — range extension for nonnegative integrands;
* `sum_tau_cub_sq_le` — the pointwise Cauchy–Schwarz bound for the `τ³`-weighted sum;
* `eventually_Dpi_le_rpow` — `Δπ = ⌈exp(κ(loglog x)³)⌉ ≤ x^r` eventually, for any `r > 0`.

Still missing (see the handoff notes in `BprimeWindowIntegrated.lean`): `integrable_G1`, the
interval-integrability of the `(∑_m wc m · |∑_{b₁ ≤ D} μ(b₁) Xf (m b₁) (t/b₁)|)/t` integrand.

This file contains no `sorry` and no `axiom`.
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary integrability and arithmetic helpers -/

/-- `Xf` written as a sum over a `u`-independent index set with `u`-dependent `if`s. -/
lemma Xf_eq_ite' (x Pz c : ℕ) (u : ℝ) :
    Xf x Pz c u = ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n),
      (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
        then (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) else 0) := by
  rw [Xf, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun n _ => ?_)
  · ext n; simp only [Finset.mem_filter]; tauto
  · by_cases h : u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u <;> simp [h]

lemma measurable_Xf' (x Pz c : ℕ) : Measurable (fun u : ℝ => Xf x Pz c u) := by
  have h : (fun u : ℝ => Xf x Pz c u) = fun u =>
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n),
        (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
          then (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) else 0) := by
    funext u; exact Xf_eq_ite' x Pz c u
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_const.mul measurable_id))

/-- `AcountAtilC x = Σ_{n ∈ Icc 1 x} ã(n)`. -/
lemma AcountAtilC_eq (x : ℕ) : AcountAtilC x = ∑ n ∈ Finset.Icc 1 x, atilc n := by
  rw [AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]

lemma AcountAtilC_nonneg' (x : ℕ) : 0 ≤ AcountAtilC x := by
  rw [AcountAtilC_eq]
  exact Finset.sum_nonneg (fun n _ => Work.FITop.atilFIa_nonneg n)

lemma atilc_zero : atilc 0 = 0 := by
  rw [atilc, Work.FITop.atilFIa, Submission.ASP.atil]
  simp

/-- `|Xf|` is dominated by the counting function `Ã`. -/
lemma abs_Xf_le_Acount (x Pz c : ℕ) (u : ℝ) : |Xf x Pz c u| ≤ AcountAtilC x := by
  have h1 : |Xf x Pz c u| ≤ ∑ n ∈ (Finset.Icc 1 x).filter
      (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u ∧
        Work.FITop4.PiCond Pz n), atilc (c * n) := abs_Xf_le_sum x Pz c u
  have h2 : (∑ n ∈ (Finset.Icc 1 x).filter
      (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u ∧
        Work.FITop4.PiCond Pz n), atilc (c * n))
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x), atilc (c * n) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => by
        rw [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, hn.2.1⟩)
      (fun i _ _ => Work.FITop.atilFIa_nonneg _)
  have h3 : (∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x), atilc (c * n))
      ≤ ∑ l ∈ Finset.Icc 1 x, atilc l := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp only [zero_mul, atilc_zero]
      rw [Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun n _ => Work.FITop.atilFIa_nonneg n)
    · have hinj : Set.InjOn (fun n => c * n) ↑((Finset.Icc 1 x).filter (fun n => c * n ≤ x)) := by
        intro a _ b _ hab
        exact Nat.mul_left_cancel hc hab
      have himg : ((Finset.Icc 1 x).filter (fun n => c * n ≤ x)).image (fun n => c * n)
          ⊆ Finset.Icc 1 x := by
        intro l hl
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
        rw [Finset.mem_filter] at hb
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb.1).1
        exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hc.ne'
          (by omega)), hb.2⟩
      calc (∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x), atilc (c * n))
          = ∑ l ∈ ((Finset.Icc 1 x).filter (fun n => c * n ≤ x)).image (fun n => c * n),
              atilc l := (Finset.sum_image (f := fun l => atilc l) hinj).symm
        _ ≤ ∑ l ∈ Finset.Icc 1 x, atilc l :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => Work.FITop.atilFIa_nonneg _)
  have h4 : (∑ l ∈ Finset.Icc 1 x, atilc l) = AcountAtilC x := (AcountAtilC_eq x).symm
  exact le_trans h1 (le_trans h2 (le_trans h3 (le_of_eq h4)))

/-- `|Xsum|` is dominated by the counting function `Ã`. -/
lemma abs_Xsum_le_Acount (x m : ℕ) (t u : ℝ) :
    |Submission.ASP.Xsum atilc x m t u| ≤ AcountAtilC x := by
  rw [Submission.ASP.Xsum]
  have h1 : |∑ b ∈ (Finset.Icc 1 x).filter
        (fun b => t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ u ∧ b * m ≤ x),
        (ArithmeticFunction.moebius b : ℝ) * atilc (b * m)|
      ≤ ∑ b ∈ (Finset.Icc 1 x).filter
        (fun b => t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ u ∧ b * m ≤ x), atilc (b * m) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => ?_))
    rw [abs_mul]
    have hμ : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := b)
      exact_mod_cast h
    have hã : 0 ≤ atilc (b * m) := Work.FITop.atilFIa_nonneg _
    calc |(ArithmeticFunction.moebius b : ℝ)| * |atilc (b * m)|
        ≤ 1 * |atilc (b * m)| := mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ = atilc (b * m) := by rw [one_mul, abs_of_nonneg hã]
  have h2 : (∑ b ∈ (Finset.Icc 1 x).filter
        (fun b => t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ u ∧ b * m ≤ x), atilc (b * m))
      ≤ ∑ b ∈ (Finset.Icc 1 x).filter (fun b => b * m ≤ x), atilc (b * m) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun b hb => by
        rw [Finset.mem_filter] at hb ⊢
        exact ⟨hb.1, hb.2.2.2⟩)
      (fun i _ _ => Work.FITop.atilFIa_nonneg _)
  have h3 : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => b * m ≤ x), atilc (b * m))
      ≤ ∑ l ∈ Finset.Icc 1 x, atilc l := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [mul_zero, atilc_zero]
      rw [Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun n _ => Work.FITop.atilFIa_nonneg n)
    · set s : Finset ℕ := (Finset.Icc 1 x).filter (fun b => b * m ≤ x) with hs
      have hinj : Set.InjOn (fun b => b * m) ↑s := by
        intro a _ b _ hab
        exact Nat.mul_right_cancel hm hab
      have himg : s.image (fun b => b * m) ⊆ Finset.Icc 1 x := by
        intro l hl
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
        rw [hs, Finset.mem_filter] at hb
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb.1).1
        exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hm.ne'),
          hb.2⟩
      calc (∑ b ∈ (Finset.Icc 1 x).filter (fun b => b * m ≤ x), atilc (b * m))
          = ∑ b ∈ s, atilc (b * m) := by rw [hs]
        _ = ∑ l ∈ s.image (fun b => b * m), atilc l :=
            (Finset.sum_image (f := fun l => atilc l) hinj).symm
        _ ≤ ∑ l ∈ Finset.Icc 1 x, atilc l :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => Work.FITop.atilFIa_nonneg _)
  have h4 : (∑ l ∈ Finset.Icc 1 x, atilc l) = AcountAtilC x := (AcountAtilC_eq x).symm
  exact le_trans h1 (le_trans h2 (le_trans h3 (le_of_eq h4)))

/-- Integrability of `u ↦ Φ u / u` for measurable `Φ` bounded by `C`, on `[a,b]`, `0 < a ≤ b`. -/
lemma intervalIntegrable_div_of_bounded' {Φ : ℝ → ℝ} {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hm : Measurable Φ) (hC : ∀ u, |Φ u| ≤ C) :
    IntervalIntegrable (fun u => Φ u / u) volume a b := by
  constructor
  · refine MeasureTheory.IntegrableOn.of_bound (measure_Ioc_lt_top (a := a) (b := b)) ?_ (C / a) ?_
    · exact ((hm.div measurable_id).aestronglyMeasurable).mono_measure Measure.restrict_le_self
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu0 : 0 < u := lt_trans ha hu.1
      have hCnn : 0 ≤ C := le_trans (abs_nonneg (Φ a)) (hC a)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0]
      calc |Φ u| / u = |Φ u| * u⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ C * u⁻¹ := mul_le_mul_of_nonneg_right (hC u) (inv_nonneg.mpr hu0.le)
        _ ≤ C * a⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ hCnn
            simpa [one_div] using one_div_le_one_div_of_le ha hu.1.le
        _ = C / a := by rw [div_eq_mul_inv]
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
    exact integrableOn_empty

/-- `∫_{lo}^{hi} f (t/b) / t dt = ∫_{lo/b}^{hi/b} f u / u du` for `b ≠ 0`. -/
lemma integral_div_comp_div' (f : ℝ → ℝ) {b lo hi : ℝ} (hb : b ≠ 0) :
    (∫ t in lo..hi, f (t / b) / t) = ∫ u in lo / b..hi / b, f u / u := by
  have hpt : ∀ t : ℝ, f (t / b) / t = (1 / b) * (f (t / b) / (t / b)) := by
    intro t
    by_cases ht : t = 0
    · simp [ht]
    · field_simp
  have h1 : (∫ t in lo..hi, f (t / b) / t)
      = (1 / b) * ∫ t in lo..hi, (fun v : ℝ => f v / v) (t / b) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => hpt t)
  rw [h1, intervalIntegral.integral_comp_div (fun v : ℝ => f v / v) hb]
  rw [smul_eq_mul, ← mul_assoc, one_div, inv_mul_cancel₀ hb, one_mul]

/-- Range extension for nonnegative integrands. -/
lemma integral_mono_range' {f : ℝ → ℝ} {c a b d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hf0 : ∀ u ∈ Set.Icc c d, 0 ≤ f u) (hint : IntervalIntegrable f volume c d) :
    (∫ u in a..b, f u) ≤ ∫ u in c..d, f u := by
  refine intervalIntegral.integral_mono_interval hca hab hbd ?_ hint
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall (fun u hu => hf0 u ⟨hu.1.le, hu.2⟩)

/-- The pointwise Cauchy–Schwarz of the two Hölder factors. -/
lemma sum_tau_cub_sq_le (x Pz : ℕ) (u : ℝ) :
    ((∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u|)) ^ 2
      ≤ Aw x Pz u * Bw x Pz u := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 x)
    (fun c => Real.sqrt |Xf x Pz c u|)
    (fun c => ((c.divisors.card : ℝ)) ^ 3 * Real.sqrt |Xf x Pz c u|)
  have h1 : (∑ c ∈ Finset.Icc 1 x,
        Real.sqrt |Xf x Pz c u| * (((c.divisors.card : ℝ)) ^ 3 * Real.sqrt |Xf x Pz c u|))
      = ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u| := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hs : Real.sqrt |Xf x Pz c u| * Real.sqrt |Xf x Pz c u| = |Xf x Pz c u| := by
      rw [← sq]; exact Real.sq_sqrt (abs_nonneg _)
    calc Real.sqrt |Xf x Pz c u| * (((c.divisors.card : ℝ)) ^ 3 * Real.sqrt |Xf x Pz c u|)
        = (Real.sqrt |Xf x Pz c u| * Real.sqrt |Xf x Pz c u|) * ((c.divisors.card : ℝ)) ^ 3 := by
          ring
      _ = ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u| := by rw [hs]; ring
  have h2 : (∑ c ∈ Finset.Icc 1 x, (Real.sqrt |Xf x Pz c u|) ^ 2) = Aw x Pz u := by
    simp only [Aw]
    exact Finset.sum_congr rfl (fun c _ => Real.sq_sqrt (abs_nonneg _))
  have h3 : (∑ c ∈ Finset.Icc 1 x,
        (((c.divisors.card : ℝ)) ^ 3 * Real.sqrt |Xf x Pz c u|) ^ 2) = Bw x Pz u := by
    simp only [Bw]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hs : Real.sqrt |Xf x Pz c u| ^ 2 = |Xf x Pz c u| := Real.sq_sqrt (abs_nonneg _)
    rw [mul_pow, hs]
    ring
  rw [h1, h2, h3] at h
  exact h

/-- `Δπ` is eventually below any fixed positive power of `x`. -/
lemma eventually_Dpi_le_rpow (κ r : ℝ) (hκ : 0 < κ) (hr : 0 < r) :
    ∀ᶠ x : ℕ in Filter.atTop, (Dpi x κ : ℝ) ≤ (x : ℝ) ^ r := by
  filter_upwards [Work.FITop.FI_ev_log_ge_nat ((128 * κ / r) ^ 4),
    Work.FITop.FI_ev_log_ge_nat 1,
    Work.FITop.FI_ev_rpow_ge_nat 1 (by norm_num) ((2 : ℝ) ^ (2 / r))] with x hlog hlog1 hxbig
  have hxbig' : (2 : ℝ) ^ (2 / r) ≤ (x : ℝ) := by simpa using hxbig
  have htwo : (2 : ℝ) ≤ (x : ℝ) ^ (r / 2) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hxbig'
      (by positivity : (0 : ℝ) ≤ r / 2)
    rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
      show (2 / r) * (r / 2) = 1 by field_simp, Real.rpow_one] at h
  have hxpos : 0 < (x : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 / r)) hxbig'
  set L : ℝ := Real.log (x : ℝ) with hL
  have hLpos : 0 < L := by rw [hL]; exact lt_of_lt_of_le one_pos hlog1
  have hLLnn : 0 ≤ Real.log L := Real.log_nonneg hlog1
  have hlogLL : Real.log L ≤ 4 * L ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div hLpos.le (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)
    calc Real.log L ≤ L ^ ((1 : ℝ) / 4) / (1 / 4) := h
      _ = 4 * L ^ ((1 : ℝ) / 4) := by ring
  have h3 : (Real.log L) ^ 3 ≤ 64 * L ^ ((3 : ℝ) / 4) := by
    calc (Real.log L) ^ 3 ≤ (4 * L ^ ((1 : ℝ) / 4)) ^ 3 := pow_le_pow_left₀ hLLnn hlogLL 3
      _ = 64 * L ^ ((3 : ℝ) / 4) := by
          have h13 : (L ^ ((1 : ℝ) / 4)) ^ (3 : ℕ) = L ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
            norm_num
          rw [mul_pow, h13]
          norm_num
  have h4 : (128 * κ / r) ^ 4 ≤ L := hlog
  have h5 : 64 * κ ≤ (r / 2) * L ^ ((1 : ℝ) / 4) := by
    have h6 : ((128 * κ / r) ^ 4) ^ ((1 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    have h7 : ((128 * κ / r) ^ 4) ^ ((1 : ℝ) / 4) = 128 * κ / r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 128 * κ / r)]
      norm_num
    rw [h7] at h6
    have h8 : (r / 2) * (128 * κ / r) = 64 * κ := by field_simp; ring
    calc 64 * κ = (r / 2) * (128 * κ / r) := h8.symm
      _ ≤ (r / 2) * L ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left h6 (by positivity)
  have hexp : Real.exp (κ * (Real.log L) ^ 3) ≤ (x : ℝ) ^ (r / 2) := by
    rw [Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    have h9 : κ * (Real.log L) ^ 3 ≤ κ * (64 * L ^ ((3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left h3 hκ.le
    have h10 : κ * (64 * L ^ ((3 : ℝ) / 4)) ≤ (r / 2) * L := by
      have h11 : (64 * κ) * L ^ ((3 : ℝ) / 4) ≤ ((r / 2) * L ^ ((1 : ℝ) / 4)) * L ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hLpos.le _)
      have h12 : ((r / 2) * L ^ ((1 : ℝ) / 4)) * L ^ ((3 : ℝ) / 4) = (r / 2) * L := by
        rw [mul_assoc, ← Real.rpow_add hLpos]
        norm_num
      calc κ * (64 * L ^ ((3 : ℝ) / 4)) = (64 * κ) * L ^ ((3 : ℝ) / 4) := by ring
        _ ≤ ((r / 2) * L ^ ((1 : ℝ) / 4)) * L ^ ((3 : ℝ) / 4) := h11
        _ = (r / 2) * L := h12
    rw [hL]
    linarith [h9, h10]
  have hDpi : (Dpi x κ : ℝ) ≤ Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3) + 1 := by
    rw [Dpi]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.exp_pos _).le)
  have hexp' : Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3) ≤ (x : ℝ) ^ (r / 2) := by
    rw [← hL]; exact hexp
  calc (Dpi x κ : ℝ) ≤ Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3) + 1 := hDpi
    _ ≤ 2 * Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3) := by
        have := Real.one_le_exp (show (0 : ℝ) ≤ κ * (Real.log (Real.log (x : ℝ))) ^ 3 by
          exact mul_nonneg hκ.le (by positivity))
        linarith
    _ ≤ 2 * (x : ℝ) ^ (r / 2) := by linarith [hexp']
    _ ≤ (x : ℝ) ^ (r / 2) * (x : ℝ) ^ (r / 2) := by nlinarith [htwo]
    _ = (x : ℝ) ^ r := by rw [← Real.rpow_add hxpos]; norm_num


/-! ## Integrability of the concrete window integrands -/

lemma wc_le (x m : ℕ) (hm : m ∈ Finset.Icc 1 x) : wc m ≤ (x : ℝ) ^ 2 := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmx : m ≤ x := (Finset.mem_Icc.mp hm).2
  have hsub : m.divisors ⊆ Finset.Icc 1 x := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd.1 (by omega),
      le_trans (Nat.le_of_dvd (by omega) hd.1) hmx⟩
  have h1 : (m.divisors.card : ℝ) ≤ (x : ℝ) := by
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact_mod_cast hcard
  calc wc m = ((m.divisors.card : ℝ)) ^ 2 := rfl
    _ ≤ (x : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2

lemma integrable_Xf_sum (x Pz : ℕ) (s : Finset ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => (∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x,
        wc m * |Xf x Pz (m * b₁) u|) / u) volume a b := by
  refine intervalIntegrable_div_of_bounded' (C := (s.card : ℝ) * (x : ℝ) *
    ((x : ℝ) ^ 2 * AcountAtilC x)) ha hab ?_ ?_
  · exact Finset.measurable_sum _ (fun b₁ _ => Finset.measurable_sum _ (fun m _ =>
      (measurable_Xf' x Pz (m * b₁)).abs.const_mul _))
  · intro u
    have h1 : (∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x, wc m * |Xf x Pz (m * b₁) u|)
        ≤ ∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 * AcountAtilC x := by
      refine Finset.sum_le_sum (fun b₁ _ => Finset.sum_le_sum (fun m hm => ?_))
      exact mul_le_mul (wc_le x m hm) (abs_Xf_le_Acount x Pz (m * b₁) u) (abs_nonneg _)
        (by positivity)
    have h2 : (∑ b₁ ∈ s, ∑ m ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 * AcountAtilC x)
        = (s.card : ℝ) * (x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x) := by
      rw [Finset.sum_const, Finset.sum_const]
      simp only [smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      ring
    rw [abs_of_nonneg (Finset.sum_nonneg (fun b₁ _ => Finset.sum_nonneg (fun m _ =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg (m.divisors.card)) 2) (abs_nonneg _))))]
    exact le_trans h1 (le_of_eq h2)

lemma integrable_tau_cub_sum (x Pz : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => (∑ c ∈ Finset.Icc 1 x,
        ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u|) / u) volume a b := by
  refine intervalIntegrable_div_of_bounded' (C := (x : ℝ) * ((x : ℝ) ^ 3 * AcountAtilC x))
    ha hab ?_ ?_
  · exact Finset.measurable_sum _ (fun c _ => (measurable_Xf' x Pz c).abs.const_mul _)
  · intro u
    have h1 : (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |Xf x Pz c u|)
        ≤ ∑ c ∈ Finset.Icc 1 x, (x : ℝ) ^ 3 * AcountAtilC x := by
      refine Finset.sum_le_sum (fun c hc => ?_)
      have hc2 : ((c.divisors.card : ℝ)) ^ 3 ≤ (x : ℝ) ^ 3 := by
        have hτ : (c.divisors.card : ℝ) ≤ (x : ℝ) := by
          have hsub : c.divisors ⊆ Finset.Icc 1 x := by
            intro d hd
            rw [Nat.mem_divisors] at hd
            exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd.1 (by
                have := (Finset.mem_Icc.mp hc).1; omega),
              le_trans (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hc).1; omega) hd.1)
                (Finset.mem_Icc.mp hc).2⟩
          have hcard := Finset.card_le_card hsub
          rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
          exact_mod_cast hcard
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hτ 3
      exact mul_le_mul hc2 (abs_Xf_le_Acount x Pz c u) (abs_nonneg _)
        (by positivity)
    have h2 : (∑ c ∈ Finset.Icc 1 x, (x : ℝ) ^ 3 * AcountAtilC x)
        = (x : ℝ) * ((x : ℝ) ^ 3 * AcountAtilC x) := by
      rw [Finset.sum_const]
      simp only [smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      ring
    rw [abs_of_nonneg (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg (c.divisors.card)) 3) (abs_nonneg _)))]
    exact le_trans h1 (le_of_eq h2)

lemma integrable_Xsum_sum (x : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ m ∈ Finset.Icc 1 x,
        wc m * |Submission.ASP.Xsum atilc x m t (2 * t)|) / t) volume a b := by
  refine intervalIntegrable_div_of_bounded' (C := (x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x))
    ha hab ?_ ?_
  · exact Finset.measurable_sum _ (fun m _ =>
      ((Submission.ASP.measurable_Xsum atilc x m (by norm_num : (0:ℝ) < 2)).abs).const_mul _)
  · intro u
    have h1 : (∑ m ∈ Finset.Icc 1 x, wc m * |Submission.ASP.Xsum atilc x m u (2 * u)|)
        ≤ ∑ m ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 * AcountAtilC x := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      exact mul_le_mul (wc_le x m hm) (abs_Xsum_le_Acount x m u (2 * u)) (abs_nonneg _)
        (by positivity)
    have h2 : (∑ m ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 * AcountAtilC x)
        = (x : ℝ) * ((x : ℝ) ^ 2 * AcountAtilC x) := by
      rw [Finset.sum_const]
      simp only [smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      ring
    rw [abs_of_nonneg (Finset.sum_nonneg (fun m _ =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg (m.divisors.card)) 2) (abs_nonneg _)))]
    exact le_trans h1 (le_of_eq h2)

lemma integrable_const_div (C : ℝ) (hC : 0 ≤ C) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => C / u) volume a b :=
  intervalIntegrable_div_of_bounded' (C := C) ha hab measurable_const
    (fun u => le_of_eq (abs_of_nonneg hC))


end

end Work.FIChain
