/-
# `Submission.Work.FIChain.tail_integral_le` — the `log 2` tail integral bound

The tail `b₁ > Δπ` of the `Π`-removal (Rankin's trick, the `W₁` estimate (10.4) of the companion
paper's §10) is bounded by integrating the Rankin step against `dt/t`: every `n` contributing to
`Xf x Pz c u` comes with the window `u ∈ [n/2, n]`, i.e. `t ∈ [b₁n/2, b₁n]`, and
`∫_{b₁n/2}^{b₁n} dt/t = log 2`.  Summing over `n` (using monotonicity and additivity of the
integral, all functions being nonnegative) produces the factor `log 2` times the discrete mass
`∑_n ã(cn)`, which is the right-hand side of the target statement.
-/
import Mathlib
import Submission.Work.FIChain.TailDefs
import Submission.Work.FIChain.BpWinDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The index set of the `Π`-restricted window and the pointwise bound for `Xf` -/

/-- The `u`-independent index set of `Xf`: `n ∈ [1,x]` with `(n,Π) = 1` and `c n ≤ x`. -/
private def XfNset (x Pz c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun n => Work.FITop4.PiCond Pz n ∧ c * n ≤ x)

private lemma one_le_of_mem_XfNset {x Pz c n : ℕ} (h : n ∈ XfNset x Pz c) : 1 ≤ n := by
  rw [XfNset, Finset.mem_filter] at h
  exact (Finset.mem_Icc.mp h.1).1

private lemma cast_pos_of_mem_XfNset {x Pz c n : ℕ} (h : n ∈ XfNset x Pz c) :
    (0 : ℝ) < (n : ℝ) := by
  have h1 := one_le_of_mem_XfNset h
  exact_mod_cast (by omega : 0 < n)

/-- `Xf` as a sum over the `u`-independent index set `XfNset`, the window conditions being
carried by `if`s. -/
private lemma tail_Xf_eq_ite (x Pz c : ℕ) (u : ℝ) :
    Xf x Pz c u = ∑ n ∈ XfNset x Pz c,
      (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
        then (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) else 0) := by
  have hL : Xf x Pz c u = ∑ n ∈ Finset.Icc 1 x,
      (if c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u ∧ Work.FITop4.PiCond Pz n
        then (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) else 0) := by
    rw [Xf, Finset.sum_filter]
  have hR : (∑ n ∈ XfNset x Pz c,
        (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
          then (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) else 0))
      = ∑ n ∈ Finset.Icc 1 x,
        (if Work.FITop4.PiCond Pz n ∧ c * n ≤ x
          then (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
            then (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) else 0) else 0) := by
    rw [XfNset, Finset.sum_filter]
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : Work.FITop4.PiCond Pz n <;> by_cases h2 : c * n ≤ x <;>
    by_cases h3 : u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u <;>
    simp [h1, h2, h3, and_assoc, and_left_comm, and_comm]

/-- `|Xf x Pz c u|` is dominated by the windowed mass: the `n`-th summand contributes
`atilc (c n)` only for `u ∈ [n/2, n]`. -/
private lemma tail_abs_Xf_le_window (x Pz c : ℕ) (u : ℝ) :
    |Xf x Pz c u| ≤ ∑ n ∈ XfNset x Pz c,
      (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun _ => atilc (c * n)) u := by
  rw [tail_Xf_eq_ite]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  by_cases h3 : u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
  · rw [if_pos h3]
    have hmem : u ∈ Set.Icc ((n : ℝ) / 2) (n : ℝ) :=
      ⟨by linarith [h3.2], le_of_lt h3.1⟩
    rw [Set.indicator_of_mem hmem, abs_mul]
    calc |(ArithmeticFunction.moebius n : ℝ)| * |atilc (c * n)|
        ≤ 1 * |atilc (c * n)| :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
            (abs_nonneg _)
      _ = atilc (c * n) := by rw [one_mul, abs_of_nonneg (Work.FITop.atilFIa_nonneg _)]
  · rw [if_neg h3, abs_zero]
    exact Set.indicator_nonneg (fun _ _ => Work.FITop.atilFIa_nonneg _) u

/-- `|Xf x Pz c u|` is dominated by the full mass `∑_{n ∈ XfNset} ã(cn)`. -/
private lemma tail_abs_Xf_le_mass (x Pz c : ℕ) (u : ℝ) :
    |Xf x Pz c u| ≤ ∑ n ∈ XfNset x Pz c, atilc (c * n) := by
  refine (tail_abs_Xf_le_window x Pz c u).trans (Finset.sum_le_sum (fun n _ => ?_))
  by_cases h : u ∈ Set.Icc ((n : ℝ) / 2) (n : ℝ)
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    exact Work.FITop.atilFIa_nonneg _

/-- Measurability of `u ↦ Xf x Pz c u`. -/
private lemma tail_measurable_Xf (x Pz c : ℕ) : Measurable (fun u : ℝ => Xf x Pz c u) := by
  rw [show (fun u : ℝ => Xf x Pz c u) = fun u => ∑ n ∈ XfNset x Pz c,
      (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
        then (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) else 0) from by
    funext u; exact tail_Xf_eq_ite x Pz c u]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_const.mul measurable_id))

private lemma tail_measurable_Xf_comp (x Pz c b : ℕ) :
    Measurable (fun t : ℝ => Xf x Pz c (t / b)) :=
  (tail_measurable_Xf x Pz c).comp (measurable_id.div_const (b : ℝ))

/-! ## 2. General analytic helpers -/

/-- A measurable function `Φ` bounded by `C` gives an interval-integrable `u ↦ Φ u / u` on
`[a,b]` with `0 < a ≤ b`. -/
private lemma tail_intervalIntegrable_div_of_bounded {Φ : ℝ → ℝ} {a b C : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hm : Measurable Φ) (hC : ∀ u, |Φ u| ≤ C) :
    IntervalIntegrable (fun u => Φ u / u) volume a b := by
  constructor
  · refine IntegrableOn.of_bound (measure_Ioc_lt_top (a := a) (b := b)) ?_ (C / a) ?_
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

/-- The substitution `t = b u`: `∫_{lo}^{hi} f (t/b)/t dt = ∫_{lo/b}^{hi/b} f u/u du`. -/
private lemma tail_integral_div_comp_div (f : ℝ → ℝ) {b lo hi : ℝ} (hb : b ≠ 0) :
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

/-- Integrability of a single window piece `u ↦ 1_{[a/2,a]}(u)·A/u`. -/
private lemma tail_intervalIntegrable_indicator_Icc_div (A a : ℝ) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) :
    IntervalIntegrable (fun u : ℝ => (Set.Icc (a / 2) a).indicator (fun u => A / u) u)
      volume α β := by
  have hmeas : Measurable (fun u : ℝ => (Set.Icc (a / 2) a).indicator (fun _ => A) u) :=
    measurable_const.indicator measurableSet_Icc
  have hbd : ∀ u : ℝ, |(Set.Icc (a / 2) a).indicator (fun _ => A) u| ≤ |A| := by
    intro u
    by_cases h : u ∈ Set.Icc (a / 2) a
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, abs_zero]
      exact abs_nonneg A
  have h := tail_intervalIntegrable_div_of_bounded
    (Φ := fun u : ℝ => (Set.Icc (a / 2) a).indicator (fun _ => A) u) hα hαβ hmeas hbd
  refine IntervalIntegrable.congr (g := fun u : ℝ =>
    (Set.Icc (a / 2) a).indicator (fun u => A / u) u) ?_ h
  intro u _
  by_cases hmem : u ∈ Set.Icc (a / 2) a
  · simp only [Set.indicator_of_mem hmem]
  · simp only [Set.indicator_of_notMem hmem]
    simp

/-- The window integral bound: `∫_α^β 1_{[a/2,a]}(u)·A/u du ≤ A log 2` for `A ≥ 0`, `a > 0`. -/
private lemma tail_indicator_Icc_div_integral_le (A a α β : ℝ) (hA : 0 ≤ A) (ha : 0 < a)
    (hα : 0 < α) (hαβ : α ≤ β) :
    (∫ u in α..β, (Set.Icc (a / 2) a).indicator (fun u => A / u) u) ≤ A * Real.log 2 := by
  have h1 : (∫ u in α..β, (Set.Icc (a / 2) a).indicator (fun u => A / u) u)
      = A * ∫ u in α..β, (Set.Icc (a / 2) a).indicator (fun u => u⁻¹) u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    by_cases h : u ∈ Set.Icc (a / 2) a
    · simp only [Set.indicator_of_mem h]
      rw [div_eq_mul_inv]
    · simp only [Set.indicator_of_notMem h]
      simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ hA
  rw [intervalIntegral.integral_of_le hαβ, MeasureTheory.setIntegral_indicator measurableSet_Icc]
  have hmemnn : ∀ u ∈ Set.Icc (a / 2) a, (0 : ℝ) ≤ u⁻¹ := fun u hu =>
    inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le (by linarith) hu.1))
  have hintOn : IntegrableOn (fun u : ℝ => u⁻¹) (Set.Icc (a / 2) a) volume := by
    refine IntegrableOn.of_bound measure_Icc_lt_top ?_ (2 / a) ?_
    · exact measurable_inv.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu0 : 0 < u := lt_of_lt_of_le (by linarith) hu.1
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0), inv_eq_one_div]
      refine (one_div_le_one_div_of_le (by linarith) hu.1).trans (le_of_eq ?_)
      field_simp
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (a / 2) a)] (fun u : ℝ => u⁻¹) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall hmemnn
  have hle : (∫ u in Set.Ioc α β ∩ Set.Icc (a / 2) a, (fun u : ℝ => u⁻¹) u)
      ≤ ∫ u in Set.Icc (a / 2) a, (fun u : ℝ => u⁻¹) u :=
    MeasureTheory.setIntegral_mono_set hintOn hnonneg Set.inter_subset_right.eventuallyLE
  have heq : (∫ u in Set.Icc (a / 2) a, (fun u : ℝ => u⁻¹) u) = Real.log 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : a / 2 ≤ a),
      integral_inv_of_pos (by linarith) ha]
    rw [show a / (a / 2) = 2 by field_simp]
  exact hle.trans (le_of_eq heq)

/-! ## 3. The window integral bound for a single `Xf` sum -/

/-- Integrability of `t ↦ |Xf x Pz c (t/b₁)|/t` on `[lo,hi]`, `0 < lo ≤ hi`. -/
private lemma tail_intervalIntegrable_comp {x Pz c b₁ : ℕ} {lo hi : ℝ} (hlo : 0 < lo)
    (hlohi : lo ≤ hi) :
    IntervalIntegrable (fun t : ℝ => |Xf x Pz c (t / b₁)| / t) volume lo hi :=
  tail_intervalIntegrable_div_of_bounded hlo hlohi (tail_measurable_Xf_comp x Pz c b₁).abs
    (fun t => by simpa using tail_abs_Xf_le_mass x Pz c (t / b₁))

/-- Integrability of `t ↦ (∑_{b₁ ∈ s} |Xf x Pz (m b₁) (t/b₁)|)/t` on `[lo,hi]`, `0 < lo ≤ hi`. -/
private lemma tail_intervalIntegrable_sum_abs {x Pz : ℕ} {s : Finset ℕ} {m : ℕ} {lo hi : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    IntervalIntegrable (fun t : ℝ => (∑ b₁ ∈ s, |Xf x Pz (m * b₁) (t / b₁)|) / t)
      volume lo hi := by
  refine tail_intervalIntegrable_div_of_bounded
    (C := ∑ b₁ ∈ s, ∑ n ∈ XfNset x Pz (m * b₁), atilc (m * b₁ * n)) hlo hlohi ?_ ?_
  · exact Finset.measurable_sum _ (fun b₁ _ => (tail_measurable_Xf_comp x Pz (m * b₁) b₁).abs)
  · intro t
    rw [abs_of_nonneg (Finset.sum_nonneg (fun b₁ _ => abs_nonneg _))]
    exact Finset.sum_le_sum (fun b₁ _ => tail_abs_Xf_le_mass x Pz (m * b₁) (t / b₁))

/-- **The window integral bound**: `∫_{lo}^{hi} |Xf x Pz c (t/b₁)|/t dt ≤ log 2 · ∑_n ã(cn)`. -/
private lemma tail_integral_abs_Xf_le (x Pz c b₁ : ℕ) {lo hi : ℝ} (hlo : 0 < lo)
    (hlohi : lo ≤ hi) (hb₁ : 0 < b₁) :
    (∫ t in lo..hi, |Xf x Pz c (t / b₁)| / t)
      ≤ Real.log 2 * ∑ n ∈ XfNset x Pz c, atilc (c * n) := by
  have hb₁ne : ((b₁ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hb₁.ne'
  rw [tail_integral_div_comp_div (fun u => |Xf x Pz c u|) hb₁ne]
  have hb₁pos : (0 : ℝ) < (b₁ : ℝ) := by exact_mod_cast hb₁
  have hαpos : 0 < lo / (b₁ : ℝ) := div_pos hlo hb₁pos
  have hαβ : lo / (b₁ : ℝ) ≤ hi / (b₁ : ℝ) :=
    div_le_div_of_nonneg_right hlohi (le_of_lt hb₁pos)
  have hpt : ∀ u ∈ Set.Icc (lo / (b₁ : ℝ)) (hi / (b₁ : ℝ)),
      |Xf x Pz c u| / u ≤ ∑ n ∈ XfNset x Pz c,
        (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun u => atilc (c * n) / u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hαpos hu.1
    calc |Xf x Pz c u| / u
        ≤ (∑ n ∈ XfNset x Pz c,
              (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun _ => atilc (c * n)) u) / u :=
          div_le_div_of_nonneg_right (tail_abs_Xf_le_window x Pz c u) hu0.le
      _ = ∑ n ∈ XfNset x Pz c,
            (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun _ => atilc (c * n)) u / u :=
          Finset.sum_div _ _ _
      _ = ∑ n ∈ XfNset x Pz c,
            (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun u => atilc (c * n) / u) u := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          by_cases h : u ∈ Set.Icc ((n : ℝ) / 2) (n : ℝ)
          · simp only [Set.indicator_of_mem h]
          · simp only [Set.indicator_of_notMem h]
            simp
  have hint1 : IntervalIntegrable (fun u => |Xf x Pz c u| / u) volume
      (lo / (b₁ : ℝ)) (hi / (b₁ : ℝ)) :=
    tail_intervalIntegrable_div_of_bounded hαpos hαβ (tail_measurable_Xf x Pz c).abs
      (fun u => by simpa using tail_abs_Xf_le_mass x Pz c u)
  have hint2 : IntervalIntegrable (fun u => ∑ n ∈ XfNset x Pz c,
      (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun u => atilc (c * n) / u) u) volume
      (lo / (b₁ : ℝ)) (hi / (b₁ : ℝ)) :=
    IntervalIntegrable.congr (fun u _ => by simp only [Finset.sum_apply])
      (IntervalIntegrable.sum (XfNset x Pz c) (fun n _ =>
        tail_intervalIntegrable_indicator_Icc_div (atilc (c * n)) (n : ℝ) hαpos hαβ))
  calc (∫ u in lo / (b₁ : ℝ)..hi / (b₁ : ℝ), |Xf x Pz c u| / u)
      ≤ ∫ u in lo / (b₁ : ℝ)..hi / (b₁ : ℝ), ∑ n ∈ XfNset x Pz c,
          (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun u => atilc (c * n) / u) u :=
        intervalIntegral.integral_mono_on hαβ hint1 hint2 hpt
    _ = ∑ n ∈ XfNset x Pz c, ∫ u in lo / (b₁ : ℝ)..hi / (b₁ : ℝ),
          (Set.Icc ((n : ℝ) / 2) (n : ℝ)).indicator (fun u => atilc (c * n) / u) u :=
        intervalIntegral.integral_finsetSum (fun n _ =>
          tail_intervalIntegrable_indicator_Icc_div (atilc (c * n)) (n : ℝ) hαpos hαβ)
    _ ≤ ∑ n ∈ XfNset x Pz c, atilc (c * n) * Real.log 2 :=
        Finset.sum_le_sum (fun n hn =>
          tail_indicator_Icc_div_integral_le (atilc (c * n)) (n : ℝ) (lo / (b₁ : ℝ))
            (hi / (b₁ : ℝ)) (Work.FITop.atilFIa_nonneg _) (cast_pos_of_mem_XfNset hn) hαpos hαβ)
    _ = Real.log 2 * ∑ n ∈ XfNset x Pz c, atilc (c * n) := by
        rw [← Finset.sum_mul]; ring

/-! ## 4. Integrability of the two sides of the target inequality -/

/-- The triangle inequality at a fixed `t`. -/
private lemma tail_abs_sum_moebius_le (x Pz D m : ℕ) (t : ℝ) :
    |∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|
      ≤ ∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
          |Xf x Pz (m * b₁) (t / b₁)| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b₁ _ => ?_))
  rw [abs_mul]
  calc |(ArithmeticFunction.moebius b₁ : ℝ)| * |Xf x Pz (m * b₁) (t / b₁)|
      ≤ 1 * |Xf x Pz (m * b₁) (t / b₁)| :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
          (abs_nonneg _)
    _ = |Xf x Pz (m * b₁) (t / b₁)| := one_mul _

/-- A constant dominating both integrands on `[lo,hi]`. -/
private def tailC (x Pz D : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
    ∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
      ∑ n ∈ XfNset x Pz (m * b₁), atilc (m * b₁ * n)

/-- Integrability of the target's integrand. -/
private lemma tail_intervalIntegrable_LHS {x Pz D : ℕ} {lo hi : ℝ} (hlo : 0 < lo)
    (hlohi : lo ≤ hi) :
    IntervalIntegrable (fun t : ℝ => (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
      |∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t) volume lo hi := by
  refine tail_intervalIntegrable_div_of_bounded (C := tailC x Pz D) hlo hlohi ?_ ?_
  · refine Finset.measurable_sum _ (fun m _ => ?_)
    refine Measurable.const_mul (Finset.measurable_sum _ (fun b₁ _ => ?_)).abs _
    exact (tail_measurable_Xf_comp x Pz (m * b₁) b₁).const_mul _
  · intro t
    rw [abs_of_nonneg (Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (abs_nonneg _)))]
    simp only [tailC]
    calc (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          |∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|)
        ≤ ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
            |Xf x Pz (m * b₁) (t / b₁)| :=
          Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left
            (tail_abs_sum_moebius_le x Pz D m t) (by positivity))
      _ ≤ ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
            ∑ n ∈ XfNset x Pz (m * b₁), atilc (m * b₁ * n) :=
          Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun b₁ _ => tail_abs_Xf_le_mass x Pz (m * b₁) (t / b₁)))
            (by positivity))

/-- Integrability of the "sum of absolute values" integrand. -/
private lemma tail_intervalIntegrable_wsum {x Pz D : ℕ} {lo hi : ℝ} (hlo : 0 < lo)
    (hlohi : lo ≤ hi) :
    IntervalIntegrable (fun t : ℝ => (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
      ∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
        |Xf x Pz (m * b₁) (t / b₁)|) / t) volume lo hi := by
  refine tail_intervalIntegrable_div_of_bounded (C := tailC x Pz D) hlo hlohi ?_ ?_
  · refine Finset.measurable_sum _ (fun m _ => ?_)
    refine Measurable.const_mul (Finset.measurable_sum _ (fun b₁ _ => ?_)) _
    exact (tail_measurable_Xf_comp x Pz (m * b₁) b₁).abs
  · intro t
    rw [abs_of_nonneg (Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun b₁ _ => abs_nonneg _))))]
    simp only [tailC]
    exact Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun b₁ _ => tail_abs_Xf_le_mass x Pz (m * b₁) (t / b₁)))
      (by positivity))

/-! ## 5. The target theorem -/

theorem tail_integral_le (x Pz D : ℕ) (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    (∫ t in lo..hi,
        (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          |∑ b₁ ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
            (ArithmeticFunction.moebius b₁ : ℝ) * Work.FIChain.Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ Real.log 2 *
          ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
            ∑ b₁ ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
              ∑ n ∈ (Finset.Icc 1 x).filter
                  (fun n => Work.FITop4.PiCond Pz n ∧ m * b₁ * n ≤ x),
                Work.FIChain.atilc (m * b₁ * n) := by
  set B : Finset ℕ := ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁) with hB
  show (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
        |∑ b₁ ∈ B, (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ Real.log 2 * ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, ∑ n ∈ XfNset x Pz (m * b₁), atilc (m * b₁ * n)
  have hA : (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
        |∑ b₁ ∈ B, (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ ∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, |Xf x Pz (m * b₁) (t / b₁)|) / t := by
    refine intervalIntegral.integral_mono_on hlohi ?_ ?_ (fun t ht => ?_)
    · exact tail_intervalIntegrable_LHS (x := x) (Pz := Pz) (D := D) hlo hlohi
    · exact tail_intervalIntegrable_wsum (x := x) (Pz := Pz) (D := D) hlo hlohi
    · exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun m _ =>
        mul_le_mul_of_nonneg_left (tail_abs_sum_moebius_le x Pz D m t) (by positivity)))
        (le_of_lt (lt_of_lt_of_le hlo ht.1))
  have hB' : (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, |Xf x Pz (m * b₁) (t / b₁)|) / t)
      = ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, ∫ t in lo..hi, |Xf x Pz (m * b₁) (t / b₁)| / t := by
    have hfun : (fun t : ℝ => (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
            ∑ b₁ ∈ B, |Xf x Pz (m * b₁) (t / b₁)|) / t)
        = fun t => ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
            ((∑ b₁ ∈ B, |Xf x Pz (m * b₁) (t / b₁)|) / t) := by
      funext t
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun m _ => by rw [mul_div_assoc])
    rw [hfun]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [show (fun t : ℝ => (∑ b₁ ∈ B, |Xf x Pz (m * b₁) (t / b₁)|) / t)
          = fun t => ∑ b₁ ∈ B, |Xf x Pz (m * b₁) (t / b₁)| / t from by
        funext t; rw [Finset.sum_div]]
      rw [intervalIntegral.integral_finsetSum]
      · intro b₁ _
        exact tail_intervalIntegrable_comp (x := x) (Pz := Pz) (c := m * b₁) (b₁ := b₁) hlo hlohi
    · intro m _
      exact (tail_intervalIntegrable_sum_abs (x := x) (Pz := Pz) (s := B) (m := m) hlo hlohi).const_mul _
  have hC : (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, ∫ t in lo..hi, |Xf x Pz (m * b₁) (t / b₁)| / t)
      ≤ ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, (Real.log 2 * ∑ n ∈ XfNset x Pz (m * b₁), atilc (m * b₁ * n)) := by
    refine Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Finset.sum_le_sum (fun b₁ hb₁ => ?_)
    have hDb₁ : D < b₁ := by
      have h := hb₁; rw [hB, Finset.mem_filter] at h; exact h.2
    exact tail_integral_abs_Xf_le x Pz (m * b₁) b₁ hlo hlohi (by omega)
  have hD : (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, (Real.log 2 * ∑ n ∈ XfNset x Pz (m * b₁), atilc (m * b₁ * n)))
      = Real.log 2 * ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ B, ∑ n ∈ XfNset x Pz (m * b₁), atilc (m * b₁ * n) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine Finset.sum_congr rfl (fun b₁ _ => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  exact hA.trans (hB'.trans_le (hC.trans_eq hD))

end

end Work.FIChain
