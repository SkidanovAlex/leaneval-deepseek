/-
# The increasing rearrangement and the paper's display `(maxintegral)`

Calegari–Dimitrov–Tang's §"Variants of the Nevanlinna growth characteristic" introduces the
*increasing rearrangement* `g*` of a measurable function `g` on `(0,1)` by

`g*(t) := inf { s : P(g > s) ≤ t }`

and observes (their display `(maxintegral)`)

`∫_0^1 2t·g*(t) dt = ∫_0^1 ∫_0^1 max(g(s), g(t)) ds dt`.

This module formalises that identity, and in fact proves both sides equal the "energy"

`∫_0^∞ (1 - (1 - F(r))²) dr`,  where `F(r) = μ {x | r < f x}`

is the (complementary) distribution function of `f` under the probability measure `μ` — so that
the identity is the statement that the *max-energy* depends only on the law of `f`, and that the
rearrangement realises that law.

## A correction of the paper's convention

With the paper's literal definition `g*(t) := inf_s { P(g > s) ≤ t }` the function `g*` is
*decreasing*, and `∫_0^1 2t·g*(t)dt` is then **not** equal to `∫∫ max(g,g)`: for the two-valued
example `g = 1_A` with `P(A) = 1/2` one gets `∫_0^1 2t g*(t)dt = 1/4` while
`∫∫max(g,g) = 3/4`.  The correct (standard) quantile function, which is increasing, is
`g*(t) := inf { s : P(g > s) ≤ 1 - t }`.  We implement that one
(`rearr μ f t = sSup {y | ofReal (1-t) < μ {x | y < f x}}` — the sSup form is equivalent, and
handler for Lean).

## Main results

* `lt_rearr_iff` — the characterisation `r < g*(t) ↔ 1 - t < μ {f > r}`;
* `integral_two_mul_rearr` — the integral side:
  `∫_0^1 2t·g*(t)dt = ∫_0^∞ (1 - (1-F r)²) dr`;
* `integral_integral_max` — the product side:
  `∫∫ max(f s, f t) dμ dμ = ∫_0^∞ (1 - (1-F r)²) dr`;
* `integral_two_mul_rearr_eq_integral_integral_max` — the paper's display `(maxintegral)`.
-/
import Mathlib

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Submission.CDT.Rearr

variable {α : Type*} [MeasurableSpace α]

/-- The increasing rearrangement (quantile function) of `f` with respect to `μ`: the smallest `y`
whose superlevel set `{f > y}` has `μ`-measure at most `1 - t`. -/
noncomputable def rearr (μ : Measure α) (f : α → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  sSup {y : ℝ≥0∞ | ENNReal.ofReal (1 - t) < μ {x | y < f x}}

/-- `y ↦ μ {f > y}` is antitone. -/
theorem meas_gt_antitone (μ : Measure α) (f : α → ℝ≥0∞) :
    Antitone fun y : ℝ≥0∞ => μ {x | y < f x} :=
  fun _a _b hab => measure_mono fun _x hx => lt_of_le_of_lt hab hx

/-- Continuity from below, along a decreasing sequence. -/
theorem tendsto_meas_gt (μ : Measure α) {f : α → ℝ≥0∞} {a : ℕ → ℝ≥0∞} {b : ℝ≥0∞}
    (ha : Antitone a) (hb : (⨅ n, a n) = b) :
    Tendsto (fun n => μ {x | a n < f x}) atTop (𝓝 (μ {x | b < f x})) := by
  have hmono : Monotone fun n => {x | a n < f x} := by
    intro m n hmn _x hx
    exact lt_of_le_of_lt (ha hmn) hx
  have hUnion : (⋃ n, {x | a n < f x}) = {x | b < f x} := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      rw [← hb]
      exact lt_of_le_of_lt (iInf_le a n) hn
    · intro hx
      rw [← hb] at hx
      obtain ⟨n, hn⟩ := iInf_lt_iff.mp hx
      exact ⟨n, hn⟩
  rw [← hUnion]
  exact tendsto_measure_iUnion_atTop hmono

/-- The rearrangement is monotone in `t`. -/
theorem rearr_mono (μ : Measure α) (f : α → ℝ≥0∞) : Monotone fun t => rearr μ f t := by
  intro s t hst
  refine sSup_le_sSup ?_
  intro y hy
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) hy

/-- The infimum over `n` of `((n+1) : ℝ≥0∞)⁻¹` is `0`. -/
theorem iInf_nat_succ_inv : (⨅ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) = 0 := by
  rw [iInf_eq_of_forall_ge_of_forall_gt_exists_lt]
  · intro n; exact zero_le
  · intro w hw
    have htend : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hmem : Iio w ∈ 𝓝 (0 : ℝ≥0∞) := (isOpen_Iio).mem_nhds hw
    obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually hmem)
    exact ⟨N, hN N le_rfl⟩

/-- **The characterisation of the rearrangement.**  For a probability measure `μ` and `0 ≤ r`,
`r < g*(t) ↔ 1 - t < μ {f > r}`. -/
theorem lt_rearr_iff (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {r t : ℝ}
    (hr : 0 ≤ r) :
    ENNReal.ofReal r < rearr μ f t ↔
      ENNReal.ofReal (1 - t) < μ {x | ENNReal.ofReal r < f x} := by
  constructor
  · intro h
    obtain ⟨c, hc, hrc⟩ := lt_sSup_iff.mp h
    simp only [mem_ofPred_eq] at hc
    have hle : μ {x | c < f x} ≤ μ {x | ENNReal.ofReal r < f x} := meas_gt_antitone μ f hrc.le
    exact lt_of_lt_of_le hc hle
  · intro h
    set a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal r + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ with ha
    have hanti : Antitone a := by
      intro m n hmn
      simp only [ha]
      exact add_le_add le_rfl (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.succ_le_succ hmn))
    have hinf : (⨅ n, a n) = ENNReal.ofReal r := by
      simp only [ha]
      rw [← ENNReal.add_iInf, iInf_nat_succ_inv, add_zero]
    have htend : Tendsto (fun n => μ {x | a n < f x}) atTop
        (𝓝 (μ {x | ENNReal.ofReal r < f x})) := tendsto_meas_gt (f := f) μ hanti hinf
    have hev : ∀ᶠ n in atTop, ENNReal.ofReal (1 - t) < μ {x | a n < f x} :=
      (tendsto_order.1 htend).1 _ h
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine lt_sSup_iff.mpr ⟨a N, ?_, ?_⟩
    · exact hN N le_rfl
    · simp only [ha]
      exact ENNReal.lt_add_right ENNReal.ofReal_ne_top (by
        rw [ENNReal.inv_ne_zero]; exact ENNReal.natCast_ne_top _)

/-- `ofReal` applied pointwise. -/
noncomputable def ofRealFn (f : α → ℝ) : α → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)

/-- The rearrangement of a real-valued function `f` (viewed through `ofReal`), as a real number. -/
noncomputable def fstar (μ : Measure α) (f : α → ℝ) (t : ℝ) : ℝ :=
  (rearr μ (ofRealFn f) t).toReal

/-- The complementary distribution function `F(r) = μ {f > r}` of a real-valued `f`. -/
noncomputable def distr (μ : Measure α) (f : α → ℝ) (r : ℝ) : ℝ := (μ {x | r < f x}).toReal

theorem distr_nonneg (μ : Measure α) (f : α → ℝ) (r : ℝ) : 0 ≤ distr μ f r :=
  ENNReal.toReal_nonneg

theorem distr_le_one (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (r : ℝ) :
    distr μ f r ≤ 1 := by
  have h : μ {x | r < f x} ≤ 1 := by
    have := measure_mono (μ := μ) (Set.subset_univ {x | r < f x})
    simpa using this
  calc distr μ f r = (μ {x | r < f x}).toReal := rfl
    _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) h
    _ = 1 := by simp

theorem distr_antitone (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) :
    Antitone (distr μ f) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun x hx => lt_of_le_of_lt hab hx)

theorem rearr_le_of_le {μ : Measure α} {f : α → ℝ≥0∞} {C : ℝ≥0∞} (hC : ∀ x, f x ≤ C)
    (t : ℝ) : rearr μ f t ≤ C := by
  refine sSup_le fun y hy => ?_
  by_contra h
  rw [not_le] at h
  have hempty : {x : α | y < f x} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact le_trans (hC x) h.le
  simp only [mem_ofPred_eq] at hy
  rw [hempty, measure_empty] at hy
  exact absurd hy (not_lt.mpr zero_le)

/-- The characterisation of `fstar` in real terms. -/
theorem lt_fstar_iff (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} {C : ℝ}
    (hC : ∀ x, f x ≤ C) {r t : ℝ} (hr : 0 ≤ r) (ht : t ≤ 1) :
    r < fstar μ f t ↔ 1 - t < distr μ f r := by
  have hne : rearr μ (ofRealFn f) t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (rearr_le_of_le (f := ofRealFn f) (C := ENNReal.ofReal C)
        (fun x => ENNReal.ofReal_le_ofReal (hC x)) t)
  rw [fstar, ← ENNReal.ofReal_lt_iff_lt_toReal hr hne, lt_rearr_iff μ hr]
  have hset : {x : α | ENNReal.ofReal r < ofRealFn f x} = {x : α | r < f x} := by
    ext x
    simp only [ofRealFn]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr
  rw [hset]
  exact ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top _ _)

/-! ### The two halves of the display `(maxintegral)` -/

/-- The bridge between the Lebesgue integral of `ofReal ∘ φ` over an interval and the (Bochner)
interval integral of `φ`. -/
theorem toReal_lintegral_Ioc_ofReal {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ∀ t ∈ Set.Ioc a b, 0 ≤ φ t) (hint : IntegrableOn φ (Set.Ioc a b) volume) :
    (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (φ t)).toReal = ∫ t in a..b, φ t := by
  have h := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioc a b)) hint
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => hφ t ht))
  rw [← h, ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Ioc fun t ht => hφ t ht),
    intervalIntegral.integral_of_le hab]

/-- The increasing rearrangement of a bounded measurable function is measurable. -/
theorem measurable_fstar (μ : Measure α) {f : α → ℝ} {C : ℝ} (hC : ∀ x, f x ≤ C) :
    Measurable fun t => fstar μ f t :=
  ENNReal.measurable_toReal.comp (rearr_mono μ (ofRealFn f)).measurable

theorem fstar_nonneg (μ : Measure α) (f : α → ℝ) (t : ℝ) : 0 ≤ fstar μ f t :=
  ENNReal.toReal_nonneg

/-- The rearrangement of a function bounded above by `C ≥ 0` is bounded above by `C`. -/
theorem fstar_le (μ : Measure α) {f : α → ℝ} {C : ℝ} (hC : ∀ x, f x ≤ C) (hC0 : 0 ≤ C)
    (t : ℝ) : fstar μ f t ≤ C := by
  have h := rearr_le_of_le (μ := μ) (f := ofRealFn f) (C := ENNReal.ofReal C)
    (fun x => ENNReal.ofReal_le_ofReal (hC x)) t
  calc fstar μ f t = (rearr μ (ofRealFn f) t).toReal := rfl
    _ ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = C := ENNReal.toReal_ofReal hC0

/-- The weight `2t dt` on `(0,1]` as a density measure. -/
noncomputable def weightMeasure : Measure ℝ :=
  (volume.withDensity fun t : ℝ => ENNReal.ofReal (2 * t)).restrict (Set.Ioc 0 1)

theorem weightMeasure_def : weightMeasure
    = (volume.withDensity fun t : ℝ => ENNReal.ofReal (2 * t)).restrict (Set.Ioc 0 1) := rfl

instance : IsFiniteMeasure weightMeasure := ⟨by
  rw [weightMeasure_def, Measure.restrict_apply (s := Set.Ioc 0 1) (t := Set.univ)
      MeasurableSet.univ,
    Set.univ_inter, withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal]
  · exact ENNReal.ofReal_lt_top
  · exact (continuous_const.mul continuous_id : Continuous fun t : ℝ => 2 * t).integrableOn_Icc.mono_set
      fun t ht => ⟨ht.1.le, ht.2⟩
  · exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => by
        show (0:ℝ) ≤ 2 * t
        linarith [ht.1])⟩

/-- The measure, under the weight `2t dt` on `(0,1]`, of the superlevel set of the rearrangement. -/
theorem weightMeasure_real_lt_fstar (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    {C : ℝ} (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) {r : ℝ} (hr : 0 < r) :
    weightMeasure.real {t : ℝ | r < fstar μ f t} = 1 - (1 - distr μ f r) ^ 2 := by
  have hF0 : 0 ≤ distr μ f r := distr_nonneg μ f r
  have hF1 : distr μ f r ≤ 1 := distr_le_one μ f r
  have hmeas : MeasurableSet {t : ℝ | r < fstar μ f t} :=
    measurableSet_lt measurable_const (measurable_fstar μ hC)
  have hset : {t : ℝ | r < fstar μ f t} ∩ Set.Ioc 0 1
      = Set.Ioc (1 - distr μ f r) 1 := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc]
    constructor
    · rintro ⟨ht, ht0, ht1⟩
      have := (lt_fstar_iff μ hC hr.le ht1).mp ht
      exact ⟨by linarith, ht1⟩
    · rintro ⟨ht, ht1⟩
      exact ⟨(lt_fstar_iff μ hC hr.le ht1).mpr (by linarith), by linarith, ht1⟩
  rw [Measure.real_def, weightMeasure_def, Measure.restrict_apply hmeas, hset,
    withDensity_apply _ measurableSet_Ioc,
    toReal_lintegral_Ioc_ofReal (by linarith) (fun t ht => by linarith [ht.1]) ?_]
  · rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  · have hi := (continuous_const.mul continuous_id : Continuous fun t : ℝ => 2 * t).intervalIntegrable
      (μ := volume) (1 - distr μ f r) 1
    rwa [intervalIntegrable_iff, Set.uIoc_of_le (by linarith)] at hi

/-- The density bridge: integrating against `2t dt` on `(0,1]` is the interval integral. -/
theorem integral_weightMeasure (h : ℝ → ℝ) :
    ∫ t, h t ∂weightMeasure = ∫ t in (0:ℝ)..1, 2 * t * h t := by
  rw [weightMeasure_def, restrict_withDensity measurableSet_Ioc,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [smul_eq_mul, ENNReal.toReal_ofReal (by linarith [ht.1.le])]

/-- **The integral side of the display `(maxintegral)`**: the increase `2t·g*(t)` of the
rearrangement integrates to `∫_0^∞ (1 - (1 - F(r))²) dr`, a functional of the law of `f` alone. -/
theorem integral_two_mul_fstar (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (h0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C) (hC0 : 0 ≤ C) :
    ∫ t in (0:ℝ)..1, 2 * t * fstar μ f t
      = ∫ r in Set.Ioi 0, (1 - (1 - distr μ f r) ^ 2) := by
  have hbound : ∀ t, ‖fstar μ f t‖ ≤ max C 0 := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (fstar_nonneg μ f t)]
    exact le_trans (fstar_le μ hC hC0 t) (le_max_left _ _)
  have hint : Integrable (fun t => fstar μ f t) weightMeasure :=
    Integrable.of_bound ((measurable_fstar μ hC).aestronglyMeasurable) _
      (Eventually.of_forall hbound)
  have hlc := hint.integral_eq_integral_meas_lt (Eventually.of_forall fun t => fstar_nonneg μ f t)
  rw [← integral_weightMeasure (fstar μ f), hlc]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
  exact weightMeasure_real_lt_fstar μ h0 hC hr

/-- The elementary fact that the rearrangement preserves the expected maximum: for a monotone
function the increase of `2t·h(t)` is the double integral of the maximum. -/
theorem integrable_max_prod (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {C : ℝ} (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    Integrable (fun p : α × α => max (f p.1) (f p.2)) (μ.prod μ) := by
  refine Integrable.of_bound ?_ (max C 0) (Eventually.of_forall fun p => ?_)
  · exact (((hf.comp measurable_fst).max (hf.comp measurable_snd))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_of_le_left (h0 p.1))]
    exact le_trans (max_le (hC p.1) (hC p.2)) (le_max_left _ _)

/-- The measure of the "at least one coordinate exceeds `r`" event under `μ ⊗ μ`. -/
theorem measureReal_prod_max_gt (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {r : ℝ} :
    (μ.prod μ).real {p : α × α | r < max (f p.1) (f p.2)}
      = 1 - (1 - distr μ f r) ^ 2 := by
  have hAm : MeasurableSet {x : α | r < f x} := measurableSet_lt measurable_const hf
  have hmeas : MeasurableSet {p : α × α | r < max (f p.1) (f p.2)} :=
    measurableSet_lt measurable_const ((hf.comp measurable_fst).max (hf.comp measurable_snd))
  have hset : {p : α × α | r < max (f p.1) (f p.2)}ᶜ
      = {x : α | r < f x}ᶜ ×ˢ {x : α | r < f x}ᶜ := by
    ext p
    simp only [mem_compl_iff, mem_prod, mem_ofPred_eq, not_lt, max_le_iff]
  have hcompl : μ.real {x : α | r < f x}ᶜ = 1 - distr μ f r := by
    rw [measureReal_compl hAm, Measure.real_def, measure_univ, distr, Measure.real_def]
    norm_num
  have huniv : (μ.prod μ).real univ = 1 := by
    rw [Measure.real_def, measure_univ]; norm_num
  have hkey : (μ.prod μ).real ({p : α × α | r < max (f p.1) (f p.2)})ᶜ
      = (1 - distr μ f r) ^ 2 := by
    rw [hset, measureReal_prod_prod, hcompl]
    ring
  calc (μ.prod μ).real {p : α × α | r < max (f p.1) (f p.2)}
      = (μ.prod μ).real univ
          - (μ.prod μ).real ({p : α × α | r < max (f p.1) (f p.2)})ᶜ := by
        have h := measureReal_compl (μ := μ.prod μ) hmeas.compl
        rwa [compl_compl] at h
    _ = 1 - (1 - distr μ f r) ^ 2 := by rw [huniv, hkey]

/-- **The product side of the display `(maxintegral)`**. -/
theorem integral_integral_max (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C) :
    ∫ s, ∫ t, max (f s) (f t) ∂μ ∂μ
      = ∫ r in Set.Ioi 0, (1 - (1 - distr μ f r) ^ 2) := by
  have hint := integrable_max_prod μ hf h0 hC
  rw [← integral_prod _ hint]
  rw [hint.integral_eq_integral_meas_lt
    (Eventually.of_forall fun p => le_max_of_le_left (h0 p.1))]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
  exact measureReal_prod_max_gt μ hf

/-- **Calegari–Dimitrov–Tang's display `(maxintegral)`**: the weighted integral of the increasing
rearrangement of a bounded nonnegative function is the double integral of the maximum. -/
theorem integral_two_mul_fstar_eq_integral_integral_max (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C)
    (hC0 : 0 ≤ C) :
    ∫ t in (0:ℝ)..1, 2 * t * fstar μ f t = ∫ s, ∫ t, max (f s) (f t) ∂μ ∂μ :=
  (integral_two_mul_fstar μ h0 hC hC0).trans (integral_integral_max μ hf h0 hC).symm

end Submission.CDT.Rearr
