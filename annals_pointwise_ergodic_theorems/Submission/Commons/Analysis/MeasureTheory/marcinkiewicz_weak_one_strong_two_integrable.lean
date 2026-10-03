import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_banach

/-!
# Marcinkiewicz interpolation, integrable form

This is the version of the Marcinkiewicz interpolation theorem needed by
`annals_pointwise_ergodic_theorems`: a `T` which is additive on *integrable* functions,
weak type `(1,1)` with constant `A₀` on integrable functions and strong type `(2,2)` with
constant `A₁` on integrable functions, is strong type `(p,p)` for `1 < p < 2`.

It is proved by re-running the truncation argument of
`Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_banach`, but tracking that all
functions to which `hadd`/`hweak`/`hstrong` are applied are truncations of an integrable function
(hence integrable).  The measurability hypothesis `AEMeasurable (T f)` of the Banach version is
not needed: the layer-cake step is done with the `innerTail` of the (possibly non-measurable)
function `‖T f‖`.
-/

open MeasureTheory Measure Filter Set
open scoped ENNReal Topology

namespace Commons.Analysis.MeasureTheory

/-! ## Integrability of truncations of an integrable function -/

/-- The level set `{x | ofReal t < ‖f x‖ₑ}` is a.e.-measurable when `f` is a.e.-strongly
measurable. -/
lemma nullMeasurableSet_ofReal_lt_enorm {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : AEStronglyMeasurable f μ) (t : ℝ) :
    NullMeasurableSet {x | ENNReal.ofReal t < ‖f x‖ₑ} μ := by
  have hnorm : AEStronglyMeasurable (fun x => ‖f x‖) μ := hf.norm
  have h1 : AEMeasurable (fun x => ENNReal.ofReal ‖f x‖) μ :=
    hnorm.aemeasurable.ennreal_ofReal
  have h3 := h1.nullMeasurableSet_preimage (s := Set.Ioi (ENNReal.ofReal t)) measurableSet_Ioi
  rw [show (fun x => ENNReal.ofReal ‖f x‖) ⁻¹' Set.Ioi (ENNReal.ofReal t)
        = {x | ENNReal.ofReal t < ‖f x‖ₑ} from by
      ext x; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, ofReal_norm]] at h3
  exact h3

/-- The indicator of an a.e.-measurable set times an integrable function is integrable. -/
lemma integrable_indicator_of_nullMeasurableSet {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {s : Set α} (hf : Integrable f μ) (hs : NullMeasurableSet s μ) :
    Integrable (s.indicator f) μ := by
  refine Integrable.mono' hf.norm (hf.aestronglyMeasurable.indicator₀ hs) (Eventually.of_forall fun x => ?_)
  rw [norm_indicator_eq_indicator_norm]
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- The high truncation of an integrable function is integrable. -/
lemma integrable_indicator_ofReal_lt_enorm {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : Integrable f μ) (t : ℝ) :
    Integrable (Set.indicator {x | ENNReal.ofReal t < ‖f x‖ₑ} f) μ :=
  integrable_indicator_of_nullMeasurableSet hf
    (nullMeasurableSet_ofReal_lt_enorm hf.aestronglyMeasurable t)

/-- The low truncation of an integrable function is integrable. -/
lemma integrable_indicator_ofReal_lt_enorm_compl {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : Integrable f μ) (t : ℝ) :
    Integrable (Set.indicator {x | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ f) μ :=
  integrable_indicator_of_nullMeasurableSet hf
    ((nullMeasurableSet_ofReal_lt_enorm hf.aestronglyMeasurable t).compl)

lemma high_pointwise_integrable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} {A0 : ℝ} (hA0 : 0 < A0) {p : ℝ}
    (hp1 : 1 < p)
    {T : (α → E) → (β → E)} {f : α → E} (hf : Integrable f μ)
    (hweak : ∀ (g : α → E) (lam : ℝ), Integrable g μ → 0 < lam →
      ν {x : β | lam < ‖T g x‖} ≤ ENNReal.ofReal (A0 / lam) * eLpNorm g 1 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      ν {a : β | t / 2 < ‖T (Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} f) a‖}
      ≤ ENNReal.ofReal (6 * A0 * t ^ (p - 2)) *
          (∫⁻ s in Set.Ioi (t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := by
  set g : α → E := Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} f with hg
  have hgi : Integrable g μ := by rw [hg]; exact integrable_indicator_ofReal_lt_enorm hf t
  have h1 : ν {a : β | t / 2 < ‖T g a‖} ≤ ENNReal.ofReal (A0 / (t/2)) * eLpNorm g 1 μ :=
    hweak g (t/2) hgi (by positivity)
  have h2 : eLpNorm g 1 μ
      = ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable]
    refine lintegral_congr fun x => ?_
    have h3 : ‖g x‖ₑ
        = Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x := by
      show ‖Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} f x‖ₑ = _
      exact enorm_indicator_eq_indicator_enorm f x
    rw [h3]
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


lemma low_pointwise_innerTail_integrable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} {A1 : ℝ}
    (hA1 : 0 < A1) {p : ℝ} (hp1 : 1 < p)
    {T : (α → E) → (β → E)} {f : α → E} (hf : Integrable f μ)
    (hstrong : ∀ g : α → E, Integrable g μ → eLpNorm (T g) 2 ν ≤ ENNReal.ofReal A1 * eLpNorm g 2 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      innerTail ν (fun a => ‖T (Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ f) a‖ₑ) (t / 2)
      ≤ ENNReal.ofReal (4 * A1 ^ 2 * t ^ (p - 3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t ^ 2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
  set h : α → E := Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ f with hh
  have hhi : Integrable h μ := by rw [hh]; exact integrable_indicator_ofReal_lt_enorm_compl hf t
  have h2t : (2:ℝ≥0∞).toReal = (2:ℝ) := by norm_num
  have hcheb : ENNReal.ofReal (t/2)^(2:ℝ) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ ∫⁻ x, ‖T h x‖ₑ ^ (2:ℝ) ∂ν :=
    pow_mul_innerTail_le (μ := ν) (W := fun x => ‖T h x‖ₑ) (u := t/2) (p := 2)
      (by positivity) (by norm_num)
  have hsquare : ENNReal.ofReal (t/2) ^ (2:ℝ) = ENNReal.ofReal ((t/2)^2) := by
    rw [rpow_two_eq, ← ENNReal.ofReal_pow (by positivity)]
  have heLph : (eLpNorm h 2 μ) ^ (2:ℝ) = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
      hhi.aestronglyMeasurable]
    simp_rw [h2t]
    rw [← ENNReal.rpow_mul, show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  have heLpTh : ∫⁻ x, ‖T h x‖ₑ ^ (2:ℝ) ∂ν ≤ (eLpNorm (T h) 2 ν) ^ (2:ℝ) := by
    by_cases hTh : AEStronglyMeasurable (T h) ν
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hTh]
      simp_rw [h2t]
      rw [← ENNReal.rpow_mul, show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]
    · rw [eLpNorm_of_not_aestronglyMeasurable hTh, ENNReal.top_rpow_of_pos (by norm_num)]
      exact le_top
  have hne0 : ENNReal.ofReal ((t/2)^2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hnetop : ENNReal.ofReal ((t/2)^2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hcheb' : ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ eLpNorm (T h) 2 ν ^ (2:ℝ) := by
    rw [← hsquare]
    exact hcheb.trans heLpTh
  have hstrong' : (eLpNorm (T h) 2 ν) ^ (2:ℝ)
      ≤ ENNReal.ofReal (A1^2) * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by
    calc (eLpNorm (T h) 2 ν) ^ (2:ℝ) ≤ (ENNReal.ofReal A1 * eLpNorm h 2 μ) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (hstrong h hhi) (by norm_num)
      _ = (ENNReal.ofReal A1) ^ (2:ℝ) * (eLpNorm h 2 μ) ^ (2:ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by rw [heLph, ofReal_sq A1 hA1.le]
  have hmain : innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
          (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by
    have hkey : ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
        ≤ ENNReal.ofReal ((t/2)^2) *
            ((ENNReal.ofReal ((t/2)^2))⁻¹ *
              (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := by
      calc ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
          ≤ ENNReal.ofReal (A1^2) * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := hcheb'.trans hstrong'
        _ = ENNReal.ofReal ((t/2)^2) *
              ((ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := by
            nth_rewrite 1 [← mul_assoc]
            rw [ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
    calc innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
        = (ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
      _ ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal ((t/2)^2) *
              ((ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ))) :=
          mul_le_mul_right hkey _
      _ = _ := by
          nth_rewrite 1 [← mul_assoc]
          rw [ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
  have hL : (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)
      = ∫⁻ x, Set.indicator {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal t} (fun x => ‖f x‖ₑ ^ 2) x ∂μ := by
    refine lintegral_congr fun x => ?_
    have hset : {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ = {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal t} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have h1 : ‖h x‖ₑ
        = Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ (fun x => ‖f x‖ₑ) x := by
      show ‖Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ f x‖ₑ = _
      exact enorm_indicator_eq_indicator_enorm f x
    rw [h1, hset]
    exact banach_trunc_sq (fun x => ‖f x‖ₑ) _ x
  have hlow := lintegral_indicator_low_le (μ := μ) (W := fun x => ‖f x‖ₑ) ht
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
  calc ENNReal.ofReal (t ^ (p - 1)) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
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
 

/-- `T f` is a.e. strongly measurable for every integrable `f ∈ L^p` (`1 < p < 2`): the low
truncations of `f` are integrable and in `L²`, so their images are a.e. strongly measurable, and
they converge to `T f` in measure by the weak `(1,1)` bound on the high truncations. -/
lemma integrable_aestronglyMeasurable_T {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}
    (T : (α → E) → (β → E))
    (hadd : ∀ f g : α → E, Integrable f μ → Integrable g μ → T (f + g) = T f + T g)
    {A0 A1 : ℝ}
    (hweak : ∀ (f : α → E) (lam : ℝ), Integrable f μ → 0 < lam →
      ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) * eLpNorm f 1 μ)
    (hstrong : ∀ f : α → E, Integrable f μ → eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * eLpNorm f 2 μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {f : α → E} (hint : Integrable f μ)
    (hfin : eLpNorm f (ENNReal.ofReal p) μ ≠ ∞) :
    AEStronglyMeasurable (T f) ν := by
  have hp0 : 0 < p := by linarith
  have hfm : AEStronglyMeasurable f μ := hint.aestronglyMeasurable
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ with hI
  have hIfin : I ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top (lt_top_iff_ne_top.mpr hfin)
    rw [ENNReal.toReal_ofReal hp0.le] at h
    exact h.ne
  set c : ℕ → ℝ := fun n => (n:ℝ) + 1 with hcdef
  have hc : ∀ n, 0 < c n := fun n => by positivity
  set S : ℕ → Set α := fun n => {x | ENNReal.ofReal (c n) < ‖f x‖ₑ} with hSdef
  set g : ℕ → α → E := fun n => (S n).indicator f with hgdef
  set h : ℕ → α → E := fun n => (S n)ᶜ.indicator f with hhdef
  have hgi : ∀ n, Integrable (g n) μ := fun n => integrable_indicator_ofReal_lt_enorm hint (c n)
  have hhi : ∀ n, Integrable (h n) μ := fun n =>
    integrable_indicator_ofReal_lt_enorm_compl hint (c n)
  have hsplit : ∀ n, T f = T (g n) + T (h n) := fun n => by
    rw [← hadd _ _ (hgi n) (hhi n)]; exact congrArg T (banach_indicator_add_compl f).symm
  have hfp : ∀ x, ‖f x‖ₑ ^ p = ENNReal.ofReal (‖f x‖ ^ p) := fun x => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  have hbig : ∀ n x, ‖g n x‖ₑ ≤ ENNReal.ofReal (c n ^ (1 - p)) * ‖f x‖ₑ ^ p := by
    intro n x
    by_cases hx : x ∈ S n
    · have hgx : g n x = f x := Set.indicator_of_mem hx f
      rw [hgx, hfp, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hc n).le _), ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have hlt : c n < ‖f x‖ := by
        have hx' : ENNReal.ofReal (c n) < ENNReal.ofReal ‖f x‖ := by
          rw [ofReal_norm]; exact hx
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hc n).le).1 hx'
      have hpos : 0 < ‖f x‖ := (hc n).trans hlt
      calc ‖f x‖ = ‖f x‖ ^ (1 - p) * ‖f x‖ ^ p := by
            rw [← Real.rpow_add hpos, show 1 - p + p = 1 by ring, Real.rpow_one]
        _ ≤ c n ^ (1 - p) * ‖f x‖ ^ p := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
            exact Real.rpow_le_rpow_of_nonpos (hc n) hlt.le (by linarith)
    · have hgx : g n x = 0 := Set.indicator_of_notMem hx f
      rw [hgx, enorm_zero]
      exact zero_le
  have hsmall : ∀ n x, ‖h n x‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (c n ^ (2 - p)) * ‖f x‖ₑ ^ p := by
    intro n x
    by_cases hx : x ∈ S n
    · have hhx : h n x = 0 := Set.indicator_of_notMem (by simpa using hx) f
      rw [hhx, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
    · have hhx : h n x = f x := Set.indicator_of_mem (by simpa using hx) f
      rw [hhx, hfp, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hc n).le _), ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hle : ‖f x‖ ≤ c n := by
        have hx' : ¬ ENNReal.ofReal (c n) < ENNReal.ofReal ‖f x‖ := by
          rw [ofReal_norm]; exact hx
        rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hc n).le, not_lt] at hx'
        exact hx'
      calc ‖f x‖ ^ (2:ℝ) = ‖f x‖ ^ (2 - p) * ‖f x‖ ^ p := by
            rw [← Real.rpow_add' (norm_nonneg _) (by norm_num : (2 - p + p : ℝ) ≠ 0),
              show 2 - p + p = (2:ℝ) by ring]
        _ ≤ c n ^ (2 - p) * ‖f x‖ ^ p := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
            exact Real.rpow_le_rpow (norm_nonneg _) hle (by linarith)
  have hTh : ∀ n, AEStronglyMeasurable (T (h n)) ν := by
    intro n
    have hL2 : eLpNorm (h n) 2 μ < ∞ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
        (hhi n).aestronglyMeasurable]
      refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (lt_top_iff_ne_top.mp ?_)
      calc ∫⁻ x, ‖h n x‖ₑ ^ (2:ℝ≥0∞).toReal ∂μ
          ≤ ∫⁻ x, ENNReal.ofReal (c n ^ (2 - p)) * ‖f x‖ₑ ^ p ∂μ := by
            refine lintegral_mono fun x => ?_
            simpa using hsmall n x
        _ = ENNReal.ofReal (c n ^ (2 - p)) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hIfin)
    refine aestronglyMeasurable_of_eLpNorm_ne_top (p := 2) (ne_of_lt ?_)
    exact (hstrong (h n) (hhi n)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL2)
  have hg1 : ∀ n, eLpNorm (g n) 1 μ ≤ ENNReal.ofReal (c n ^ (1 - p)) * I := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm (hgi n).aestronglyMeasurable]
    calc ∫⁻ x, ‖g n x‖ₑ ∂μ ≤ ∫⁻ x, ENNReal.ofReal (c n ^ (1 - p)) * ‖f x‖ₑ ^ p ∂μ :=
          lintegral_mono fun x => hbig n x
      _ = ENNReal.ofReal (c n ^ (1 - p)) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hclim : Tendsto (fun n => ENNReal.ofReal (c n ^ (1 - p)) * I) atTop (𝓝 0) := by
    have h1 : Tendsto c atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n => c n ^ (1 - p)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < p - 1 by linarith)).comp h1
      refine this.congr fun n => ?_
      simp only [Function.comp, neg_sub]
    have h3 : Tendsto (fun n => ENNReal.ofReal (c n ^ (1 - p))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h2
    simpa using ENNReal.Tendsto.mul_const h3 (Or.inr hIfin)
  have hconv : TendstoInMeasure ν (fun n => T (h n)) atTop (T f) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hbound : ∀ n, ν {x | ε ≤ edist (T (h n) x) (T f x)}
        ≤ ENNReal.ofReal (A0 / (ε.toReal / 2)) * (ENNReal.ofReal (c n ^ (1 - p)) * I) := by
      intro n
      refine le_trans (measure_mono ?_) ((hweak (g n) (ε.toReal / 2) (hgi n) (by positivity)).trans
        (mul_le_mul_right (hg1 n) _))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [hsplit n, Pi.add_apply, edist_eq_enorm_sub, show T (h n) x - (T (g n) x + T (h n) x)
        = -T (g n) x by abel, enorm_neg, ← ofReal_norm] at hx
      have := ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hx
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => zero_le) hbound
    simpa using ENNReal.Tendsto.const_mul hclim (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨ns, -, hns⟩ := hconv.exists_seq_tendsto_ae
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun i => hTh (ns i)) hns

theorem marcinkiewicz_weak_one_strong_two_integrable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} (T : (α → E) → (β → E)) (hadd : ∀ f g : α → E, MeasureTheory.Integrable f μ → MeasureTheory.Integrable g μ → T (f + g) = T f + T g) {A0 A1 : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) (hweak : ∀ (f : α → E) (lam : ℝ), MeasureTheory.Integrable f μ → 0 < lam → ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) * MeasureTheory.eLpNorm f 1 μ) (hstrong : ∀ f : α → E, MeasureTheory.Integrable f μ → MeasureTheory.eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f 2 μ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : ∃ C : ℝ, 0 < C ∧ ∀ f : α → E, MeasureTheory.Integrable f μ → MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (C * A0 ^ (2 / p - 1) * A1 ^ (2 - 2 / p)) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
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
  intro f hint
  have hCpos : ENNReal.ofReal (K ^ (1/p) / (A0 ^ (2/p - 1) * A1 ^ (2 - 2/p)) * A0 ^ (2 / p - 1)
      * A1 ^ (2 - 2 / p)) ≠ 0 := by
    have hK' : 0 < K ^ (1/p) := Real.rpow_pos_of_pos hKpos _
    have hA : 0 < A0 ^ (2/p - 1) * A1 ^ (2 - 2/p) :=
      mul_pos (Real.rpow_pos_of_pos hA0 _) (Real.rpow_pos_of_pos hA1 _)
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    rw [mul_assoc]
    exact mul_pos (div_pos hK' hA) hA
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) μ = ∞
  · rw [hfin, ENNReal.mul_top hCpos]
    exact le_top
  have hTm : AEStronglyMeasurable (T f) ν :=
    integrable_aestronglyMeasurable_T T hadd hweak hstrong hp1 hp2 hint hfin
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hTf : eLpNorm (T f) (ENNReal.ofReal p) ν = (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hTm, htoReal]
  have hf : eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hint.aestronglyMeasurable, htoReal]
  rw [hTf, hf]
  have hmain : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤ ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    have hlayer := banach_lintegral_rpow_le_innerTail (ν := ν) (W := fun x => ‖T f x‖ₑ)
        (fun x => enorm_ne_top) hp0
    refine hlayer.trans ?_
    have hmaj : ∀ t : ℝ, 0 < t →
        innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
          ≤ ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
          + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) (t^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
      intro t ht
      have h3 := high_pointwise_integrable (A0 := A0) (p := p) (T := T) (f := f) hA0 hp1 hint hweak ht
      have h4 := low_pointwise_innerTail_integrable (A1 := A1) (p := p) (T := T) (f := f) hA1 hp1 hint hstrong ht
      have hWVM : ∀ x, ‖T f x‖ₑ ≤
          ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ
            + ENNReal.ofReal (‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖) := by
        intro x
        have hsum : Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f
            + Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f = f := banach_indicator_add_compl f
        have hkey : ‖T f x‖ₑ ≤ ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖ₑ
            + ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ := by
          conv_lhs => rw [← hsum, hadd (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f)
            (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f)
            (integrable_indicator_ofReal_lt_enorm hint t)
            (integrable_indicator_ofReal_lt_enorm_compl hint t)]
          exact enorm_add_le _ _
        calc ‖T f x‖ₑ ≤ ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖ₑ
              + ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ := hkey
          _ = ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ
              + ENNReal.ofReal (‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖) := by
              rw [ofReal_norm]; ring
      have hdec := banach_innerTail_le (ν := ν) (W := fun x => ‖T f x‖ₑ)
          (V := fun x => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ)
          (w := fun x => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖) hWVM ht
      calc innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
          ≤ (ν {a : β | t/2 < ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) a‖}
              + innerTail ν (fun a => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) a‖ₑ) (t/2))
              * ENNReal.ofReal (t^(p-1)) := mul_le_mul_left hdec _
        _ = ENNReal.ofReal (t^(p-1)) * ν {a : β | t/2 < ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) a‖}
              + ENNReal.ofReal (t^(p-1)) * innerTail ν (fun a => ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) a‖ₑ) (t/2) := by
            ring
        _ ≤ _ := add_le_add h3 h4

    have hInt : ∫⁻ t in Set.Ioi (0:ℝ), innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
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
          (∫⁻ t in Set.Ioi (0:ℝ), innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1)))
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
