import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two

/-!
# Marcinkiewicz interpolation for Banach-space-valued functions

The commons already contains the classical Marcinkiewicz interpolation theorem
`Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two` for `ℂ`-valued functions,
together with the (function-space-agnostic) "inner tail" machinery used in its proof.

In this file we record the Banach-space-valued version: for a real normed space `E` and an
additive operator `T : (α → E) → (β → E)` which is weak-type `(1,1)` with constant `A₀` and
strong-type `(2,2)` with constant `A₁`, the operator is strong-type `(p,p)` for `1 < p < 2`.

The proof is the same truncation argument as in the `ℂ` case; the only changes are that the
truncations are written with `Set.indicator` (rather than multiplication by a `0/1`-valued
function) and that the norm of an indicator is computed with `enorm_indicator_eq_indicator_enorm`.
-/

open MeasureTheory Measure Filter Set
open scoped ENNReal Topology

namespace Commons.Analysis.MeasureTheory

/-! ## Splitting a function into two indicator pieces -/

/-- Splitting a function into the part supported on `s` and the part supported on its complement. -/
lemma banach_indicator_add_compl {α E : Type*} [AddMonoid E] {s : Set α} (f : α → E) :
    Set.indicator s f + Set.indicator sᶜ f = f := by
  funext x
  rw [Pi.add_apply]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx), add_zero]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx), zero_add]

/-- Squaring an `enorm` after applying an indicator. -/
lemma banach_trunc_sq {α : Type*} (W : α → ℝ≥0∞) (s : Set α) (x : α) :
    (Set.indicator s W x) ^ (2:ℝ) = Set.indicator s (fun x => (W x) ^ 2) x := by
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact rpow_two_eq (W x)
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]

/-- The tail set at level `t` is contained in the union of the tails of the truncations. -/
lemma banach_tail_subset {α : Type*} {β E : Type*} [MeasurableSpace β] [MeasurableSpace E] [SeminormedAddCommGroup E]
    (T : (α → E) → (β → E))
    (hadd : ∀ f g : α → E, T (f + g) = T f + T g) (t : ℝ) (ht : 0 < t)
    (f g h : α → E) (hsum : g + h = f) :
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
lemma banach_high_pointwise {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} {A0 : ℝ} (hA0 : 0 < A0) {p : ℝ}
    (hp1 : 1 < p)
    {T : (α → E) → (β → E)} {f : α → E} (hfm : AEStronglyMeasurable f μ)
    (hweak : ∀ (g : α → E) (lam : ℝ), 0 < lam →
      ν {x : β | lam < ‖T g x‖} ≤ ENNReal.ofReal (A0 / lam) * eLpNorm g 1 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      ν {a : β | t / 2 < ‖T (Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} f) a‖}
      ≤ ENNReal.ofReal (6 * A0 * t ^ (p - 2)) *
          (∫⁻ s in Set.Ioi (t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := by
  set g : α → E := Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} f with hg
  have h1 : ν {a : β | t / 2 < ‖T g a‖} ≤ ENNReal.ofReal (A0 / (t/2)) * eLpNorm g 1 μ :=
    hweak g (t/2) (by positivity)
  have h2 : eLpNorm g 1 μ
      = ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
    have hgm : AEStronglyMeasurable g μ :=
      hfm.indicator₀ (nullMeasurableSet_lt aemeasurable_const hfm.enorm)
    rw [eLpNorm_one_eq_lintegral_enorm hgm]
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

/-- The strong-type bound for the low truncation, at level `t/2`, multiplied by `t^(p-1)`. -/
lemma banach_innerTail_le {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {W V : β → ℝ≥0∞} {w : β → ℝ}
    (hWV : ∀ x, W x ≤ V x + ENNReal.ofReal (w x)) {t : ℝ} (ht : 0 < t) :
    innerTail ν W t ≤ ν {x | t / 2 < w x} + innerTail ν V (t / 2) := by
  set B : Set β := {x | t / 2 < w x} with hB
  have hsubB : B = {x | t / 2 < w x} := hB
  have hstep : ∀ (E : {E // MeasurableSet E ∧ E ⊆ {x | ENNReal.ofReal t < W x}})
      (C : Set β), B ⊆ C → MeasurableSet C →
      ν E.1 ≤ ν C + innerTail ν V (t / 2) := by
    intro E C hBC hC
    have hsub : E.1 \ C ⊆ {x | ENNReal.ofReal (t/2) < V x} := by
      intro x hx
      have hxE : x ∈ E.1 := hx.1
      have hxC : x ∉ C := hx.2
      have hw : w x ≤ t / 2 := by
        by_contra hcon
        exact hxC (hBC (by rw [hsubB]; exact not_le.mp hcon))
      have hWt : ENNReal.ofReal t < W x := E.2.2 hxE
      by_contra hcon
      have hcon' : V x ≤ ENNReal.ofReal (t/2) := le_of_not_gt hcon
      have h2 : W x ≤ ENNReal.ofReal t := by
        calc W x ≤ V x + ENNReal.ofReal (w x) := hWV x
          _ ≤ ENNReal.ofReal (t/2) + ENNReal.ofReal (t/2) :=
              add_le_add hcon' (ENNReal.ofReal_le_ofReal hw)
          _ = ENNReal.ofReal t := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
              norm_num
      exact absurd hWt (not_lt.2 h2)
    have hle : ν (E.1 \ C) ≤ innerTail ν V (t/2) :=
      le_innerTail (E.2.1.diff hC) hsub
    have hun : (E.1 ∩ C) ∪ (E.1 \ C) = E.1 := by
      ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
    have hdisj : Disjoint (E.1 ∩ C) (E.1 \ C) := by
      rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx.2
    calc ν E.1 = ν ((E.1 ∩ C) ∪ (E.1 \ C)) := by rw [hun]
      _ = ν (E.1 ∩ C) + ν (E.1 \ C) :=
          measure_union hdisj (E.2.1.diff hC)
      _ ≤ ν C + innerTail ν V (t/2) := add_le_add (measure_mono Set.inter_subset_right) hle
  have hkey : innerTail ν W t
      ≤ ⨅ C : {C // B ⊆ C ∧ MeasurableSet C}, (ν C.1 + innerTail ν V (t/2)) := by
    rw [innerTail]
    refine iSup_le fun E => le_iInf fun C => hstep E C C.2.1 C.2.2
  refine hkey.trans ?_
  rw [← ENNReal.iInf_add, ← measure_eq_iInf']

lemma banach_lintegral_rpow_le_innerTail {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {W : β → ℝ≥0∞} (hWfin : ∀ x, W x ≠ ∞) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, W x ^ p ∂ν
      ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ), innerTail ν W t * ENNReal.ofReal (t ^ (p - 1)) := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have hp1 : (0:ℝ) < 1 / p := one_div_pos.2 hp
  rw [← iSup_lintegral_measurable_le_eq_lintegral (fun x => W x ^ p)]
  refine iSup_le fun g => iSup_le fun hg => iSup_le fun hgle => ?_
  have hu_meas : Measurable (fun x => (g x) ^ (1/p)) :=
    (ENNReal.continuous_rpow_const (y := (1/p))).measurable.comp hg
  set u : β → ℝ≥0∞ := fun x => (g x) ^ (1/p) with hu
  have hup : ∀ x, u x ^ p = g x := by
    intro x
    show ((g x) ^ (1/p)) ^ p = g x
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hpne, ENNReal.rpow_one]
  have huW : ∀ x, u x ≤ W x := by
    intro x
    have h1 : u x ^ p ≤ W x ^ p := by rw [hup x]; exact hgle x
    have h2 : u x = (u x ^ p) ^ (1/p) := by
      rw [← ENNReal.rpow_mul, mul_one_div_cancel hpne, ENNReal.rpow_one]
    rw [h2]
    calc (u x ^ p) ^ (1/p) ≤ (W x ^ p) ^ (1/p) := ENNReal.rpow_le_rpow h1 (le_of_lt hp1)
      _ = W x := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hpne, ENNReal.rpow_one]
  have hufin : ∀ x, u x ≠ ∞ := fun x => ne_top_of_le_ne_top (hWfin x) (huW x)
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul ν
      (f := fun x => (u x).toReal) (Eventually.of_forall fun x => ENNReal.toReal_nonneg)
      (hu_meas.ennreal_toReal.aemeasurable) hp
  have hleft : ∫⁻ x, g x ∂ν = ∫⁻ x, ENNReal.ofReal ((u x).toReal ^ p) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (le_of_lt hp),
      ENNReal.ofReal_toReal (hufin x), hup x]
  rw [hleft, hlayer]
  refine mul_le_mul_right ?_ _
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  refine mul_le_mul_left ?_ _
  refine le_innerTail (measurableSet_lt measurable_const hu_meas.ennreal_toReal) ?_
  intro x hx
  have : ENNReal.ofReal t < ENNReal.ofReal ((u x).toReal) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)).2 hx
  rw [ENNReal.ofReal_toReal (hufin x)] at this
  exact lt_of_lt_of_le this (huW x)

lemma banach_low_pointwise_innerTail {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} {A1 : ℝ}
    (hA1 : 0 < A1) {p : ℝ} (hp1 : 1 < p)
    {T : (α → E) → (β → E)} {f : α → E} (hfm : AEStronglyMeasurable f μ)
    (hstrong : ∀ g : α → E, eLpNorm (T g) 2 ν ≤ ENNReal.ofReal A1 * eLpNorm g 2 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      innerTail ν (fun a => ‖T (Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ f) a‖ₑ) (t / 2)
      ≤ ENNReal.ofReal (4 * A1 ^ 2 * t ^ (p - 3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) (t ^ 2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
  set h : α → E := Set.indicator {x : α | ENNReal.ofReal t < ‖f x‖ₑ}ᶜ f with hh
  have h2t : (2:ℝ≥0∞).toReal = (2:ℝ) := by norm_num
  have hcheb : ENNReal.ofReal (t/2)^(2:ℝ) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ ∫⁻ x, ‖T h x‖ₑ ^ (2:ℝ) ∂ν :=
    pow_mul_innerTail_le (μ := ν) (W := fun x => ‖T h x‖ₑ) (u := t/2) (p := 2)
      (by positivity) (by norm_num)
  have hsquare : ENNReal.ofReal (t/2) ^ (2:ℝ) = ENNReal.ofReal ((t/2)^2) := by
    rw [rpow_two_eq, ← ENNReal.ofReal_pow (by positivity)]
  have hhm : AEStronglyMeasurable h μ :=
    hfm.indicator₀ (nullMeasurableSet_lt aemeasurable_const hfm.enorm).compl
  have heLph : (eLpNorm h 2 μ) ^ (2:ℝ) = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hhm]
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
          ENNReal.rpow_le_rpow (hstrong h) (by norm_num)
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

/-- Under the weak `(1,1)` and strong `(2,2)` hypotheses, `T f` is a.e. strongly measurable for
every `f ∈ L^p` (`1 < p < 2`): the low truncations of `f` lie in `L²`, so their images are
a.e. strongly measurable, and they converge to `T f` in measure by the weak `(1,1)` bound applied
to the high truncations. -/
lemma banach_aestronglyMeasurable_T {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}
    (T : (α → E) → (β → E)) (hadd : ∀ f g : α → E, T (f + g) = T f + T g)
    {A0 A1 : ℝ}
    (hweak : ∀ (f : α → E) (lam : ℝ), 0 < lam →
        ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) * eLpNorm f 1 μ)
    (hstrong : ∀ f : α → E, eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * eLpNorm f 2 μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {f : α → E} (hfm : AEStronglyMeasurable f μ)
    (hfin : eLpNorm f (ENNReal.ofReal p) μ ≠ ∞) :
    AEStronglyMeasurable (T f) ν := by
  have hp0 : 0 < p := by linarith
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ with hI
  have hIfin : I ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top (lt_top_iff_ne_top.mpr hfin)
    rw [ENNReal.toReal_ofReal hp0.le] at h
    exact h.ne
  set c : ℕ → ℝ := fun n => (n:ℝ) + 1 with hcdef
  have hc : ∀ n, 0 < c n := fun n => by positivity
  set S : ℕ → Set α := fun n => {x | ENNReal.ofReal (c n) < ‖f x‖ₑ} with hSdef
  have hS : ∀ n, NullMeasurableSet (S n) μ := fun n =>
    nullMeasurableSet_lt aemeasurable_const hfm.enorm
  set g : ℕ → α → E := fun n => (S n).indicator f with hgdef
  set h : ℕ → α → E := fun n => (S n)ᶜ.indicator f with hhdef
  have hsplit : ∀ n, T f = T (g n) + T (h n) := fun n => by
    rw [← hadd]; exact congrArg T (banach_indicator_add_compl f).symm
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
  -- the images of the low truncations are a.e. strongly measurable
  have hTh : ∀ n, AEStronglyMeasurable (T (h n)) ν := by
    intro n
    have hhm : AEStronglyMeasurable (h n) μ := hfm.indicator₀ (hS n).compl
    have hL2 : eLpNorm (h n) 2 μ < ∞ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hhm]
      refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (lt_top_iff_ne_top.mp ?_)
      calc ∫⁻ x, ‖h n x‖ₑ ^ (2:ℝ≥0∞).toReal ∂μ
          ≤ ∫⁻ x, ENNReal.ofReal (c n ^ (2 - p)) * ‖f x‖ₑ ^ p ∂μ := by
            refine lintegral_mono fun x => ?_
            simpa using hsmall n x
        _ = ENNReal.ofReal (c n ^ (2 - p)) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hIfin)
    refine aestronglyMeasurable_of_eLpNorm_ne_top (p := 2) (ne_of_lt ?_)
    exact (hstrong (h n)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL2)
  -- the high truncations are small in `L¹`
  have hg1 : ∀ n, eLpNorm (g n) 1 μ ≤ ENNReal.ofReal (c n ^ (1 - p)) * I := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm (hfm.indicator₀ (hS n))]
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
      refine le_trans (measure_mono ?_) ((hweak (g n) (ε.toReal / 2) (by positivity)).trans
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

theorem marcinkiewicz_weak_one_strong_two_banach
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    (T : (α → E) → (β → E))
    (hadd : ∀ f g : α → E, T (f + g) = T f + T g)
    (hmeas : ∀ f : α → E, AEMeasurable (T f) ν)
    {A0 A1 : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1)
    (hweak : ∀ (f : α → E) (lam : ℝ), 0 < lam →
        ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) * MeasureTheory.eLpNorm f 1 μ)
    (hstrong : ∀ f : α → E,
        MeasureTheory.eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f 2 μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : α → E,
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
  have hCpos : ENNReal.ofReal (K ^ (1/p) / (A0 ^ (2/p - 1) * A1 ^ (2 - 2/p)) * A0 ^ (2 / p - 1)
      * A1 ^ (2 - 2 / p)) ≠ 0 := by
    have hK' : 0 < K ^ (1/p) := Real.rpow_pos_of_pos hKpos _
    have hA : 0 < A0 ^ (2/p - 1) * A1 ^ (2 - 2/p) :=
      mul_pos (Real.rpow_pos_of_pos hA0 _) (Real.rpow_pos_of_pos hA1 _)
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    rw [mul_assoc]
    exact mul_pos (div_pos hK' hA) hA
  by_cases hfm : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hfm, ENNReal.mul_top hCpos]
    exact le_top
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) μ = ∞
  · rw [hfin, ENNReal.mul_top hCpos]
    exact le_top
  have hTm : AEStronglyMeasurable (T f) ν :=
    banach_aestronglyMeasurable_T T hadd hweak hstrong hp1 hp2 hfm hfin
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hTf : eLpNorm (T f) (ENNReal.ofReal p) ν = (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hTm, htoReal]
  have hf : eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hfm, htoReal]
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
      have h3 := banach_high_pointwise (A0 := A0) (p := p) (T := T) (f := f) hA0 hp1 hfm hweak ht
      have h4 := banach_low_pointwise_innerTail (A1 := A1) (p := p) (T := T) (f := f) hA1 hp1 hfm hstrong ht
      have hWVM : ∀ x, ‖T f x‖ₑ ≤
          ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ
            + ENNReal.ofReal (‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖) := by
        intro x
        have hsum : Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f
            + Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f = f := banach_indicator_add_compl f
        have hkey : ‖T f x‖ₑ ≤ ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f) x‖ₑ
            + ‖T (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f) x‖ₑ := by
          conv_lhs => rw [← hsum, hadd (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ} f)
            (Set.indicator {y : α | ENNReal.ofReal t < ‖f y‖ₑ}ᶜ f)]
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
