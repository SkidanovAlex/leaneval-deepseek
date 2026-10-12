import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.MeanSqPiece

open MeasureTheory
open scoped ENNReal

local notation "F3" => Fin 3 → ℝ

/-! ## The moving box and its volume -/

/-- Joint measurability of the sliding-box indicator: the set of pairs `(u, x)` with
`x ∈ slBox ℓ h u` is measurable.  In coordinates the condition is
`max (-ℓ/2) (h u_j - h/2) ≤ x_j ≤ min (ℓ/2) (h u_j + h/2)` for each `j`, an intersection of
three closed conditions. -/
lemma corrMS3_boxSet_measurable (ℓ h : ℝ) :
    MeasurableSet {p : F3 × F3 | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} := by
  have hEq : {p : F3 × F3 | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1}
      = ⋂ j : Fin 3, {p : F3 × F3 | p.2 j ∈ Work.BoseFixB1S.slI ℓ h (p.1 j)} := by
    ext p
    simp [Work.BoseFixB1S.mem_slBox]
  rw [hEq]
  refine MeasurableSet.iInter fun j => ?_
  have hEq2 : {p : F3 × F3 | p.2 j ∈ Work.BoseFixB1S.slI ℓ h (p.1 j)}
      = {p : F3 × F3 | max (-ℓ/2) (h * p.1 j - h/2) ≤ p.2 j}
        ∩ {p : F3 × F3 | p.2 j ≤ min (ℓ/2) (h * p.1 j + h/2)} := by
    ext p
    simp [Work.BoseFixB1S.slI, Set.mem_Icc]
  rw [hEq2]
  exact MeasurableSet.inter ((isClosed_le (by fun_prop) (by fun_prop)).measurableSet)
    ((isClosed_le (by fun_prop) (by fun_prop)).measurableSet)

/-- The volume of a sliding box is finite (each `slI` is bounded). -/
lemma corrMS3_volume_slBox_ne_top (ℓ h : ℝ) (u : F3) :
    volume (Work.BoseFixB1S.slBox ℓ h u) ≠ ⊤ := by
  rw [Work.BoseFixB1S.volume_slBox, Fin.prod_univ_three]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (Work.BoseFixB1S.volume_slI_ne_top ℓ h (u 0))
      (Work.BoseFixB1S.volume_slI_ne_top ℓ h (u 1)))
    (Work.BoseFixB1S.volume_slI_ne_top ℓ h (u 2))

/-! ## Measurability in the sliding centre `u` -/

/-- The real volume `volume.real (slBox ℓ h u) = (volume (slBox ℓ h u)).toReal` of the sliding
box is a measurable function of its centre. -/
lemma corrMS3_realVolume_measurable (ℓ h : ℝ) :
    Measurable (fun u : F3 => (volume : Measure F3).real (Work.BoseFixB1S.slBox ℓ h u)) := by
  have hboxset := corrMS3_boxSet_measurable ℓ h
  have hvol : Measurable (fun u : F3 => volume (Work.BoseFixB1S.slBox ℓ h u)) := by
    have hjoint1 : Measurable (Function.uncurry (fun (u : F3) (x : F3) =>
        (Work.BoseFixB1S.slBox ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
      have hEq : Function.uncurry (fun (u : F3) (x : F3) =>
          (Work.BoseFixB1S.slBox ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x)
          = {p : F3 × F3 | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1}.indicator
              (fun _ => (1 : ℝ≥0∞)) := by
        funext p
        obtain ⟨u, x⟩ := p
        simp only [Function.uncurry_apply_pair]
        by_cases hx : x ∈ Work.BoseFixB1S.slBox ℓ h u
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show (u, x) ∈ {p : F3 × F3 |
              p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} from hx)]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (u, x) ∉ {p : F3 × F3 |
              p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} from hx)]
      rw [hEq]
      exact measurable_const.indicator hboxset
    have hmain := Measurable.lintegral_prod_right (ν := (volume : Measure F3)) hjoint1
    convert hmain using 2 with u
    exact (MeasureTheory.lintegral_indicator_one (Work.BoseFixB1S.measurableSet_slBox ℓ h u)).symm
  have hreal : (fun u : F3 => (volume : Measure F3).real (Work.BoseFixB1S.slBox ℓ h u))
      = fun u : F3 => (volume (Work.BoseFixB1S.slBox ℓ h u)).toReal := by
    funext u; rw [MeasureTheory.Measure.real_def]
  rw [hreal]
  exact ENNReal.measurable_toReal.comp hvol

/-- The box mean `u ↦ ∫_{slBox ℓ h u} w` of a continuous `w` is measurable (the `u`-marginal
of the jointly measurable box indicator times `w`). -/
lemma corrMS3_boxIntegral_measurable {ℓ h : ℝ} {w : F3 → ℝ} (hw : Continuous w) :
    Measurable (fun u : F3 => ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) := by
  have hboxset := corrMS3_boxSet_measurable ℓ h
  have hjoint : Measurable (Function.uncurry (fun (u : F3) (x : F3) =>
      (Work.BoseFixB1S.slBox ℓ h u).indicator w x)) := by
    have hEq : Function.uncurry (fun (u : F3) (x : F3) =>
        (Work.BoseFixB1S.slBox ℓ h u).indicator w x)
        = {p : F3 × F3 | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1}.indicator
            (fun p => w p.2) := by
      funext p
      obtain ⟨u, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      by_cases hx : x ∈ Work.BoseFixB1S.slBox ℓ h u
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show (u, x) ∈ {p : F3 × F3 |
            p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} from hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (u, x) ∉ {p : F3 × F3 |
            p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} from hx)]
    rw [hEq]
    exact (hw.measurable.comp measurable_snd).indicator hboxset
  have hsm := StronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure F3)) hjoint.stronglyMeasurable
  convert hsm.measurable using 2 with u
  exact (MeasureTheory.integral_indicator (Work.BoseFixB1S.measurableSet_slBox ℓ h u)).symm

/-! ## The pointwise comparison of the two box means -/

/-- `ENNReal.ofReal` of a reciprocal is at most the reciprocal of the `ENNReal.ofReal` (for a
nonnegative real; the degenerate case `x = 0` is handled by `0⁻¹ = ⊤` on the `ℝ≥0∞` side). -/
lemma corrMS3_ofReal_inv_le_inv_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · rw [ENNReal.ofReal_inv_of_pos h]

/-- For continuous real-valued `w` and any set `s`, `ofReal |∫_s w| ≤ ∫⁻_s ofReal |w|`.  Only
`w`'s a.e.-strong measurability is used, so `s` need not be measurable or bounded. -/
lemma corrMS3_ofReal_abs_setIntegral_le_lintegral {w : F3 → ℝ} (hw : Continuous w)
    (s : Set F3) :
    ENNReal.ofReal |∫ x in s, w x| ≤ ∫⁻ x in s, ENNReal.ofReal |w x| := by
  have h1 : |∫ x in s, w x| ≤ ∫ x in s, |w x| := by
    have := norm_integral_le_integral_norm (f := w) (μ := (volume : Measure F3).restrict s)
    simpa [Real.norm_eq_abs] using this
  have h3 : (∫ x in s, |w x|) = (∫⁻ x in s, ENNReal.ofReal |w x|).toReal := by
    have := integral_norm_eq_lintegral_enorm (μ := (volume : Measure F3).restrict s) (f := w)
      hw.aestronglyMeasurable
    simpa only [Real.norm_eq_abs, ← ofReal_norm] using this
  calc ENNReal.ofReal |∫ x in s, w x|
      ≤ ENNReal.ofReal (∫ x in s, |w x|) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ((∫⁻ x in s, ENNReal.ofReal |w x|).toReal) := by rw [h3]
    _ ≤ ∫⁻ x in s, ENNReal.ofReal |w x| := ENNReal.ofReal_toReal_le

/-- **Pointwise step.**  The `ofReal` of the square of the `ℝ`-valued box mean of `w` is at
most the square of the normalised `ℝ≥0∞` box mean of `|w|`. -/
lemma corrMS3_slBox_mean_sq_le_lintegral {ℓ h : ℝ} {w : F3 → ℝ} (hw : Continuous w) (u : F3) :
    ENNReal.ofReal ((1 / (volume : Measure F3).real (Work.BoseFixB1S.slBox ℓ h u) *
        ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x)^2)
      ≤ ((∫⁻ x in Work.BoseFixB1S.slBox ℓ h u, ENNReal.ofReal |w x|) /
          (volume (Work.BoseFixB1S.slBox ℓ h u)))^2 := by
  set m := (volume : Measure F3).real (Work.BoseFixB1S.slBox ℓ h u) with hm
  set A := ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x with hA
  set I := ∫⁻ x in Work.BoseFixB1S.slBox ℓ h u, ENNReal.ofReal |w x| with hI
  set V := volume (Work.BoseFixB1S.slBox ℓ h u) with hV
  have hmnn : 0 ≤ m := by
    rw [hm, MeasureTheory.Measure.real_def]; exact ENNReal.toReal_nonneg
  have step1 : ENNReal.ofReal ((1 / m * A)^2) = (ENNReal.ofReal |1 / m * A|)^2 := by
    rw [← sq_abs (1 / m * A), ENNReal.ofReal_pow (abs_nonneg _)]
  have step2 : ENNReal.ofReal |1 / m * A| = ENNReal.ofReal (1 / m) * ENNReal.ofReal |A| := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), one_div, abs_inv, abs_of_nonneg hmnn]
  have step3 : ENNReal.ofReal (1 / m) ≤ (ENNReal.ofReal m)⁻¹ := by
    rw [one_div]
    exact corrMS3_ofReal_inv_le_inv_of_nonneg hmnn
  have step4 : ENNReal.ofReal |A| ≤ I := by
    rw [hA, hI]
    exact corrMS3_ofReal_abs_setIntegral_le_lintegral hw _
  have step5 : (ENNReal.ofReal (1 / m) * ENNReal.ofReal |A|)^2
      ≤ ((ENNReal.ofReal m)⁻¹ * I)^2 := by
    have hmul : ENNReal.ofReal (1 / m) * ENNReal.ofReal |A| ≤ (ENNReal.ofReal m)⁻¹ * I :=
      mul_le_mul' step3 step4
    simpa using pow_le_pow_left' hmul 2
  have hVm : V = ENNReal.ofReal m := by
    rw [hV, hm, MeasureTheory.Measure.real_def,
      ENNReal.ofReal_toReal (corrMS3_volume_slBox_ne_top ℓ h u)]
  calc ENNReal.ofReal ((1 / m * A)^2)
      = (ENNReal.ofReal |1 / m * A|)^2 := step1
    _ = (ENNReal.ofReal (1 / m) * ENNReal.ofReal |A|)^2 := by rw [step2]
    _ ≤ ((ENNReal.ofReal m)⁻¹ * I)^2 := step5
    _ = (I / V)^2 := by rw [hVm, ENNReal.div_eq_inv_mul]

/-! ## The right-hand side in `ℝ≥0∞`-form -/

/-- The cube `slBig ℓ` is compact (a product of three compact intervals). -/
lemma corrMS3_isCompact_slBig (ℓ : ℝ) : IsCompact (Work.BoseFixB1S.slBig ℓ) := by
  simpa [Work.BoseFixB1S.slBig] using
    (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc (a := -ℓ/2) (b := ℓ/2)))

/-- The `ℝ≥0∞` cube integral of `(ofReal |w|)²` is the `ofReal` of the `ℝ` cube integral of
`w²`. -/
lemma corrMS3_lintegral_slBig_ofReal_sq {ℓ : ℝ} {w : F3 → ℝ} (hw : Continuous w) :
    ∫⁻ x in Work.BoseFixB1S.slBig ℓ, (ENNReal.ofReal |w x|)^2
      = ENNReal.ofReal (∫ x in Work.BoseFixB1S.slBig ℓ, (w x)^2) := by
  have hpt : ∀ x, (ENNReal.ofReal |w x|)^2 = ENNReal.ofReal ((w x)^2) := by
    intro x
    rw [← sq_abs (w x), ENNReal.ofReal_pow (abs_nonneg (w x)) 2]
  rw [lintegral_congr hpt]
  symm
  refine MeasureTheory.ofReal_integral_eq_lintegral_ofReal ?_
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
  exact ((hw.pow 2).continuousOn.integrableOn_compact (corrMS3_isCompact_slBig ℓ)).integrable

/-! ## The main transfer -/

open scoped ENNReal MeasureTheory in
theorem corrMeanSqRealFin3
    (H3 : ∀ {ℓ h : ℝ}, 0 < h → h ≤ ℓ → ∀ {F : (Fin 3 → ℝ) → ℝ≥0∞}, Measurable F →
      ∫⁻ u : Fin 3 → ℝ,
          ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
            / (MeasureTheory.volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2
        ≤ ENNReal.ofReal ((9 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2)
    {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {w : (Fin 3 → ℝ) → ℝ} (hw : Continuous w) :
    MeasureTheory.Integrable (fun u : Fin 3 → ℝ =>
        ((1 / (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)).real
            (Work.BoseFixB1S.slBox ℓ h u)) *
          ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2)
      ∧ (∫ u : Fin 3 → ℝ,
          ((1 / (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)).real
              (Work.BoseFixB1S.slBox ℓ h u)) *
            ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2)
        ≤ (9 / h) ^ 3 * (∫ x in Work.BoseFixB1S.slBig ℓ, (w x) ^ 2) := by
  -- a.e.-strong measurability of the integrand
  have hAEm : AEMeasurable (fun u : F3 =>
      ((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
          (Work.BoseFixB1S.slBox ℓ h u)) *
        ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2) (volume : Measure F3) :=
    (((measurable_const.div (corrMS3_realVolume_measurable ℓ h)).mul
      (corrMS3_boxIntegral_measurable hw)).pow_const 2).aemeasurable
  -- the pointwise comparison
  have hpt : ∀ u : F3, ENNReal.ofReal
        (((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
          (Work.BoseFixB1S.slBox ℓ h u)) *
        ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2)
      ≤ ((∫⁻ x in Work.BoseFixB1S.slBox ℓ h u, ENNReal.ofReal |w x|) /
          (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2 := fun u =>
    corrMS3_slBox_mean_sq_le_lintegral hw u
  have hW : Measurable (fun y : F3 => ENNReal.ofReal |w y|) := (hw.abs).measurable.ennreal_ofReal
  -- the `ℝ≥0∞` bound, with `F := fun y => ofReal |w y|`
  have hle : (∫⁻ u : F3, ENNReal.ofReal
        (((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
          (Work.BoseFixB1S.slBox ℓ h u)) *
        ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2))
      ≤ ENNReal.ofReal ((9 / h) ^ 3) *
        ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (ENNReal.ofReal |w y|) ^ 2 :=
    le_trans (lintegral_mono hpt) (H3 hh hhℓ hW)
  rw [corrMS3_lintegral_slBig_ofReal_sq hw] at hle
  -- finiteness of the right-hand side
  have hJnn : 0 ≤ ∫ x in Work.BoseFixB1S.slBig ℓ, (w x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hfin : ENNReal.ofReal ((9 / h) ^ 3) *
      ENNReal.ofReal (∫ x in Work.BoseFixB1S.slBig ℓ, (w x) ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hLt : (∫⁻ u : F3, ENNReal.ofReal
        (((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
          (Work.BoseFixB1S.slBox ℓ h u)) *
        ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2)) < ⊤ :=
    lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
  have hIeq : (∫ u : F3, (((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
          (Work.BoseFixB1S.slBox ℓ h u)) *
        ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2))
      = (∫⁻ u : F3, ENNReal.ofReal
        (((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
          (Work.BoseFixB1S.slBox ℓ h u)) *
        ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun u => sq_nonneg _) hAEm.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine ⟨hAEm.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    rw [show (∫⁻ a : F3, ENNReal.ofReal
          ‖(((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
            (Work.BoseFixB1S.slBox ℓ h a)) *
          ∫ x in Work.BoseFixB1S.slBox ℓ h a, w x) ^ 2)‖)
        = ∫⁻ a : F3, ENNReal.ofReal
          (((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
            (Work.BoseFixB1S.slBox ℓ h a)) *
          ∫ x in Work.BoseFixB1S.slBox ℓ h a, w x) ^ 2) from
      lintegral_congr fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]]
    exact hLt
  · rw [hIeq]
    calc (∫⁻ u : F3, ENNReal.ofReal
          (((1 / (MeasureTheory.volume : MeasureTheory.Measure F3).real
            (Work.BoseFixB1S.slBox ℓ h u)) *
          ∫ x in Work.BoseFixB1S.slBox ℓ h u, w x) ^ 2)).toReal
        ≤ (ENNReal.ofReal ((9 / h) ^ 3) *
            ENNReal.ofReal (∫ x in Work.BoseFixB1S.slBig ℓ, (w x) ^ 2)).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = (9 / h) ^ 3 * (∫ x in Work.BoseFixB1S.slBig ℓ, (w x) ^ 2) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofReal hJnn]

end Work.BoseFixB1B.MeanSqPiece
