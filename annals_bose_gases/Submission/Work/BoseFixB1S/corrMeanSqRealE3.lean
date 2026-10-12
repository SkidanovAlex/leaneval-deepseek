import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Smear.meanSq3dE3H
import Submission.Work.BoseFixB1S.CorrMS.oneDim9
import Submission.Work.BoseFixB1S.CorrMS.threeDim9
import Submission.Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary `ℝ≥0∞` bookkeeping -/

/-- `ofReal` of a reciprocal is at most the reciprocal of the `ofReal` (for a nonnegative real,
with the degenerate case `x = 0` handled by `0⁻¹ = ⊤` on the `ℝ≥0∞` side). -/
lemma corrMS_ofReal_inv_le_inv_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · rw [ENNReal.ofReal_inv_of_pos h]

/-! ## The sliding box mass -/

/-- The true box volume `boxMass` is nonnegative (it is a Lebesgue volume). -/
lemma corrMS_boxMass_nonneg (ℓ d : ℝ) (u : ℝ³) :
    0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
  exact ENNReal.toReal_nonneg

/-- `ENNReal.ofReal` of the box mass is the Lebesgue volume of the box. -/
lemma corrMS_ofReal_boxMass_eq_volume {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ℝ) (u : ℝ³) :
    ENNReal.ofReal (Work.SmallBoxSliding.boxMass ℓ d u)
      = (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) :=
  (Work.SmallBoxSliding.ofReal_boxMass_eq hℓ u).trans
    (Work.SmallBoxSliding.lintegral_ofReal_boxInd ℓ d u)

/-! ## The comparison of a set integral with its `ℝ≥0∞` lintegral -/

/-- For a continuous real-valued `w` and any set `s`, the `ofReal` of the absolute value of the
set integral of `w` is at most the `ℝ≥0∞` set lintegral of `ofReal |w|`.  No integrability or
boundedness of `s` is needed: `ofReal (‖∫‖) ≤ ofReal (∫‖·‖) ≤ ∫⁻ ‖·‖ₑ` and
`∫ ‖f‖ = (∫⁻ ‖f‖ₑ).toReal` holds for *any* a.e.-strongly-measurable `f`. -/
lemma corrMS_ofReal_abs_setIntegral_le_lintegral {w : ℝ³ → ℝ} (hw : Continuous w) (s : Set ℝ³) :
    ENNReal.ofReal |∫ x in s, w x| ≤ ∫⁻ x in s, ENNReal.ofReal |w x| := by
  have h1 : |∫ x in s, w x| ≤ ∫ x in s, |w x| := by
    have := norm_integral_le_integral_norm (f := w) (μ := (volume : Measure ℝ³).restrict s)
    simpa [Real.norm_eq_abs] using this
  have h3 : (∫ x in s, |w x|) = (∫⁻ x in s, ENNReal.ofReal |w x|).toReal := by
    have := integral_norm_eq_lintegral_enorm (μ := (volume : Measure ℝ³).restrict s) (f := w)
      hw.aestronglyMeasurable
    simpa only [Real.norm_eq_abs, ← ofReal_norm] using this
  calc ENNReal.ofReal |∫ x in s, w x|
      ≤ ENNReal.ofReal (∫ x in s, |w x|) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ((∫⁻ x in s, ENNReal.ofReal |w x|).toReal) := by rw [h3]
    _ ≤ ∫⁻ x in s, ENNReal.ofReal |w x| := ENNReal.ofReal_toReal_le

/-! ## The pointwise comparison of the `ℝ`-valued and the `ℝ≥0∞`-valued box mean -/

/-- **Pointwise step.**  The `ofReal` of the square of the `ℝ`-valued box mean of `w` is bounded by
the square of the normalised `ℝ≥0∞` box mean of `|w|`. -/
lemma corrMS_ofReal_boxMean_sq_le_lintegral {ℓ d : ℝ} (hℓ : 0 < ℓ) {w : ℝ³ → ℝ}
    (hw : Continuous w) (u : ℝ³) :
    ENNReal.ofReal ((1 / Work.SmallBoxSliding.boxMass ℓ d u *
        ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
      ≤ ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, ENNReal.ofReal |w x|) /
          (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u))^2 := by
  set m := Work.SmallBoxSliding.boxMass ℓ d u with hm
  set A := ∫ x in Submission.BoseGases.dlBox ℓ d u, w x with hA
  set I := ∫⁻ x in Submission.BoseGases.dlBox ℓ d u, ENNReal.ofReal |w x| with hI
  set V := (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) with hV
  have hmnn : 0 ≤ m := corrMS_boxMass_nonneg ℓ d u
  have step1 : ENNReal.ofReal ((1 / m * A)^2) = (ENNReal.ofReal |1 / m * A|)^2 := by
    rw [← sq_abs (1 / m * A), ENNReal.ofReal_pow (abs_nonneg _)]
  have step2 : ENNReal.ofReal |1 / m * A| = ENNReal.ofReal (1 / m) * ENNReal.ofReal |A| := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), one_div, abs_inv, abs_of_nonneg hmnn]
  have step3 : ENNReal.ofReal (1 / m) ≤ (ENNReal.ofReal m)⁻¹ := by
    rw [one_div]
    exact corrMS_ofReal_inv_le_inv_of_nonneg hmnn
  have step4 : ENNReal.ofReal |A| ≤ I := by
    rw [hA, hI]
    exact corrMS_ofReal_abs_setIntegral_le_lintegral hw _
  have step5 : (ENNReal.ofReal (1 / m) * ENNReal.ofReal |A|)^2
      ≤ ((ENNReal.ofReal m)⁻¹ * I)^2 := by
    have hmul : ENNReal.ofReal (1 / m) * ENNReal.ofReal |A| ≤ (ENNReal.ofReal m)⁻¹ * I :=
      mul_le_mul' step3 step4
    simpa using pow_le_pow_left' hmul 2
  have hVm : V = ENNReal.ofReal m := by
    rw [hV, hm]
    exact (corrMS_ofReal_boxMass_eq_volume hℓ d u).symm
  calc ENNReal.ofReal ((1 / m * A)^2)
      = (ENNReal.ofReal |1 / m * A|)^2 := step1
    _ = (ENNReal.ofReal (1 / m) * ENNReal.ofReal |A|)^2 := by rw [step2]
    _ ≤ ((ENNReal.ofReal m)⁻¹ * I)^2 := step5
    _ = (I / V)^2 := by rw [hVm, ENNReal.div_eq_inv_mul]

/-! ## The `ℝ≥0∞` form of the right-hand side -/

/-- The `ℝ≥0∞` box lintegral of `(ofReal |w|)²` is the `ofReal` of the `ℝ` box integral of
`w²` (both over the centred cube `acube ℓ`). -/
lemma corrMS_lintegral_acube_ofReal_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℝ³ → ℝ} (hw : Continuous w) :
    ∫⁻ x in Submission.BoseGases.acube ℓ, (ENNReal.ofReal |w x|)^2
      = ENNReal.ofReal (∫ x in Submission.BoseGases.acube ℓ, (w x)^2) := by
  have hpt : ∀ x, (ENNReal.ofReal |w x|)^2 = ENNReal.ofReal ((w x)^2) := by
    intro x
    rw [← sq_abs (w x), ENNReal.ofReal_pow (abs_nonneg (w x)) 2]
  rw [lintegral_congr hpt]
  symm
  refine MeasureTheory.ofReal_integral_eq_lintegral_ofReal ?_
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
  exact ((hw.pow 2).continuousOn.integrableOn_compact
    (Submission.BoseGases.acube_compact hℓ)).integrable

/-! ## A.e. measurability of the squared box mean -/

/-- The squared box mean of a continuous `w` is a.e.-measurable in the sliding centre (the
`u`-marginal of the jointly measurable box indicator times `w`). -/
lemma corrMS_aemeasurable_boxMean_sq {ℓ d : ℝ} (hℓ : 0 < ℓ) {w : ℝ³ → ℝ}
    (hw : Continuous w) :
    AEMeasurable (fun u : ℝ³ => ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2) (volume : Measure ℝ³) := by
  set Φ : Submission.BoseGases.X 1 → ℝ := fun ψ => w (ψ 0) with hΦ
  have hΦc : Continuous Φ := hw.comp (continuous_apply 0)
  have h := Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean (d := d) hℓ hΦc
  refine (h.pow_const 2).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [one_div, Work.UBBInputs9.B.boxMean, hΦ]

/-! ## The transfer of the `ℝ≥0∞` bound to the `ℝ`-valued statement -/

/-- **The `ℝ`-valued statement from its `ℝ≥0∞` form.**  Taking the `ℝ≥0∞` sliding-box
mean-square bound (at `W = fun x => ENNReal.ofReal |w x|`, i.e. `Work.BoseFixB1S.meanSq3d_E3`)
as an explicit hypothesis, this is the whole content of `Work.BoseFixB1S.corrMeanSqRealE3`:
the transfer to the `ℝ`-valued statement, at the level of the *integrals* (never of the
integrands, where `ofReal` is not multiplicative). -/
theorem corrMS_of_enn {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {w : ℝ³ → ℝ} (hw : Continuous w)
    (hE3 : ∫⁻ u : ℝ³,
        ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, ENNReal.ofReal |w x|) /
          (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u))^2
      ≤ ENNReal.ofReal ((9/(ℓ*d))^3) *
        ∫⁻ x in Submission.BoseGases.acube ℓ, (ENNReal.ofReal |w x|)^2) :
    MeasureTheory.Integrable (fun u : ℝ³ =>
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
      ∧ (∫ u : ℝ³,
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
        ≤ (9/(ℓ*d))^3 *
          (∫ x in Submission.BoseGases.acube ℓ, (w x)^2) := by
  have hAEm : AEMeasurable
      (fun u : ℝ³ => ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2) (volume : Measure ℝ³) :=
    corrMS_aemeasurable_boxMean_sq hℓ hw
  have hpt : ∀ u : ℝ³, ENNReal.ofReal (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2) ≤
      ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, ENNReal.ofReal |w x|) /
        (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u))^2 :=
    fun u => corrMS_ofReal_boxMean_sq_le_lintegral hℓ hw u
  have hle : (∫⁻ u : ℝ³, ENNReal.ofReal (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2))
      ≤ ENNReal.ofReal ((9/(ℓ*d))^3) *
        ∫⁻ x in Submission.BoseGases.acube ℓ, (ENNReal.ofReal |w x|)^2 :=
    le_trans (lintegral_mono hpt) hE3
  rw [corrMS_lintegral_acube_ofReal_sq hℓ hw] at hle
  have hJnn : 0 ≤ ∫ x in Submission.BoseGases.acube ℓ, (w x)^2 :=
    integral_nonneg fun x => sq_nonneg _
  have hfin : ENNReal.ofReal ((9/(ℓ*d))^3) *
      ENNReal.ofReal (∫ x in Submission.BoseGases.acube ℓ, (w x)^2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hLt : (∫⁻ u : ℝ³, ENNReal.ofReal (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
      ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)) < ⊤ :=
    lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
  have hIeq : (∫ u : ℝ³, ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
      ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
      = (∫⁻ u : ℝ³, ENNReal.ofReal (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
      ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => sq_nonneg _)
      hAEm.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine ⟨hAEm.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    rw [show (∫⁻ a : ℝ³, ENNReal.ofReal ‖((1 / Work.SmallBoxSliding.boxMass ℓ d a) *
        ∫ x in Submission.BoseGases.dlBox ℓ d a, w x)^2‖)
        = ∫⁻ a : ℝ³, ENNReal.ofReal (((1 / Work.SmallBoxSliding.boxMass ℓ d a) *
        ∫ x in Submission.BoseGases.dlBox ℓ d a, w x)^2) from
      lintegral_congr fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]]
    exact hLt
  · rw [hIeq]
    calc (∫⁻ u : ℝ³, ENNReal.ofReal (((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)).toReal
        ≤ (ENNReal.ofReal ((9/(ℓ*d))^3) *
            ENNReal.ofReal (∫ x in Submission.BoseGases.acube ℓ, (w x)^2)).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = (9/(ℓ*d))^3 * (∫ x in Submission.BoseGases.acube ℓ, (w x)^2) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofReal hJnn]

/-- **The real-valued sliding-box mean-square bound** (the `ℝ`-valued counterpart of
`Work.BoseFixB1S.meanSq3d_E3`, for a continuous test function `w`).

For `0 < ℓ`, `0 < d ≤ 1` and continuous `w : EuclideanSpace ℝ (Fin 3) → ℝ`:

* `u ↦ ( (1/|B(u)|) ∫_{B(u)} w )²` is integrable (`B(u) = dlBox ℓ d u`, `|B(u)| = boxMass ℓ d u`),
* and its integral is at most `(9/(ℓ d))³ ∫_{acube ℓ} w²`.

PROOF ROUTE.  Apply the ENNReal bound `meanSq3d_E3` to
`W := fun x => ENNReal.ofReal |w x|` (measurable).  Pointwise
`ENNReal.ofReal ((1/boxMass u * ∫_{B(u)}w)²) ≤ ((∫⁻_{x∈B(u)} W x)/(volume (B(u))))²`:
use `|∫_{B(u)}w| ≤ ∫_{B(u)}|w|`, `ENNReal.ofReal (boxMass ℓ d u) = volume (dlBox ℓ d u)`
(`boxMass_eq_measureReal`, `lintegral_ofReal_boxInd`), and
`ENNReal.ofReal (∫_{B(u)}|w|) = ∫⁻_{x∈B(u)} W x`
(`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, with `w` continuous and `dlBox` bounded).
Then `∫_u (…)² = (∫⁻_u ofReal ((…)²)).toReal ≤ (ofReal ((9/(ℓd))³ ∫_{acube ℓ}w²)).toReal`, using
`ENNReal.toReal_mono` and, for the right-hand side,
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`.  `Integrable` follows from
`HasFiniteIntegral` (`MeasureTheory.hasFiniteIntegral_iff_norm`) and the a.e.-measurability of the
box mean (adapt `Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean` to `w`). -/
theorem corrMeanSqRealE3 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : Continuous w) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
      ∧ (∫ u : EuclideanSpace ℝ (Fin 3),
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x)^2)
        ≤ (9/(ℓ*d))^3 *
          (∫ x in Submission.BoseGases.acube ℓ, (w x)^2) := by
  refine corrMS_of_enn hℓ hd hd1 hw ?_
  have hW : Measurable (fun x : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal |w x|) :=
    (hw.abs).measurable.ennreal_ofReal
  refine Work.BoseFixB1.Smear.meanSq3dE3H hℓ hd hd1 ?_ hW
  intro F hF
  exact Work.BoseFixB1S.CorrMS.threeDim9 (ℓ := ℓ) (h := ℓ * d) (by positivity)
    (by nlinarith [hd1, hℓ])
    (fun {F'} hF' => Work.BoseFixB1S.CorrMS.oneDim9 (ℓ := ℓ) (h := ℓ * d) (by positivity)
      (by nlinarith [hd1, hℓ]) hF') hF

end Work.BoseFixB1S
