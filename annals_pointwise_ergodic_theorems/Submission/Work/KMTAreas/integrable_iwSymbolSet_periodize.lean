import Mathlib
import Submission.Work.Analysis.IWMultiplier.Basic
import Submission.Work.KMTAreas.schwartz_decay_bound
import Submission.Work.KMTAreas.schwartz_shift_summable
import Submission.Work.KMTAreas.tsum_inv_sq_shift_le

/-!
# Integrability of the IW symbol of the periodisation of a Schwartz function

For a Schwartz symbol `φ : ℝ → ℂ` the periodisation
`periodize φ ξ = ∑' k : ℤ, φ (x + k)` (`x ∈ [0,1)` the canonical representative of `ξ ∈ ℝ/ℤ`)
is bounded: the Schwartz decay bound `‖φ t‖ ≤ C / (1 + |t|)^2` together with the uniform bound
`∑_{k : ℤ} 1 / (1 + (x + k)^2) ≤ B` (independent of `x`) gives `‖periodize φ ξ‖ ≤ C * B`.
The series is a sum of measurable functions, so the periodisation is a.e. measurable, and hence
`periodize φ ∈ L^∞(ℝ/ℤ)`, in particular integrable.  Translating a symbol by a fixed frequency
preserves `L^∞`, so the IW symbol `iwSymbolSet A (periodize φ) = ∑_{α ∈ A} (periodize φ) (· - α)`
is again in `L^∞(ℝ/ℤ)`, hence integrable on the probability space `ℝ/ℤ`.

Note that no support hypothesis on `φ` is needed (unlike `memLp_periodize`): the decay of the
Schwartz function replaces compact support.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KMTAreas

open MeasureTheory

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- The canonical representative `ℝ/ℤ → [0,1)` is measurable. -/
private lemma measurable_equivIco_val_circle :
    Measurable fun ξ : Circ => (AddCircle.equivIco (1 : ℝ) 0 ξ).val :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

/-- Each summand `ξ ↦ φ (x(ξ) + k)` of the periodisation of a measurable `φ` is measurable. -/
private lemma measurable_periodizeTerm {φ : ℝ → ℂ} (hφ : Measurable φ) (k : ℤ) :
    Measurable fun ξ : Circ =>
      φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ)) :=
  hφ.comp (measurable_equivIco_val_circle.add measurable_const)

/-- The periodisation of a Schwartz function is a.e. measurable: it is the sum of the measurable
functions `ξ ↦ φ (x(ξ) + k)`. -/
private lemma aemeasurable_periodize_schwartz (φ : SchwartzMap ℝ ℂ) :
    AEMeasurable (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ))
      Work.Analysis.IonescuWainger.circleMeasure := by
  have h : AEMeasurable
      (fun ξ : Circ => ∑' k : ℤ, (φ : ℝ → ℂ)
        ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ)))
      Work.Analysis.IonescuWainger.circleMeasure :=
    AEMeasurable.tsum fun k =>
      (measurable_periodizeTerm φ.continuous.measurable k).aemeasurable
  unfold Work.Analysis.IonescuWainger.periodize
  exact h

/-- The periodisation of a Schwartz function is bounded: for every `ξ` the series is dominated by
`C ∑_{k} 1 / (1 + (x + k)^2)`, and this is at most `C * B` with `B` independent of `x`. -/
private lemma norm_periodize_schwartz_le (φ : SchwartzMap ℝ ℂ) :
    ∃ Cb : ℝ, ∀ ξ : Circ,
      ‖Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ) ξ‖ ≤ Cb := by
  obtain ⟨C, hC0, hC⟩ := Work.KMTAreas.schwartz_decay_bound φ
  obtain ⟨B, hB0, hB⟩ := Work.KMTAreas.tsum_inv_sq_shift_le
  refine ⟨C * B, fun ξ => ?_⟩
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hx
  have hξ : Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ) ξ
      = ∑' k : ℤ, (φ : ℝ → ℂ) (x + (k : ℝ)) := by
    rw [Work.Analysis.IonescuWainger.periodize]
  have hsumφ : Summable fun k : ℤ => ‖(φ : ℝ → ℂ) (x + (k : ℝ))‖ :=
    Work.KMTAreas.schwartz_shift_summable φ x
  have hsumg : Summable fun k : ℤ => C * (1 / (1 + (x + (k : ℝ)) ^ 2)) :=
    (hB x).1.mul_left C
  have hterm : ∀ k : ℤ,
      ‖(φ : ℝ → ℂ) (x + (k : ℝ))‖ ≤ C * (1 / (1 + (x + (k : ℝ)) ^ 2)) := by
    intro k
    have hle : 1 + (x + (k : ℝ)) ^ 2 ≤ (1 + |x + (k : ℝ)|) ^ 2 := by
      nlinarith [sq_abs (x + (k : ℝ)), abs_nonneg (x + (k : ℝ))]
    have hpos : (0 : ℝ) < 1 + (x + (k : ℝ)) ^ 2 := by positivity
    have h3 : 1 / (1 + |x + (k : ℝ)|) ^ 2 ≤ 1 / (1 + (x + (k : ℝ)) ^ 2) :=
      one_div_le_one_div_of_le hpos hle
    calc ‖(φ : ℝ → ℂ) (x + (k : ℝ))‖ ≤ C / (1 + |x + (k : ℝ)|) ^ 2 := hC _
      _ = C * (1 / (1 + |x + (k : ℝ)|) ^ 2) := by rw [mul_one_div]
      _ ≤ C * (1 / (1 + (x + (k : ℝ)) ^ 2)) := mul_le_mul_of_nonneg_left h3 hC0
  rw [hξ]
  calc ‖∑' k : ℤ, (φ : ℝ → ℂ) (x + (k : ℝ))‖
      ≤ ∑' k : ℤ, ‖(φ : ℝ → ℂ) (x + (k : ℝ))‖ := norm_tsum_le_tsum_norm hsumφ
    _ ≤ ∑' k : ℤ, C * (1 / (1 + (x + (k : ℝ)) ^ 2)) :=
        Summable.tsum_le_tsum hterm hsumφ hsumg
    _ = C * ∑' k : ℤ, (1 / (1 + (x + (k : ℝ)) ^ 2)) := tsum_mul_left
    _ ≤ C * B := mul_le_mul_of_nonneg_left (hB x).2 hC0

/-- The periodisation of a Schwartz function is in `L^∞(ℝ/ℤ)`. -/
theorem memLp_periodize_schwartz (φ : SchwartzMap ℝ ℂ) :
    MemLp (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ))
      ⊤ Work.Analysis.IonescuWainger.circleMeasure := by
  obtain ⟨Cb, hCb⟩ := norm_periodize_schwartz_le φ
  exact memLp_top_of_bound (aemeasurable_periodize_schwartz φ).aestronglyMeasurable Cb
    (Filter.Eventually.of_forall hCb)

/-- The IW symbol over a finite set of arithmetic frequencies of the periodisation of a Schwartz
function is integrable on the circle: it lies in `L^∞` and the circle has finite measure. -/
theorem integrable_iwSymbolSet_periodize (A : Finset Work.Analysis.IonescuWainger.Circle)
    (φ : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)))
      Work.Analysis.IonescuWainger.circleMeasure :=
  (Work.Analysis.IWMultiplier.memLp_iwSymbolSet A (memLp_periodize_schwartz φ)).integrable le_top

end Work.KMTAreas
