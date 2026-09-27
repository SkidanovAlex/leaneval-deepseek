import Mathlib
import Submission.Mostow.Interfaces

/-!
# Area V (`volumeSqueeze`) — shared vocabulary

Definitions and elementary facts about the hyperbolic volume `volH`, the weight
`tpart⁻¹` and the hyperbolic Jacobian `hjac`, used by `Work.Mostow.volumeSqueeze`
and by the delegated chapters of area V.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

variable {n : ℕ}

/-- The density of hyperbolic volume with respect to Lebesgue measure in the chart. -/
def hdens (u : E n) : ℝ≥0∞ := ENNReal.ofReal (tpart u)⁻¹

/-- The Lebesgue-measure weight attached to a `C¹` map `F`: the hyperbolic volume of the
image is controlled by integrating this against Lebesgue measure. -/
def hjacLeb (F : E n → E n) (u : E n) : ℝ≥0∞ :=
  ENNReal.ofReal |(fderiv ℝ F u).det| * hdens (F u)

@[simp] theorem hdens_apply (u : E n) : hdens u = ENNReal.ofReal (tpart u)⁻¹ := rfl

theorem tpart_pos (u : E n) : 0 < tpart u := by
  rw [tpart, Real.sqrt_pos]
  positivity

theorem one_le_tpart_VolDefs (u : E n) : 1 ≤ tpart u := by
  rw [tpart]
  apply Real.le_sqrt_of_sq_le
  have : (0:ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
  linarith

theorem continuous_tpart_VolDefs : Continuous (tpart : E n → ℝ) :=
  Real.continuous_sqrt.comp (by fun_prop)

theorem hdens_pos (u : E n) : 0 < hdens u := by
  rw [hdens, ENNReal.ofReal_pos]
  exact inv_pos.mpr (tpart_pos u)

theorem hdens_ne_zero (u : E n) : hdens u ≠ 0 := ne_of_gt (hdens_pos u)

theorem measurable_hdens : Measurable (hdens : E n → ℝ≥0∞) :=
  Measurable.comp ENNReal.measurable_ofReal
    ((continuous_tpart_VolDefs.inv₀ (fun u => ne_of_gt (tpart_pos u))).measurable)

theorem volH_def (n : ℕ) : volH n = (volume : Measure (E n)).withDensity (hdens : E n → ℝ≥0∞) :=
  rfl

theorem volHApply (n : ℕ) {s : Set (E n)} (hs : MeasurableSet s) :
    volH n s = ∫⁻ u in s, hdens u ∂(volume : Measure (E n)) := by
  rw [volH_def, withDensity_apply _ hs]

theorem hjac_eq (F : E n → E n) (u : E n) :
    hjac F u = |(fderiv ℝ F u).det| * (tpart u / tpart (F u)) := rfl

theorem hjac_nonneg (F : E n → E n) (u : E n) : 0 ≤ hjac F u :=
  mul_nonneg (abs_nonneg _) (le_of_lt (div_pos (tpart_pos u) (tpart_pos (F u))))

theorem volHNull (n : ℕ) {s : Set (E n)} :
    volH n s = 0 ↔ (volume : Measure (E n)) s = 0 := by
  rw [volH_def, MeasureTheory.withDensity_apply_eq_zero measurable_hdens]
  have h : {x : E n | hdens x ≠ 0} = Set.univ := Set.eq_univ_of_forall (fun x => hdens_ne_zero x)
  rw [h, Set.univ_inter]

theorem volHPosOpen (n : ℕ) {U : Set (E n)} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < volH n U := by
  rw [pos_iff_ne_zero]
  intro h0
  exact hU.measure_ne_zero (volume : Measure (E n)) hne ((volHNull n).mp h0)

theorem hjacContinuous (n : ℕ) {F : E n → E n} (hF : ContDiff ℝ 1 F) : Continuous (hjac F) := by
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have h1 : Continuous fun u : E n => |(fderiv ℝ F u).det| :=
    (ContinuousLinearMap.continuous_det.comp hfd).abs
  have h2 : Continuous fun u : E n => tpart u := continuous_tpart_VolDefs
  have h3 : Continuous fun u : E n => tpart (F u) := continuous_tpart_VolDefs.comp hF.continuous
  have h4 : Continuous fun u : E n => tpart u / tpart (F u) :=
    h2.div h3 (fun u => ne_of_gt (tpart_pos (F u)))
  exact h1.mul h4

theorem hjacComp (n : ℕ) {F G : E n → E n} {u : E n}
    (hF : DifferentiableAt ℝ F (G u)) (hG : DifferentiableAt ℝ G u) :
    hjac (F ∘ G) u = hjac F (G u) * hjac G u := by
  have hdet : (fderiv ℝ (F ∘ G) u).det = (fderiv ℝ F (G u)).det * (fderiv ℝ G u).det := by
    rw [fderiv_comp u hF hG]
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  rw [hjac_eq, hjac_eq, hjac_eq, hdet, abs_mul, Function.comp_apply]
  have hy : tpart (G u) ≠ 0 := ne_of_gt (tpart_pos (G u))
  have hz : tpart (F (G u)) ≠ 0 := ne_of_gt (tpart_pos (F (G u)))
  field_simp
  try ring

end

end Work.Mostow
