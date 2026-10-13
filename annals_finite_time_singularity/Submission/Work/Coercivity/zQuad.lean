/-
# Quadrant bookkeeping for the `D_z`-coercivity assembly

The product of the two restricted measures on the quadrant, `wip`-congruence, and
additivity of `wip` in its first argument.  These are the measure-theoretic utilities
shared by the main file `zDerivative` and by the lower-order term estimates.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Coercivity.zAux
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.wip_eq_integral_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The product of the two restricted measures on the quadrant. -/
def quadMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)

theorem quadMeasure_eq : quadMeasure = volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
  rw [quadMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]

/-- `IntegrableOn` over the quadrant is integrability with respect to the product of the
two restricted measures. -/
theorem integrableOn_quadrant_iff (F : ℝ × ℝ → ℝ) :
    IntegrableOn F (Spaces.Iz ×ˢ Spaces.Iθ) ↔ Integrable F quadMeasure := by
  rw [quadMeasure, IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]

/-- A.e. on the quadrant, the point lies in `Iz ×ˢ Iθ`. -/
theorem ae_quadrant_mem : ∀ᵐ p ∂quadMeasure, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
  rw [quadMeasure_eq]
  exact ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)

/-- A.e. on the quadrant the radial variable is positive (`{0}` is null). -/
theorem ae_pos_fst_quadrant : ∀ᵐ p ∂quadMeasure, 0 < p.1 := by
  have hμ : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Spaces.Iz := by
    rw [Spaces.Iz]
    exact Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := 0))
  have hslice : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 0 < z := by
    rw [← hμ]
    exact ae_restrict_mem measurableSet_Ioi
  rw [quadMeasure]
  have h : ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (s := Set.Ioi (0 : ℝ) ×ˢ Set.univ)
      (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
      (hslice.mono (fun x hx => Filter.Eventually.of_forall (fun _ => by simp [hx])))
  filter_upwards [h] with p hp
  simpa using hp.1

/-- `wip` only sees its first argument through the quadrant integrand: two first arguments
agreeing on the open quadrant give the same `wip`. -/
theorem wip_congr_aeQ (ρ A B g : ℝ → ℝ → ℝ)
    (h : ∀ z θ, 0 < z → θ ∈ Spaces.Iθ → A z θ = B z θ) :
    wip ρ A g = wip ρ B g := by
  have hμ : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Spaces.Iz := by
    rw [Spaces.Iz]
    exact Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := 0))
  have hpos : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 0 < z := by
    rw [← hμ]
    exact ae_restrict_mem measurableSet_Ioi
  simp only [wip]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with z hz
  refine setIntegral_congr_fun measurableSet_Icc ?_
  intro θ hθ
  show A z θ * g z θ * ρ z θ = B z θ * g z θ * ρ z θ
  rw [h z θ hz hθ]

/-- Additivity of `wip` in its first argument, whenever both integrands are honest. -/
theorem wip_add (ρ A B g : ℝ → ℝ → ℝ)
    (hA : IntegrableOn
      (Function.uncurry (fun z θ => A z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hB : IntegrableOn
      (Function.uncurry (fun z θ => B z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    wip ρ (fun z θ => A z θ + B z θ) g = wip ρ A g + wip ρ B g := by
  have hA' : Integrable (fun p : ℝ × ℝ => A p.1 p.2 * g p.1 p.2 * ρ p.1 p.2)
      quadMeasure := (integrableOn_quadrant_iff _).mp hA
  have hB' : Integrable (fun p : ℝ × ℝ => B p.1 p.2 * g p.1 p.2 * ρ p.1 p.2)
      quadMeasure := (integrableOn_quadrant_iff _).mp hB
  have hsum : Integrable (fun p : ℝ × ℝ =>
      (A p.1 p.2 + B p.1 p.2) * g p.1 p.2 * ρ p.1 p.2) quadMeasure := by
    refine (hA'.add hB').congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.add_apply]
    ring
  rw [wip_eq_integral_prod ρ (fun z θ => A z θ + B z θ) g
        ((integrableOn_quadrant_iff _).mpr hsum),
      wip_eq_integral_prod ρ A g hA, wip_eq_integral_prod ρ B g hB]
  change (∫ p, (A p.1 p.2 + B p.1 p.2) * g p.1 p.2 * ρ p.1 p.2 ∂quadMeasure)
      = (∫ p, A p.1 p.2 * g p.1 p.2 * ρ p.1 p.2 ∂quadMeasure)
        + (∫ p, B p.1 p.2 * g p.1 p.2 * ρ p.1 p.2 ∂quadMeasure)
  rw [← MeasureTheory.integral_add hA' hB']
  apply integral_congr_ae
  filter_upwards with p
  ring

/-- Additivity of `IntegrableOn` for the `wip` integrands. -/
theorem wip_int_add (ρ A B g : ℝ → ℝ → ℝ)
    (hA : IntegrableOn
      (Function.uncurry (fun z θ => A z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hB : IntegrableOn
      (Function.uncurry (fun z θ => B z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    IntegrableOn
      (Function.uncurry (fun z θ => (A z θ + B z θ) * g z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  refine (hA.add hB).congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Function.uncurry_def, Pi.add_apply]
  ring

/-- A.e. for the restricted measure `volume.restrict (Iz ×ˢ Iθ)`: membership of the point. -/
theorem ae_mem_quadrant :
    ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)), p ∈ Spaces.Iz ×ˢ Spaces.Iθ :=
  ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)

/-- A.e. for the restricted measure: the radial variable is positive. -/
theorem ae_pos_fst_quadrant_restrict :
    ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)), 0 < p.1 := by
  rw [← quadMeasure_eq]
  exact ae_pos_fst_quadrant

end Work.Coercivity
