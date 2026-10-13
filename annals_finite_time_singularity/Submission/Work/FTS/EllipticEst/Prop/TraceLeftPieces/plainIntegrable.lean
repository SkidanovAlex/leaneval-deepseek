import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.TraceLeftPieces

set_option autoImplicit false

/-- On the open angular interval `(0, π/2)` the angular weight `sin(2θ)^{-η}` is `≥ 1`,
because `sin(2θ) ∈ (0,1]` there and the exponent `-η` is `≤ 0`. -/
private lemma one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : -(Work.Spaces.eta) ≤ 0 := by
    have := Work.Spaces.eta_pos
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge (x := Real.sin (2 * θ)) (y := 0)
    (z := -(Work.Spaces.eta)) hpos hle hη
  simpa [Work.FTS.EllipticEst.thEta] using h

/-- If `g · sin(2θ)^{-η}` is integrable on `Iθ` and `g` is almost everywhere strongly
measurable, then `g` is integrable on the open interval `(0, π/2)`: there the weight
`sin(2θ)^{-η}` dominates the constant `1`. -/
private lemma integrableOn_of_integrableOn_mul_thEta {g : ℝ → ℝ}
    (hm : AEStronglyMeasurable g (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
    (h : IntegrableOn (fun θ => g θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    IntegrableOn g (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩
  have h1 : Integrable (fun θ => g θ * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := h.mono_set hsub
  refine h1.mono hm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hth : 1 ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
  have hth0 : 0 ≤ Work.FTS.EllipticEst.thEta θ := le_trans zero_le_one hth
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hth0]
  simpa using mul_le_mul_of_nonneg_left hth (abs_nonneg (g θ))

/-- The product of two functions whose squares are integrable is integrable (AM–GM:
`|u v| ≤ (u² + v²)/2`), provided it is a.e. strongly measurable. -/
private lemma integrableOn_mul_of_integrableOn_sq {s : Set ℝ} {u v : ℝ → ℝ}
    (hu : IntegrableOn (fun x => u x ^ 2) s) (hv : IntegrableOn (fun x => v x ^ 2) s)
    (hm : AEStronglyMeasurable (fun x => u x * v x) (volume.restrict s)) :
    IntegrableOn (fun x => u x * v x) s := by
  have hsum : Integrable (fun x => (1 / 2 : ℝ) * (u x ^ 2 + v x ^ 2)) (volume.restrict s) :=
    (hu.add hv).const_mul (1 / 2 : ℝ)
  refine hsum.mono hm ?_
  filter_upwards with x
  have hS : 0 ≤ u x ^ 2 + v x ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg hS]
  have h2 : 2 * |u x| * |v x| ≤ u x ^ 2 + v x ^ 2 := by
    nlinarith [sq_nonneg (|u x| - |v x|), sq_abs (u x), sq_abs (v x)]
  linarith

theorem plainIntegrable (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hA1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hD : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv f θ) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hso : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsm : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hcf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hf.continuousOn
  have hcd : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen hso (by norm_num)
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.deriv_of_isOpen hso (m := 1) (by norm_num)
  have hcd2 : ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen hso (by norm_num)
  have hf2 : IntegrableOn (fun θ => f θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_of_integrableOn_mul_thEta (g := fun θ => f θ ^ 2)
      ((hcf.aestronglyMeasurable hsm).pow 2) hA
  have hg2 : IntegrableOn (fun θ => deriv f θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_of_integrableOn_mul_thEta (g := fun θ => deriv f θ ^ 2)
      ((hcd.aestronglyMeasurable hsm).pow 2) hA1
  have hh2 : IntegrableOn (fun θ => deriv (deriv f) θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_of_integrableOn_mul_thEta (g := fun θ => deriv (deriv f) θ ^ 2)
      ((hcd2.aestronglyMeasurable hsm).pow 2) hD
  refine ⟨hf2, hg2, hh2, ?_, ?_⟩
  · exact integrableOn_mul_of_integrableOn_sq hf2 hg2 ((hcf.mul hcd).aestronglyMeasurable hsm)
  · exact integrableOn_mul_of_integrableOn_sq hf2 hh2 ((hcf.mul hcd2).aestronglyMeasurable hsm)

end Work.FTS.EllipticEst.Prop.TraceLeftPieces
