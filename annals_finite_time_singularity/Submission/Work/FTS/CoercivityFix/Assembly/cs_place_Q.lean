import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.Coercivity.integrable_sqrt_mul_sqrt
import Submission.Work.Spaces.ProductTools
import Submission.Work.FTS.CoercivityStep.Base.H1IP_cs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

/-- Two-dimensional (iterated) Cauchy–Schwarz for the quadrant measure: for `L²`-blocks `X`, `Y`
that are a.e. strongly measurable on every angular slice and on the product measure,
`|∫_z ∫_θ X·Y| ≤ √(∫∫X²)·√(∫∫Y²)`.

ROUTE.  `Submission/Work/FTS/CoercivityStep/Base/H1IP_cs.lean` contains a `private` proof of
exactly this statement (the lemma `cs_place` there); it is used only inside that file, so it must
be reproduced here.  The proof is Cauchy–Schwarz twice: on each angular slice
(`Work.Coercivity.holder_two_mul` with the functions `X z`, `Y z`), then in the radial variable
applied to `z ↦ √(∫_θ X(z,θ)²)` and `z ↦ √(∫_θ Y(z,θ)²)`, which are integrable by
`Work.Coercivity.integrable_sqrt_mul_sqrt`.  The integrability/measurability of the two pieces
is obtained from `Spaces.L2Mem` and the a.e. strong measurability hypotheses via
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` and `Integrable.mono'`. -/
theorem cs_place_Q (X Y : ℝ → ℝ → ℝ)
    (hX : Work.Spaces.L2Mem X) (hY : Work.Spaces.L2Mem Y)
    (hXs : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => X z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hYs : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Y z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hXp : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hYp : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Y p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, X z θ * Y z θ|
      ≤ Real.sqrt (Work.Spaces.L2Sq X) * Real.sqrt (Work.Spaces.L2Sq Y) := by
  set A : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (X z θ) ^ 2 with hAdef
  set B : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (Y z θ) ^ 2 with hBdef
  have hAint : Integrable A (volume.restrict Spaces.Iz) := by
    rw [hAdef]; exact hX.2
  have hBint : Integrable B (volume.restrict Spaces.Iz) := by
    rw [hBdef]; exact hY.2
  have hAnonneg : ∀ z, 0 ≤ A z := by
    intro z; rw [hAdef]; exact integral_nonneg fun θ => sq_nonneg _
  have hBnonneg : ∀ z, 0 ≤ B z := by
    intro z; rw [hBdef]; exact integral_nonneg fun θ => sq_nonneg _
  -- Cauchy–Schwarz on every angular slice.
  have hslice : ∀ z ∈ Spaces.Iz,
      |∫ θ in Spaces.Iθ, X z θ * Y z θ| ≤ Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z hz
    have h := Coercivity.holder_two_mul (volume.restrict Spaces.Iθ) (X z) (Y z)
      (hXs z hz) (hYs z hz) (hX.1 z hz) (hY.1 z hz)
    simpa only [hAdef, hBdef] using h.2
  -- The dominating function is integrable.
  have hGint : Integrable (fun z => Real.sqrt (A z) * Real.sqrt (B z))
      (volume.restrict Spaces.Iz) :=
    Coercivity.integrable_sqrt_mul_sqrt _ A B hAint hBint hAnonneg hBnonneg
  -- The outer integrand is a.e. strongly measurable.
  have hFmeas : AEStronglyMeasurable (fun z => ∫ θ in Spaces.Iθ, X z θ * Y z θ)
      (volume.restrict Spaces.Iz) := by
    have h : AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2 * Y p.1 p.2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := hXp.mul hYp
    have := h.integral_prod_right' (μ := volume.restrict Spaces.Iz)
      (ν := volume.restrict Spaces.Iθ)
    simpa using this
  have hFint : Integrable (fun z => ∫ θ in Spaces.Iθ, X z θ * Y z θ)
      (volume.restrict Spaces.Iz) := by
    refine hGint.mono' hFmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    simpa only [Real.norm_eq_abs] using hslice z hz
  -- Measurability and integrability of the two square-root functions in `z`.
  have hAmeas : AEStronglyMeasurable A (volume.restrict Spaces.Iz) := by
    rw [hAdef]
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (X p.1 p.2) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := hXp.pow 2
    have := h2.integral_prod_right' (μ := volume.restrict Spaces.Iz)
      (ν := volume.restrict Spaces.Iθ)
    simpa using this
  have hBmeas : AEStronglyMeasurable B (volume.restrict Spaces.Iz) := by
    rw [hBdef]
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Y p.1 p.2) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := hYp.pow 2
    have := h2.integral_prod_right' (μ := volume.restrict Spaces.Iz)
      (ν := volume.restrict Spaces.Iθ)
    simpa using this
  have hAsq : Integrable (fun z => (Real.sqrt (A z)) ^ 2) (volume.restrict Spaces.Iz) :=
    hAint.congr (Eventually.of_forall fun z => (Real.sq_sqrt (hAnonneg z)).symm)
  have hBsq : Integrable (fun z => (Real.sqrt (B z)) ^ 2) (volume.restrict Spaces.Iz) :=
    hBint.congr (Eventually.of_forall fun z => (Real.sq_sqrt (hBnonneg z)).symm)
  have hcs2 := Coercivity.holder_two_mul (volume.restrict Spaces.Iz)
    (fun z => Real.sqrt (A z)) (fun z => Real.sqrt (B z))
    (Real.continuous_sqrt.comp_aestronglyMeasurable hAmeas)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hBmeas) hAsq hBsq
  have hfA : (∫ z in Spaces.Iz, (Real.sqrt (A z)) ^ 2) = ∫ z in Spaces.Iz, A z :=
    integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hAnonneg z))
  have hfB : (∫ z in Spaces.Iz, (Real.sqrt (B z)) ^ 2) = ∫ z in Spaces.Iz, B z :=
    integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hBnonneg z))
  calc |∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, X z θ * Y z θ|
      ≤ ∫ z in Spaces.Iz, |∫ θ in Spaces.Iθ, X z θ * Y z θ| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z in Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hGint
          (ae_restrict_of_forall_mem measurableSet_Ici hslice)
    _ = |∫ z in Spaces.Iz, Real.sqrt (A z) * Real.sqrt (B z)| :=
        (abs_of_nonneg (integral_nonneg fun z =>
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    _ ≤ Real.sqrt (∫ z in Spaces.Iz, (Real.sqrt (A z)) ^ 2)
          * Real.sqrt (∫ z in Spaces.Iz, (Real.sqrt (B z)) ^ 2) := hcs2.2
    _ = Real.sqrt (Spaces.L2Sq X) * Real.sqrt (Spaces.L2Sq Y) := by
        rw [hfA, hfB, hAdef, hBdef]
        rfl

end Work.FTS.CoercivityFix.Assembly

end
