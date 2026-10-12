import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.SectorProj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

set_option linter.style.haveILetI false

open MeasureTheory

/-- **Cauchy–Schwarz on the support.**  For continuous compactly supported `f : ℝ³ → ℝ`,
`(∫ f)² ≤ (∫ f²)·|supp f|` (`|supp f|` the real Lebesgue volume of `Function.support f`).

Route: `μ := volume.restrict (Function.support f)` is a finite measure (`f` has compact support, so
its support has finite volume), `f` is bounded on the support (continuous + compact support), and
`Submission.BoseGases.cs_finite_measure` (declared in `Submission/SectorProj.lean`, import
`Submission.SectorProj`) gives `(∫ f ∂μ)² ≤ μ.real univ · ∫ f² ∂μ`; `setIntegral_support` converts
both restricted integrals back to integrals over `ℝ³`, and
`MeasureTheory.measureReal_restrict_apply_univ` identifies `μ.real univ` with
`volume.real (Function.support f)`.  (A self-contained route via
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2` and the constant function `1`
on the finite-measure space also works; importing `Submission.SectorProj` is allowed but optional.) -/
theorem sq_integral_le_integral_sq_mul_support {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) :
    (∫ x : EuclideanSpace ℝ (Fin 3), f x) ^ 2
      ≤ (∫ x : EuclideanSpace ℝ (Fin 3), (f x) ^ 2)
        * (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
            (Function.support f) := by
  -- Restrict the Lebesgue measure to the (compact) support of `f`.
  let μ : Measure (EuclideanSpace ℝ (Fin 3)) :=
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Function.support f)
  -- `μ` is a finite measure: the support is contained in the compact `tsupport`.
  have hfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    show μ Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (subset_tsupport f)) hcs.measure_lt_top
  haveI : IsFiniteMeasure μ := hfin
  -- `f` is bounded (continuous with compact support).
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hf
  have hm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, |f x| ≤ C := ae_of_all _ (fun x => by
    simpa [Real.norm_eq_abs] using hC x)
  -- Cauchy–Schwarz on the finite measure space.
  have hmain := Submission.BoseGases.cs_finite_measure (μ := μ) (f := f) hm hb
  -- Convert the two restricted integrals back to integrals over `ℝ³`.
  have h1 : (∫ x, f x ∂μ) = ∫ x, f x := by
    change (∫ x in Function.support f, f x) = ∫ x, f x
    exact setIntegral_support
  have h2 : (∫ x, (f x) ^ 2 ∂μ) = ∫ x, (f x) ^ 2 := by
    have hsp : Function.support (fun x : EuclideanSpace ℝ (Fin 3) => (f x) ^ 2)
        = Function.support f := by
      ext x
      simp [Function.mem_support]
    change (∫ x in Function.support f, (f x) ^ 2) = ∫ x, (f x) ^ 2
    rw [← hsp]
    exact setIntegral_support
  -- The mass of `μ` is the volume of the support.
  have hvol : μ.real Set.univ
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
          (Function.support f) :=
    measureReal_restrict_apply_univ _
  rw [h1, h2, hvol] at hmain
  rwa [mul_comm] at hmain

end Work.UBBInputs8.A
