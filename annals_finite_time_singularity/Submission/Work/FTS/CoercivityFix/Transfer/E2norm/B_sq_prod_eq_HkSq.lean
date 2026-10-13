import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

theorem B_sq_prod_eq_HkSq (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.Dth f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      ∫ p, (Work.Spaces.Dth f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
  -- The `ℋ⁰`-integrand of `D_θ f` is *definitionally* the square of `D_θ f · w/ sin(2θ)^{η/2}`:
  -- at `k = 0` the mixed (`i ≥ 1`) double sum of `HkIntegrand` is empty.
  have hpt : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth f) z θ
      = (Work.Spaces.Dth f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro z θ
    simp only [Work.Spaces.HkIntegrand]
    simp
  -- `D_θ f` is `C^∞` on the open quadrant, so its `ℋ⁰`-integrand is continuous there, hence
  -- a.e. strongly measurable for the product measure (the complement of the quadrant in
  -- `Iz × Iθ` is the union of the three null segments `{0} × Iθ`, `Iz × {0}`, `Iz × {π/2}`).
  have hDth : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) :=
    Work.FTS.LocData.contDiffOn_Dth Work.Spaces.isOpen_quadU hsm
  have hAE : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.Dth f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 0 (Work.Spaces.Dth f) hDth)).congr
      (Filter.Eventually.of_forall fun p => hpt p.1 p.2)
  -- Tonelli–Fubini, fed by the two halves of `HkMem`.
  obtain ⟨hint, hval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => (Work.Spaces.Dth f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun z θ => sq_nonneg _) hAE
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      (hmem.1 z hz).congr (Filter.Eventually.of_forall fun θ => hpt z θ))
    (by
      have heq : (fun a : ℝ => ∫ b, (Work.Spaces.Dth f a b
              * (Work.Spaces.w a / (Real.sin (2 * b)) ^ (Work.Spaces.eta / 2))) ^ 2
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = fun a : ℝ => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth f) a θ := by
        funext a
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun b => (hpt a b).symm)
      rw [heq]
      exact hmem.2)
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [Work.Spaces.HkSq]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  exact (hpt a b).symm

end Work.FTS.CoercivityFix.Transfer.E2norm
