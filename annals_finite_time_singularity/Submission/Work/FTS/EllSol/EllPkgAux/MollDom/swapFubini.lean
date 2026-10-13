import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem swapFubini {k : ℝ → ℝ} {v : ℝ → ℝ → ℝ} {ε θ σ : ℝ}
    (h : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => k (σ - p.1) * Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2 * v p.1 p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ t : ℝ, k (σ - t) * (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * v t s))
      = ∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * (∫ t : ℝ, k (σ - t) * v t s) := by
  -- Fubini/Tonelli for the product measure `volume × (volume ↾ Iθ)`: both sides are the
  -- iterated integral of the single product integrand, so both equal its product integral.
  set F : ℝ × ℝ → ℝ :=
    fun p => k (σ - p.1) * Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2 * v p.1 p.2
    with hFdef
  -- left-hand side: the `t`-integral of the `Iθ`-integral
  have hlhs : (∫ t : ℝ, k (σ - t) * (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integral_prod F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (k (σ - t))
      (fun s => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * v t s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F]
    ring
  -- right-hand side: the `Iθ`-integral of the `t`-integral
  have hrhs : (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * (∫ t : ℝ, k (σ - t) * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integral_prod_symm F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (Work.FTS.EllSol.EllPkgAux.Kern
      (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s) (fun t => k (σ - t) * v t s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [F]
    ring
  exact hlhs.trans hrhs.symm

end Work.FTS.EllSol.EllPkgAux.MollDom
