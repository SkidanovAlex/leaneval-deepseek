import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollDzPthConv
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zMixedDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thMoll_pth_fold
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixed_id
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix.integrable_sKerd_KJ_pth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

local notation "Iθ" => Work.Spaces.Iθ

/-- **Fubini for the angular kernel `KJ` and a compactly supported radial kernel.**

For a radial kernel `k` and a function `v` whose product against `k (σ - ·)` is jointly
integrable for the product measure `volume × (volume ↾ Iθ)`, the two iterated integrals of
`k (σ - t) · KJ ε θ s · v t s` agree.  This is the `KJ`-analogue of `swapFubini` (which is
stated for the folded kernel `Kern (sKer ε)`); both are the same computation, namely that each
side is the product integral of the single joint integrand
(`MeasureTheory.integral_prod` / `MeasureTheory.integral_prod_symm`), after moving the constants
`k (σ - t)` resp. `KJ ε θ s` in and out of the inner integral
(`MeasureTheory.integral_const_mul`). -/
theorem swapFubini_KJ {k : ℝ → ℝ} {v : ℝ → ℝ → ℝ} {ε θ σ : ℝ}
    (h : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => k (σ - p.1) * (Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * v p.1 p.2))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ))) :
    (∫ t : ℝ, k (σ - t) * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * v t s))
      = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * (∫ t : ℝ, k (σ - t) * v t s) := by
  set F : ℝ × ℝ → ℝ := fun p => k (σ - p.1) * (Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * v p.1 p.2)
    with hFdef
  have hlhs : (∫ t : ℝ, k (σ - t) * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ)) := by
    rw [MeasureTheory.integral_prod F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (k (σ - t))
      (fun s => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * v t s)]
  have hrhs : (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * (∫ t : ℝ, k (σ - t) * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ)) := by
    rw [MeasureTheory.integral_prod_symm F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (Work.FTS.EllSol.EllPkgAux.KJ ε θ s)
      (fun t => k (σ - t) * v t s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [F]
    ring
  exact hlhs.trans hrhs.symm

theorem zmoll_mixed_conv (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ
        = ∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
            * Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z := by
  intro z hz θ hθ
  -- the mixed derivative, with the two differentiations detached
  rw [Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixed_id G hT hF δ ε hP z hz θ hθ]
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  -- unfold the Schur operator on the right-hand side
  rw [show (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
        * Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z)
      = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
          * (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
              * Work.Spaces.pth G (Real.exp t) s) from rfl]
  -- the angular derivative of the angular mollification, as the `KJ`-fold
  have hstep1 : (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
        * Work.Spaces.pth (fun z' θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z' θ')
            (Real.exp t) θ)
      = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
          * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
              * Work.Spaces.pth G (Real.exp t) s) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [Work.FTS.EllSol.EllPkgAux.MollDom.thMoll_pth_fold G hT ε hε0 hε1
      (Real.exp t) (Real.exp_pos t) θ hθ]
    simp only [Work.FTS.EllSol.EllPkgAux.KJ]
  -- exchange the two integrations
  have hstep2 := swapFubini_KJ (k := Work.FTS.EllSol.EllPkgAux.sKerd δ)
    (v := fun t s => Work.Spaces.pth G (Real.exp t) s) (ε := ε) (θ := θ) (σ := Real.log z)
    (Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix.integrable_sKerd_KJ_pth G hT hF δ ε
      hδ0 hδ1 hε0 hε1 hz hθ)
  exact hstep1.trans hstep2

end Work.FTS.EllSol.EllPkgAux.MollDom
