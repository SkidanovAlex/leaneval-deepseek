import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_data
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.sliceL1_bound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDzComm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c
open Work.Spaces (Dz pz)
open Work.EllipticEst.Core

local notation "Iθ" => Work.Spaces.Iθ

set_option maxHeartbeats 4000000

/-- **The engine applied to `G`**: the log-mollification commutes with `D_z`,
`D_z (zmoll G δ ε) z θ = zmoll (D_z G) δ ε z θ` for `z > 0`, `θ ∈ Iθ`. -/
theorem zmoll_dz_eq (G : ℝ → ℝ → ℝ) (hT : TraceClass G) (hF : FourInts G) (δ ε : ℝ)
    (hP : Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Iθ,
      Dz (zmoll G δ ε) z θ = zmoll (Dz G) δ ε z θ := by
  obtain ⟨hsd1, hsd2, hsd3, hsd4, -, -, -⟩ := slice_data hT
  obtain ⟨C, hCpos, hCint, hCb, hCint', hCb'⟩ := sliceL1_bound hT hF
  have hCnn : (0 : ℝ) ≤ C := le_of_lt hCpos
  have hdnn : ∀ w : ℝ, 0 ≤ dIntS G w := by
    intro w
    rw [dIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  set F₁ : ℝ → ℝ := fun w => C * MGf G w + C * (1 + dIntS G w) with hF₁def
  have hF₁int : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn F₁ (Set.Icc a b) := by
    intro a b ha hab
    rw [hF₁def]
    exact (hCint a b ha hab).add (hCint' a b ha hab)
  have hF₁b : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |G w s| ≤ F₁ w := by
    intro w hw
    rw [hF₁def]
    exact (hCb w hw).trans (le_add_of_nonneg_right
      (mul_nonneg hCnn (by linarith [hdnn w])))
  have hF₁b' : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Dz G w s| ≤ F₁ w := by
    intro w hw
    rw [hF₁def]
    have hmg : (0 : ℝ) ≤ C * MGf G w := by
      rw [MGf]
      exact mul_nonneg hCnn (by positivity)
    exact (hCb' w hw).trans (le_add_of_nonneg_left hmg)
  have hc := zmoll_dz_comm (u := G) (F := F₁) hP hT.2.1 hT.2.2.1 hsd1 hT.1.continuousOn
    (fun w hw s hs => hT.1.hasDerivAt_slice hs hw) (hT.1.pz).continuousOn hF₁int hF₁b hF₁b'
    (fun w hw => (hsd2 w hw).integrableOn_compact isCompact_Icc)
  intro z hz θ hθ
  rw [hc z hz θ hθ]
  rw [show zmoll (Dz G) δ ε z θ
      = ∫ t : ℝ, sKer δ (Real.log z - t) * thMoll (Dz G) ε (Real.exp t) θ from rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show sKer δ (Real.log z - t)
      * (∫ s in Iθ, Kern (sKer ε) θ s * Dz G (Real.exp t) s)
    = sKer δ (Real.log z - t) * thMoll (Dz G) ε (Real.exp t) θ
  rw [← thMoll_fold (u := Dz G) (z := Real.exp t) (θ' := θ) hP.1 hP.2.1
    (hsd3 (Real.exp t)) (hsd4 (Real.exp t)) (hsd2 (Real.exp t) (Real.exp_pos t))
    (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])]

end Work.FTS.EllSol.EllPkgAux.MollDom
