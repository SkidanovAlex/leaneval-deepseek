import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_data
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.sliceL1_bound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ddG_sliceL1_bound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDzComm
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDzEq

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

/-- **The engine applied to `D_z G`**: the second log-radial derivative of `zmoll G δ ε` is the
folded `D_z²G` against the log-kernel. -/
theorem zmoll_dz2_eq (G : ℝ → ℝ → ℝ) (hT : TraceClass G) (hF : FourInts G) (δ ε : ℝ)
    (hP : Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Iθ,
      Dz (Dz (zmoll G δ ε)) z θ
        = ∫ t : ℝ, sKer δ (Real.log z - t)
            * (∫ s in Iθ, Kern (sKer ε) θ s * Dz (Dz G) (Real.exp t) s) := by
  obtain ⟨hsd1, hsd2, hsd3, hsd4, -, -, hsd7⟩ := slice_data hT
  obtain ⟨C₁, hC₁pos, hC₁int, hC₁b, hC₁int', hC₁b'⟩ := sliceL1_bound hT hF
  obtain ⟨C₂, hC₂pos, hC₂int, hC₂b⟩ := ddG_sliceL1_bound hT hF
  have hC₁nn : (0 : ℝ) ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : (0 : ℝ) ≤ C₂ := le_of_lt hC₂pos
  have hdnn : ∀ w : ℝ, 0 ≤ dIntS G w := by
    intro w
    rw [dIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  have hddnn : ∀ w : ℝ, 0 ≤ ddIntS G w := by
    intro w
    rw [ddIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  set F₂ : ℝ → ℝ := fun w => C₁ * (1 + dIntS G w) + C₂ * (1 + ddIntS G w) with hF₂def
  have hF₂int : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn F₂ (Set.Icc a b) := by
    intro a b ha hab
    rw [hF₂def]
    exact (hC₁int' a b ha hab).add (hC₂int a b ha hab)
  have hF₂b : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Dz G w s| ≤ F₂ w := by
    intro w hw
    rw [hF₂def]
    exact (hC₁b' w hw).trans (le_add_of_nonneg_right
      (mul_nonneg hC₂nn (by linarith [hddnn w])))
  have hF₂b' : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Dz (Dz G) w s| ≤ F₂ w := by
    intro w hw
    rw [hF₂def]
    exact (hC₂b w hw).trans (le_add_of_nonneg_left
      (mul_nonneg hC₁nn (by linarith [hdnn w])))
  have hc₂ := zmoll_dz_comm (u := Dz G) (F := F₂) hP hsd3 hsd4 hsd2 (hT.1.Dz).continuousOn
    (fun w hw s hs => (hT.1.Dz).hasDerivAt_slice hs hw) ((hT.1.Dz).pz).continuousOn
    hF₂int hF₂b hF₂b' (fun w hw => hsd7 w hw)
  have h1 := zmoll_dz_eq G hT hF δ ε hP
  intro z hz θ hθ
  have hdeq : deriv (fun z' : ℝ => Dz (zmoll G δ ε) z' θ) z
      = deriv (fun z' : ℝ => zmoll (Dz G) δ ε z' θ) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h1 z' hz' θ hθ
  calc Dz (Dz (zmoll G δ ε)) z θ
      = z * deriv (fun z' : ℝ => Dz (zmoll G δ ε) z' θ) z := by rw [Dz, pz]
    _ = z * deriv (fun z' : ℝ => zmoll (Dz G) δ ε z' θ) z := by rw [hdeq]
    _ = Dz (zmoll (Dz G) δ ε) z θ := by rw [Dz, pz]
    _ = ∫ t : ℝ, sKer δ (Real.log z - t)
          * (∫ s in Iθ, Kern (sKer ε) θ s * Dz (Dz G) (Real.exp t) s) := hc₂ z hz θ hθ

end Work.FTS.EllSol.EllPkgAux.MollDom
