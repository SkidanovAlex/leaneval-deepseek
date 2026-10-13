import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.mixedRadialThetaMul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- The angular datum `θ ↦ sin²θ`, viewed as a function of `(z,θ)`, is `C^∞` on the open
quadrant `Q0 = (0,∞) × (0,π/2)`. -/
theorem fkSinSqLeibniz_sinSq_smoothOpen :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ (θ : ℝ) => Real.sin θ ^ 2)) Work.FTS.EllipticEst.Q0
  fun_prop

theorem fkSinSqLeibniz :
    ∀ (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g → ∀ (j a : ℕ), j + a ≤ 6 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j a (fun z θ => Real.sin θ ^ 2 * g z θ) z θ
          = ∑ r ∈ Finset.range (a + 1), (a.choose r : ℝ)
              * (Work.Spaces.DthIter r (fun _ θ' => Real.sin θ' ^ 2) z θ
                  * Work.Spaces.mixed j (a - r) g z θ) := by
  intro g hg j a _hja z θ hz hθ hθ2
  exact Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.thetaOnlyLeibniz
    (γ := fun θ' => Real.sin θ' ^ 2) fkSinSqLeibniz_sinSq_smoothOpen hg j a z θ hz hθ hθ2

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
