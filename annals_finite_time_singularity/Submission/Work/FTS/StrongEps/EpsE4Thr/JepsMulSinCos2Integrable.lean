import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.JepsSmoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- The open-quadrant smoothness of `W` in the raw `∀ n`-form used by the `J_ε`-API
(`SmoothOpen` is definitionally `ContDiffOn ℝ smoothOrder (uncurry ·) Q0`). -/
theorem smoothOpen_forall_of_smoothOpen {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry W)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall W).mp hsm n

/-- **Integrability of the `sin θ cos²θ`-moment of the mollified slice.**

`J_ε W` is `C^∞` on the open quadrant and, being a mollification of an `ℋ^1`-profile, is
honestly `ℋ^0`; the level-`0` honesty alone controls the angular endpoints (its weight
`sin(2θ)^{-η/2}` with `η = 99/100 < 1` forces `|W| ≲ sin(2θ)^{-a}` with `a < 1/200`), so the
bounded multiplier `sinCos2` is integrable against the slice. -/
theorem integrableOn_Jeps_mul_sinCos2 {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  intro r hr
  -- the raw `∀ n`-form of the smoothness of `W`, and the descent `ℋ¹ ⟹ ℋ⁰`
  have hsmW := smoothOpen_forall_of_smoothOpen hsm
  have hmem0W : Work.Spaces.HkMem α 0 W :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 1)
      (by norm_num) hsmW hmem
  -- `J_ε W` is again `ℋ⁰` and `C^∞` on the open quadrant
  have hmem0J : Work.Spaces.HkMem α 0 (Work.FTS.StrongEps.Jeps ρ ε W) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmW hmem0W
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε W) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmW
  -- the level-`0` absorption `|g·sinCos2| ≤ (g·w/sin^{η/2})² + 1` on the slice
  have hcont : ContinuousOn (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε W))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsmJ.continuousOn
  have hmain : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hcont hmem0J hr
  exact hmain

theorem JepsMulSinCos2Integrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {W : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
  integrableOn_Jeps_mul_sinCos2 hρ hε hα hsm hmem

end Work.FTS.StrongEps.EpsE4Thr
