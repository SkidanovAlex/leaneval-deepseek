/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Dth_Lhat_O.lean` — `D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` in the **open** class `SmoothOpen`

The open-class (`SmoothOpen`, i.e. genuine `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, the
class carried by `RegQo`) twin of `Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat`, which is stated
for the interior class `Work.FTS.LocData.SmoothQuad` (`C^∞` on the strip `z > -1`).

Nothing in the proof of `Dth_Lhat` uses the strip `z > -1` beyond the *open-quadrant*
differentiability of the slices, and the `DthAux` helper lemmas
(`contDiffOn_uncurry_pz_sm`, `contDiffOn_uncurry_pth_sm`, `pth_L_of_smooth`, `pth_Dth_eq`,
`hasDerivAt_sin_two`) are already stated for an *arbitrary* open set.  So the port only has to
swap `QuadL = Ioi (-1) ×ˢ Ioo 0 (π/2)` for `Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)` and the class
`SmoothQuad` for `SmoothOpen`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.LhatCalc

set_option autoImplicit false
set_option maxHeartbeats 800000

open DthAux

/-- **`D_θ` commutes exactly with `𝓛̂ = 𝓛 − Transport` on the open class**:
`D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` for every `C^∞` datum on the open quadrant and every interior point
`z > 0`, `0 < θ < π/2`. -/
theorem Dth_Lhat_open {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.EllipticEst.Q0 := hf
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
    hcd.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pz_sm Work.FTS.EllipticEst.isOpen_Q0 hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
        smoothOrder_ne_zero)
  have hpth_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pth_sm Work.FTS.EllipticEst.isOpen_Q0 hcd
  have hpthθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth_sm.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
        smoothOrder_ne_zero)
  have dL : DifferentiableAt ℝ (fun θ' => Work.Coercivity.L f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.L f z θ')
        = (fun θ' => f z θ' + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') from by
      funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring]
    exact (hfθ.add (hpzθ.const_mul z)).sub (hfθ.const_mul (2 / (1 + z)))
  have hDθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ := by
    rw [show (fun θ' => Work.Spaces.Dth f z θ')
        = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') from by
      funext θ'; simp only [Work.Spaces.Dth]]
    exact ((hasDerivAt_sin_two θ).differentiableAt).mul hpthθ
  have dTr : DifferentiableAt ℝ (fun θ' => Work.Coercivity.Transport f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.Transport f z θ')
        = (fun θ' => (3 / (1 + z)) * Work.Spaces.Dth f z θ') from by
      funext θ'; simp only [Work.Coercivity.Transport]; ring]
    exact hDθ.const_mul (3 / (1 + z))
  have hpth : Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pth (Work.Coercivity.L f) z θ
        - Work.Spaces.pth (Work.Coercivity.Transport f) z θ := by
    show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ = _
    rw [show (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
        = ((fun θ' => Work.Coercivity.L f z θ')
            - fun θ' => Work.Coercivity.Transport f z θ') from by
      funext θ'; simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply]]
    rw [deriv_sub dL dTr]
    rfl
  rw [show Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ from rfl]
  rw [hpth]
  rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dth f) z θ]
  rw [pth_L_of_smooth Work.FTS.EllipticEst.isOpen_Q0 hcd hmem,
    Work.Coercivity.pth_Transport]
  rw [show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth f) z θ from rfl]
  rw [Work.Coercivity.pz_Dth_val]
  rw [show Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth f) z θ from rfl]
  rw [show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  rw [pth_Dth_eq (g := f) hpthθ]
  ring

end Work.FTS.CoercivityFix.LhatCalc
