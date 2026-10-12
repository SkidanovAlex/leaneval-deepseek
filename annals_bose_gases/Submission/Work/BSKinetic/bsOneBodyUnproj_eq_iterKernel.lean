import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.IterKernelAux.bsWin_mul_integrable
import Submission.Work.BSKinetic.IterKernelAux.winModeForm_congr_mul
import Submission.Work.SmallBoxBridge.Resolve.winModeForm_eq_kernelForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unprojected one-body big-box form as an iterated kernel form

`bsOneBodyUnproj ℓ F u ψ = (2π)⁻³ ∫_p F‖p‖ · ‖kinFT (χ_u·ψ) p‖²` is the quadratic form of the
windowed one-body operator `χ_u F(√−Δ) χ_u` on the moving box `Λ(u) = ℓu + acube ℓ`, with window
`χ_u = bsWin ℓ u = χ_ℓ(· − ℓu)`.  This file identifies it with the position-space **iterated
kernel form** of the convolution operator with kernel `K_F = 𝓕⁻¹F = kinKernel F`,

    `bsOneBodyUnproj ℓ F u ψ = ∫_x (χ_uψ)(x) · ∫_y K_F(x−y)·(χ_uψ)(y) dy`,

i.e. the (c1)-half of the kinetic bridge at the big-box family, pointwise in `u`.

The kernel identity for a general window is
`Work.SmallBoxBridge.Resolve.winModeForm_eq_kernelForm`, which however carries the side condition
`|χ| ≤ 1`.  That side condition is **not** satisfied by `χ_u`: the corpus bump is L²-normalised,
`chiSup = (∫χ²)^{-1/2} > 1`, and `χ_u` attains values of modulus `chiSup`.  The condition is an
artefact of that statement, because `winModeForm χ F u` depends on `(χ, u)` only through the
*product* `χ·u` (`IterKernelAux.winModeForm_congr_mul`).  Hence the proof below applies the kernel
identity to the **constant** window `χ ≡ 1` and the state `χ_u·ψ` — legitimate, since `|1| ≤ 1`
and `χ_u·ψ` is integrable (`IterKernelAux.bsWin_mul_integrable`, the window being a smooth bump
and `ψ` smooth) — and transports the conclusion back along the product identity
`1·(χ_uψ) = χ_u·ψ`.
-/

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

set_option autoImplicit false

theorem bsOneBodyUnproj_eq_iterKernel {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          (Work.BSKinetic.bsWin ℓ u x * ψ x) *
            (∫ y : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.kinKernel F (x - y) *
                (Work.BSKinetic.bsWin ℓ u y * ψ y)) := by
  -- the windowed state `χ_u·ψ` is integrable: `χ_u` is a smooth bump, `ψ` is continuous
  have hgi : Integrable (fun x : ℝ³ => (1 : ℝ) * (bsWin ℓ u x * ψ x)) := by
    simpa only [one_mul] using IterKernelAux.bsWin_mul_integrable hℓ u hψ hcs
  -- the (c1) kernel identity at the *constant* window `χ ≡ 1` and the state `χ_u·ψ`
  have hkey := Work.SmallBoxBridge.Resolve.winModeForm_eq_kernelForm (fun _ : ℝ³ => (1 : ℝ))
    (fun x : ℝ³ => bsWin ℓ u x * ψ x) F hFi hgi measurable_const (fun _ => by simp)
  -- `winModeForm` depends only on the product `χ·u`
  have hprod := IterKernelAux.winModeForm_congr_mul (F := F) (χ₁ := bsWin ℓ u) (u₁ := ψ)
    (χ₂ := fun _ : ℝ³ => (1 : ℝ)) (u₂ := fun x : ℝ³ => bsWin ℓ u x * ψ x)
    (fun x => by ring)
  -- `bsOneBodyUnproj ℓ F u ψ` *is* `winModeForm (bsWin ℓ u) F ψ`, definitionally
  have hdef : bsOneBodyUnproj ℓ F u ψ
      = Submission.BoseGases.winModeForm (bsWin ℓ u) F ψ := rfl
  rw [hdef, hprod, hkey]
  simp only [one_mul]

end Work.BSKinetic
