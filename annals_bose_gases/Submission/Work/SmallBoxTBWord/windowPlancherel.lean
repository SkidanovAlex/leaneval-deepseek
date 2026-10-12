import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The windowed Plancherel identity for the kinetic symbol `‖·‖²`

`Work.SmallBoxTBWord.windowPlancherel`: for a smooth compactly supported window
`W` (with `tsupport W ⊆ acube a`) and an arbitrary smooth `ψ`,

    (2π)⁻³ ∫_p ‖p‖²‖𝓕(Wψ)(p/(2π))‖²
      = ∫_{acube a} Σ_k (∂_k (Wψ))² .

The compact support of the product `Wψ` is what makes the identity true: it is
supplied by `HasCompactSupport.mul_right` from the compact support of `W`, so no
support hypothesis on `ψ` is needed, and the integral over `acube a` may be
replaced by the integral over all of `ℝ³` because `Wψ` (hence all its derivatives)
vanishes off `tsupport W ⊆ acube a`.

The analytic content is the Bridge's (c1) identity
`Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet` (the Plancherel /
`L²`-kernel computation) applied with the trivial window `1`: the windowed mode
form of the product `Wψ` is exactly `(2π)⁻³∫_p ‖p‖²‖kinFT (Wψ) p‖²`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.SmallBoxTBWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem windowPlancherel {a : ℝ} {W ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (ha : 0 < a)
    (hW : ContDiff ℝ (⊤ : ENat) W) (hWcs : HasCompactSupport W)
    (htsupp : tsupport W ⊆ Submission.BoseGases.acube a) (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z => (W z : ℂ) * (ψ z : ℂ)) p‖ ^ 2
      = ∫ z in Submission.BoseGases.acube a, ∑ k : Fin 3,
          (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * ψ w) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  -- The product `Wψ` is smooth with compact support (this is the only place the
  -- support of `W` is used, so `ψ` itself needs no support hypothesis).
  have hv_cont : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => W y * ψ y) := hW.mul hψ
  have hv_cs : HasCompactSupport (fun y : ℝ³ => W y * ψ y) := hWcs.mul_right
  -- The Bridge's windowed Plancherel identity with the trivial window `1`.
  have hkey := Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet
    (fun _ : ℝ³ => (1 : ℝ)) (fun y => W y * ψ y) contDiff_const hv_cont hv_cs
  -- The left-hand side is the windowed mode form of `Wψ` with symbol `‖·‖²`.
  have hL : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z => (W z : ℂ) * (ψ z : ℂ)) p‖ ^ 2
      = Submission.BoseGases.winModeForm (fun _ : ℝ³ => (1 : ℝ)) (fun r => r ^ 2)
          (fun y => W y * ψ y) := by
    have hfun : (fun y : ℝ³ => (((1 : ℝ) : ℂ) * ((W y * ψ y : ℝ) : ℂ)))
        = (fun z : ℝ³ => (W z : ℂ) * (ψ z : ℂ)) := by
      funext y; push_cast; ring
    unfold Submission.BoseGases.winModeForm
    rw [hfun]
  -- The trivial window disappears from the position-space side.
  have hfd_eq : (fun y : ℝ³ => 1 * (W y * ψ y)) = (fun w : ℝ³ => W w * ψ w) := by
    funext y; rw [one_mul]
  -- `Wψ` vanishes in a neighbourhood of every point outside `acube a`, so all
  -- its partial derivatives vanish there and the integrand is zero off the cube.
  have hzero : ∀ z : ℝ³, z ∉ Submission.BoseGases.acube a →
      (∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => W w * ψ w) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 := by
    intro z hz
    have hzW : z ∉ tsupport W := fun h => hz (htsupp h)
    have hsub : tsupport (fun w : ℝ³ => W w * ψ w) ⊆ tsupport W := by
      apply closure_mono
      intro w hw
      simp only [Function.mem_support, ne_eq] at hw ⊢
      exact fun hW0 => hw (by simp [hW0])
    have hzv : z ∉ tsupport (fun w : ℝ³ => W w * ψ w) := fun h => hzW (hsub h)
    have hfd : fderiv ℝ (fun w : ℝ³ => W w * ψ w) z = 0 :=
      (HasFDerivAt.of_notMem_tsupport ℝ hzv).fderiv
    simp [hfd]
  -- Assemble: replace the cube integral by the full-space integral (the
  -- integrand vanishes off the cube), then apply the (c1) identity.
  rw [hL, hkey, hfd_eq, MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Submission.BoseGases.acube a) hzero]

end Work.SmallBoxTBWord
