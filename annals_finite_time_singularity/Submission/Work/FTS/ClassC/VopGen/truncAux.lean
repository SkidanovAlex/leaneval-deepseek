import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.VopGen.truncSlots
import Submission.Work.FTS.ClassC.aslotAux.bslOpPth.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.truncAux`

Two small helpers for the truncation half `VopGen.TruncStmt`:

* `ae_mem_Q0_prod` — a.e. points of `Iz ×ˢ Iθ` lie in the open quadrant;
* `deriv_chi_sq_mul`, `deriv_chi_sq_mul_sgm` — the product rule `D_z(χ²X) = 2(zχχ')X + χ²D_zX`
  on a slice, with and without the angular weight attached.
-/
noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ)

/-- A.e. points of `Iz ×ˢ Iθ` lie in the open quadrant. -/
theorem ae_mem_Q0_prod : ∀ᵐ p ∂(volume.restrict (Iz ×ˢ Iθ)), p ∈ Work.FTS.EllipticEst.Q0 := by
  have h1 : ∀ᵐ p ∂(volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))),
      p ∈ Work.FTS.EllipticEst.Q0 :=
    MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioo)
      (fun p hp => hp)
  have hcomp : (volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) : Measure (ℝ × ℝ))
      = volume.restrict (Iz ×ˢ Iθ) :=
    Work.FTS.ClassC.aslotAux.BslOpPth.restrict_prod_eq_restrict_Q0.symm.trans
      Work.FTS.ClassC.aslotAux.BslOpPth.restrict_rect_eq.symm
  rwa [hcomp] at h1

/-- The product rule for `χ²·X` on a slice of the open quadrant. -/
theorem deriv_chi_sq_mul {χ : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X) (hχd : Differentiable ℝ χ)
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z) :
    z * deriv (fun z' => (χ z') ^ 2 * X z' θ) z
      = (2 * (z * χ z * deriv χ z)) * X z θ + (χ z) ^ 2 * (z * Work.Spaces.pz X z θ) := by
  have h1 : HasDerivAt (fun z' => (χ z') ^ 2) (2 * (χ z) ^ (2 - 1) * deriv χ z) z :=
    (hχd.differentiableAt.hasDerivAt).pow 2
  have h2 : HasDerivAt (fun z' => X z' θ) (Work.Spaces.pz X z θ) z :=
    hX.hasDerivAt_slice hθ hz
  have h3 : deriv (fun z' => χ z' ^ 2 * X z' θ) z
      = 2 * χ z ^ (2 - 1) * deriv χ z * X z θ + χ z ^ 2 * Work.Spaces.pz X z θ := by
    rw [show (fun z' => χ z' ^ 2 * X z' θ)
      = (fun z' => χ z' ^ 2) * (fun z' => X z' θ) from rfl]
    exact (h1.mul h2).deriv
  rw [h3]
  norm_num
  ring

/-- The same product rule with the angular weight attached. -/
theorem deriv_chi_sq_mul_sgm {α : ℝ} {χ : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X) (hχd : Differentiable ℝ χ)
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z) :
    z * deriv (fun z' => (χ z') ^ 2 * X z' θ * sgm α θ) z
      = sgm α θ * ((2 * (z * χ z * deriv χ z)) * X z θ + (χ z) ^ 2
          * (z * Work.Spaces.pz X z θ)) := by
  have h1 : (fun z' => (χ z') ^ 2 * X z' θ * sgm α θ)
      = (fun z' => sgm α θ * ((χ z') ^ 2 * X z' θ)) := by
    funext y; ring
  rw [h1, deriv_const_mul_field (u := sgm α θ)]
  rw [show z * (sgm α θ * deriv (fun z' => χ z' ^ 2 * X z' θ) z)
      = sgm α θ * (z * deriv (fun z' => χ z' ^ 2 * X z' θ) z) from by ring,
    deriv_chi_sq_mul hX hχd hθ hz]

end Work.FTS.ClassC.VopGen
