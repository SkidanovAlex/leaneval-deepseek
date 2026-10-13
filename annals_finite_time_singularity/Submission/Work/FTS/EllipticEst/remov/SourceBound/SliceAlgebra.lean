import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Algebraic identities for the weak-class slices

* `Lzero1` applied to the `z`-slice of `Ψ` is the slice of `Lzero` (definitional).
* `D_z²Ψ = z²∂_z²Ψ + z∂_zΨ` on the open quadrant.
* On the open quadrant, the equation `bslOp α Ψ = F` rewrites as
  `Lzero1 (Ψ z ·) = F z · + α² D_z²Ψ + 5α D_zΨ` for the *slices*.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- `Lzero1` applied to the `z`-slice of `Ψ` is the slice of `Work.Elliptic.Lzero`. -/
theorem Lzero1_slice_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Work.Elliptic.Lzero Ψ z θ := rfl

/-- **`D_z²Ψ` splits as `z²∂_z²Ψ + z∂_zΨ`.** -/
theorem srcB_DzIter_two_eq (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ z θ
      = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pz Ψ z θ := by
  have hd : HasDerivAt (fun z' : ℝ => Work.Spaces.pz Ψ z' θ)
      (Work.Spaces.pzIter 2 Ψ z θ) z := by
    have h := (hΨ.pz).hasDerivAt_slice hθ hz
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
  have hprod := (hasDerivAt_id z).mul hd
  show z * deriv (id * fun z' : ℝ => Work.Spaces.pz Ψ z' θ) z
    = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pz Ψ z θ
  rw [hprod.deriv]
  simp only [one_mul, id_eq]
  ring

/-- **The slice equation in the `D_z`-form.** -/
theorem Lzero1_slice_eq_source {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
      = F z θ + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ + 5 * α * Work.Spaces.DzIter 1 Ψ z θ := by
  have hbsl := heq z θ hz hθ.1 hθ.2
  simp only [Work.Elliptic.bslOp] at hbsl
  have hL : Work.Elliptic.Lzero Ψ z θ
      = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
    linarith [hbsl]
  rw [Lzero1_slice_eq, hL, srcB_DzIter_two_eq Ψ hΨ hz hθ]
  show F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
    = F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pz Ψ z θ)
      + 5 * α * (z * Work.Spaces.pz Ψ z θ)
  ring

end Work.FTS.EllipticEst.remov
