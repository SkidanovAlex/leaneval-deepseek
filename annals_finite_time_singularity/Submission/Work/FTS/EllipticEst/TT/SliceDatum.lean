/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.SliceDatum`: elementary facts about the radially differentiated slices `D_z^jΨ`

The proof of the `ℋ^k` elliptic estimate applies the estimates to the *slices* `D_z^jΨ`
(`j ≤ k`) of the solution, for which the same equation holds with source `D_z^jF`
(`TT.bslOp_DzIter_eq`) and the same Dirichlet data.  This module records the parts that need no
analysis:

* `DzIter_zero_at_zero`, `DzIter_zero_at_pi_half`: the Dirichlet data `Ψ z 0 = Ψ z (π/2) = 0` is
  preserved, because it is a statement about the one-variable function `z ↦ Ψ z θ` being
  identically zero;
* `EllWeakPos.smoothOpen`: the smoothness hypothesis of `EllWeakPos` is `SmoothOpen`, the shape
  in which the open-quadrant calculus of `Work.FTS.EllipticEst.OpenQDefs` is stated;
* `EllWeakPos.smoothOpen_DzIter`: the slices are again smooth there.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The Dirichlet data is preserved by `D_z^j` -/

/-- If `Ψ z 0 = 0` for every `z`, then `(D_z^jΨ) z 0 = 0` for every `z`: the slice
`z ↦ Ψ z 0` is the zero function, so each of its `z`-derivatives vanishes. -/
theorem DzIter_zero_at_zero (Ψ : ℝ → ℝ → ℝ) (j : ℕ) (h : ∀ z, Ψ z 0 = 0) :
    ∀ z, Work.Spaces.DzIter j Ψ z 0 = 0 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro z
    have hfun : (fun z' => Work.Spaces.DzIter j Ψ z' 0) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [hfun, deriv_const]
    ring

/-- If `Ψ z (π/2) = 0` for every `z`, then `(D_z^jΨ) z (π/2) = 0` for every `z`. -/
theorem DzIter_zero_at_pi_half (Ψ : ℝ → ℝ → ℝ) (j : ℕ) (h : ∀ z, Ψ z (Real.pi / 2) = 0) :
    ∀ z, Work.Spaces.DzIter j Ψ z (Real.pi / 2) = 0 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro z
    have hfun : (fun z' => Work.Spaces.DzIter j Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [hfun, deriv_const]
    ring

/-! ## Smoothness of the data and of the slices, in the `open-quadrant` shape -/

/-- The smoothness field of `EllWeakPos` is the `SmoothOpen` of `OpenQDefs`. -/
theorem EllWeakPos.smoothOpen {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr (h.smooth)

/-- The slices of a datum of the weak class are again smooth on the open quadrant. -/
theorem EllWeakPos.smoothOpen_DzIter {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPos α k F Ψ) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ) :=
  (h.smoothOpen).DzIter j

end Work.FTS.EllipticEst.TT
