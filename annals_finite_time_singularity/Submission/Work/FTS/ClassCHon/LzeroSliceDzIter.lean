/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassCHon/LzeroSliceDzIter` — the `Lzero1`-slice identity for the `D_z`-iterates

The Green-formula route to the node's angular slot (`ClassCHon.PlainFam`'s family **(P)**,
`b = 2`) needs, for every `a`, the one-dimensional `θ`-ODE satisfied by the slice
`θ ↦ D_z^a Ψ(z,θ)`:

    `Lzero1 (D_z^a Ψ(z,·)) = D_z^a F(z,·) + α² · D_z^{a+2}Ψ(z,·) + 5α · D_z^{a+1}Ψ(z,·)`

on `(0,π/2)`.  This is `TT.Lzero_eq_of_bsl` (the `a = 0` case) applied to the *shifted* datum
`(D_z^a F, D_z^a Ψ)`, whose `bslOp`-equation is `TT.bslOp_DzIter_eq`.

The statement is the exact `heq` input of `ClassCHon.angGreenFormula` (and hence of the
`hgreen` input of `ClassCHon.hkMem_zero_pthIter_two_of_green`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.ang_a_weak
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon

set_option autoImplicit false

/-- `D_z^{j+i} = D_z^j ∘ D_z^i`. -/
theorem DzIter_add (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (j + i) f = Work.Spaces.DzIter j (Work.Spaces.DzIter i f) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.succ_add, Work.Spaces.DzIter_succ, ih]
      rfl

/-- **The `θ`-ODE of the `D_z`-iterate.**  If `Ψ` is smooth on the open quadrant and
`bslOp α Ψ = F` there, then for every `a` the slice `θ ↦ D_z^a Ψ(z,θ)` solves

`Lzero1 (D_z^a Ψ(z,·)) = D_z^a F(z,·) + α² D_z^{a+2}Ψ(z,·) + 5α D_z^{a+1}Ψ(z,·)`

on `(0,π/2)`. -/
theorem lzero1_slice_DzIter {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) (a : ℕ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter a Ψ z t) θ
        = Work.Spaces.DzIter a F z θ + α ^ 2 * Work.Spaces.DzIter (a + 2) Ψ z θ
          + 5 * α * Work.Spaces.DzIter (a + 1) Ψ z θ := by
  intro z hz θ hθ0 hθ1
  have hsmForall : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry Ψ)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hsm
  -- the equation for the shifted datum
  have hShift : ∀ z', 0 < z' → ∀ θ', 0 < θ' → θ' < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.Spaces.DzIter a Ψ) z' θ'
        = Work.Spaces.DzIter a F z' θ' :=
    Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ a hsmForall hEq
  have hmain := Work.FTS.EllipticEst.TT.Lzero_eq_of_bsl (α := α) (F := Work.Spaces.DzIter a F)
    (Ψ := Work.Spaces.DzIter a Ψ) (hsm.DzIter a) hShift z hz θ hθ0 hθ1
  -- identify the two `D_z`-iterates of the shifted datum
  have h2 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter a Ψ)
      = Work.Spaces.DzIter (a + 2) Ψ := by
    rw [show Work.Spaces.DzIter 2 (Work.Spaces.DzIter a Ψ)
        = Work.Spaces.DzIter (2 + a) Ψ from (DzIter_add 2 a Ψ).symm]
    rw [show 2 + a = a + 2 from by omega]
  rw [h2] at hmain
  rw [← Work.Spaces.DzIter_succ a Ψ] at hmain
  exact hmain

end Work.FTS.ClassCHon
