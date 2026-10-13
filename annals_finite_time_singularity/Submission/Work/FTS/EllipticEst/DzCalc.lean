/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z`-calculus of the elliptic operator (neutral home)

`D_z = z ∂_z` is the radial derivative that the elliptic operator (PolarBSL) commutes with:
its radial part is `-α²z²∂_zz - α(5+α)z∂_z = -α²D_z² - 5αD_z` once the identity
`z²∂_zz = D_z² - D_z` is used.  The two declarations below are the algebraic content of
"estimates on the radial derivatives are relatively simple to get" (Elgindi, Annals 194 (3)
2021, tex 988).

## Why this module exists separately

`Work.FTS.EllipticEst.TT.est_two_weak` needs `zsq_pzIter2_eq`; importing
`Submission.Work.FTS.EllipticEst.propHk_fts` for it created a *mutual* import cycle, because
that module imports the `Cores/Pieces` statements which are proved through the `TT` stretch.
The calculus therefore lives here, with the **same names in the same namespace**
(`Work.FTS.EllipticEst.zsq_pzIter2_eq`, `Work.FTS.EllipticEst.bslOp_eq_Dz`), so that

* `TT/est_two_weak.lean` imports *this* module (no cycle), and
* every module that imports `propHk_fts.lean` still sees the names, since that file imports
  this one.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- `z² ∂_zz Ψ = D_z²Ψ - D_z Ψ` pointwise (the two slice derivatives involved being the
`z → Ψ z θ` and `z → ∂_zΨ z θ` ones). -/
theorem zsq_pzIter2_eq (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.Dz Ψ z θ := by
  have hd : deriv (fun z' => z' * Work.Spaces.pz Ψ z' θ) z
      = Work.Spaces.pz Ψ z θ + z * deriv (fun z' => Work.Spaces.pz Ψ z' θ) z := by
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ)
        = (fun z' : ℝ => z') * (fun z' => Work.Spaces.pz Ψ z' θ) := by
      funext x; rfl
    rw [hfun]
    have h := deriv_mul (c := fun z' : ℝ => z')
      (d := fun z' => Work.Spaces.pz Ψ z' θ) (x := z) differentiableAt_id h2
    simpa using h
  have hA : Work.Spaces.DzIter 2 Ψ z θ
      = z * deriv (fun z' => z' * Work.Spaces.pz Ψ z' θ) z := by
    have h : Work.Spaces.pz (Work.Spaces.Dz Ψ) z θ
        = deriv (fun z' => z' * Work.Spaces.pz Ψ z' θ) z := rfl
    have h' : Work.Spaces.DzIter 2 Ψ z θ = z * Work.Spaces.pz (Work.Spaces.Dz Ψ) z θ := rfl
    rw [h', h]
  have hB : Work.Spaces.pzIter 2 Ψ z θ = deriv (fun z' => Work.Spaces.pz Ψ z' θ) z := rfl
  have hC : Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ := rfl
  rw [hA, hB, hC, hd]
  ring

/-- The elliptic operator in the `D_z` form:
`bslOp α Ψ = -α² D_z²Ψ - 5α D_zΨ + Lzero Ψ`. -/
theorem bslOp_eq_Dz (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z) :
    Work.Elliptic.bslOp α Ψ z θ
      = -α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ - 5 * α * Work.Spaces.Dz Ψ z θ
        + Work.Elliptic.Lzero Ψ z θ := by
  have hDz : (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
      = (α * (5 + α)) * Work.Spaces.Dz Ψ z θ := by
    simp only [Work.Spaces.Dz]; ring
  have hz2 : -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
      = -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by ring
  rw [Work.Elliptic.bslOp_apply, hz2, hDz, zsq_pzIter2_eq Ψ h1 h2]
  ring

end Work.FTS.EllipticEst
