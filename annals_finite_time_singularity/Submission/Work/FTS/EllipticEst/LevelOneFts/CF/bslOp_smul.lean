import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ScaleAPI

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LevelOneFts.CF

set_option autoImplicit false

/-!
# Homogeneity of the elliptic operator `bslOp` under multiplication by a constant

`bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` with
`L₀Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` is a linear differential operator, so
`bslOp α (c • Ψ) = c • bslOp α Ψ` pointwise.  No differentiability hypothesis is needed here
(unlike additivity): Mathlib's `deriv` is totalised, but it still commutes with multiplication
by a constant *unconditionally* (`deriv_const_mul_field`), because at a non-differentiable point
both sides vanish.

The homogeneity of the individual first-order operators `pz`, `pth` and of their iterates is
already available as `Work.FTS.EllipticEst.{pz,pth,pzIter,pthIter}_smul`; here we only need to
transport those to the pointwise form and handle the composite operator `Lzero` (whose
`tan θ · ·` slot forces one function-level reassociation), and then `bslOp` is immediate.
-/

/-! ## Pointwise form of the homogeneity of the derivatives -/

theorem pz_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (c • f) z θ = c * Work.Spaces.pz f z θ := by
  have h := congrFun (congrFun (Work.FTS.EllipticEst.pz_smul c f) z) θ
  simpa only [Pi.smul_apply, smul_eq_mul] using h

theorem pth_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (c • f) z θ = c * Work.Spaces.pth f z θ := by
  have h := congrFun (congrFun (Work.FTS.EllipticEst.pth_smul c f) z) θ
  simpa only [Pi.smul_apply, smul_eq_mul] using h

theorem pzIter_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter n (c • f) z θ = c * Work.Spaces.pzIter n f z θ := by
  have h := congrFun (congrFun (Work.FTS.EllipticEst.pzIter_smul c f n) z) θ
  simpa only [Pi.smul_apply, smul_eq_mul] using h

theorem pthIter_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pthIter n (c • f) z θ = c * Work.Spaces.pthIter n f z θ := by
  have h := congrFun (congrFun (Work.FTS.EllipticEst.pthIter_smul c f n) z) θ
  simpa only [Pi.smul_apply, smul_eq_mul] using h

/-! ## Homogeneity of `L₀` -/

/-- The `tan θ · ·` slot of `L₀` commutes with constants, after the (pointwise) reassociation
`tan θ · (c · f) = c · (tan θ · f)`. -/
theorem pth_tan_mul_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * (c • f) z' θ') z θ
      = c * Work.Spaces.pth (fun z' θ' => Real.tan θ' * f z' θ') z θ := by
  have hfun : (fun z' θ' : ℝ => Real.tan θ' * (c • f) z' θ')
      = c • (fun z' θ' : ℝ => Real.tan θ' * f z' θ') := by
    funext z' θ'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, Work.FTS.EllipticEst.pth_smul]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem Lzero_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (c • f) z θ = c * Work.Elliptic.Lzero f z θ := by
  have h2 := pthIter_smul_apply c f 2 z θ
  have ht := pth_tan_mul_smul_apply c f z θ
  rw [Work.Elliptic.Lzero, Work.Elliptic.Lzero]
  rw [h2, ht]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Homogeneity of `bslOp` -/

theorem bslOp_smul (α c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α (c • f) z θ = c * Work.Elliptic.bslOp α f z θ := by
  have h2 := pzIter_smul_apply c f 2 z θ
  have h1 := pz_smul_apply c f z θ
  have hL := Lzero_smul_apply c f z θ
  simp only [Work.Elliptic.bslOp_apply, h2, h1, hL]
  ring

end Work.FTS.EllipticEst.LevelOneFts.CF
