import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.OddExt

/-!
# Homogeneity of the elliptic operator `bslOp` under multiplication by a constant

`Work.Elliptic.bslOp p Ψ = -p²z²∂_zzΨ - p(5+p)z∂_zΨ + L₀Ψ` with
`L₀Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` is a linear differential operator, whence
`bslOp p (c · Ψ) = c · bslOp p Ψ` pointwise.  No differentiability hypothesis is needed:
Mathlib's `deriv` is totalised, but it still commutes with multiplication by a constant
*unconditionally* (`deriv_const_mul_field`), because at a non-differentiable point both sides
vanish.

The only work is to transfer that homogeneity to the iterated operators `pzIter 2`, `pz`,
`pthIter 2` and to the `tan θ · ·` slot of `L₀` (which needs the pointwise reassociation
`tan θ · (c · Ψ) = c · (tan θ · Ψ)`).
-/

/-! ## Homogeneity of the individual derivatives (pointwise) -/

private lemma pz_cm_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) z θ = c * Work.Spaces.pz f z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field c

private lemma pth_cm_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) z θ = c * Work.Spaces.pth f z θ := by
  rw [Work.Spaces.pth, Work.Spaces.pth]
  exact deriv_const_mul_field c

private lemma pzIter_cm_apply (c : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter n (fun z θ => c * f z θ) z θ = c * Work.Spaces.pzIter n f z θ := by
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ]
      have heq : Work.Spaces.pzIter k (fun z θ => c * f z θ)
          = fun z θ => c * Work.Spaces.pzIter k f z θ := funext fun z => funext fun θ => ih z θ
      rw [heq, pz_cm_apply, Work.Spaces.pzIter_succ]

private lemma pthIter_cm_apply (c : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter n (fun z θ => c * f z θ) z θ = c * Work.Spaces.pthIter n f z θ := by
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ]
      have heq : Work.Spaces.pthIter k (fun z θ => c * f z θ)
          = fun z θ => c * Work.Spaces.pthIter k f z θ := funext fun z => funext fun θ => ih z θ
      rw [heq, pth_cm_apply, Work.Spaces.pthIter_succ]

/-- The `tan θ · ·` slot of `L₀` commutes with a constant, after the reassociation
`tan θ · (c · Ψ) = c · (tan θ · Ψ)` of the differentiated function. -/
private lemma pth_tan_cm_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * (c * f z' θ')) z θ
      = c * Work.Spaces.pth (fun z' θ' => Real.tan θ' * f z' θ') z θ := by
  rw [Work.Spaces.pth, Work.Spaces.pth]
  rw [show (fun θ' => Real.tan θ' * (c * f z θ')) = (fun θ' => c * (Real.tan θ' * f z θ'))
      from funext fun θ' => by ring]
  exact deriv_const_mul_field c

/-! ## Homogeneity of `bslOp` -/

theorem bslOp_const_mul (p c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp p (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Elliptic.bslOp p Ψ z θ := by
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
  rw [pzIter_cm_apply c 2 Ψ z θ, pz_cm_apply c Ψ z θ, pth_tan_cm_apply c Ψ z θ,
    pthIter_cm_apply c 2 Ψ z θ]
  ring

end Work.FTS.BSIdent.OddExt
