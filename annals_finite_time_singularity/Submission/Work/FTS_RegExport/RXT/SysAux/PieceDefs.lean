import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.PieceDefs` — one-variable forms of `D_z` and `D_θ`

The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` of `Work.Spaces` act on functions of two
variables.  Every function occurring in `explicit_piece_bounds` is a finite sum of products
`A(z)·B(θ)` of a function of `z` alone with a function of `θ` alone, and on such a product the
two operators act separately:

  `D_z^j D_θ^i (A·B) (z,θ) = (ZIter j A z)·(TIter i B θ)`,

where `ZIter j A = (z d/dz)^j A` and `TIter i B = (sin(2θ) d/dθ)^i B` are the one-variable
versions.  This file sets up `ZIter`, `TIter` and proves that splitting
(`DzIter_sep`, `DthIter_sep`, `mixed_sep`); the bounds on the individual one-variable factors
are the lemmas `ZIter_*` (in `piece_z_bounds`) and `TIter_*` (in `piece_t_bounds`).

Note that `deriv_const_mul_field` and `deriv_mul_const_field` are *unconditional* in Lean
(`deriv` is totalised), so the splitting needs no differentiability hypotheses at all.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-- `(z ∂_z)^j A`, the one-variable version of the radial operator `D_z`. -/
def ZIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, A => A
  | j + 1, A => fun z => z * deriv (ZIter j A) z

/-- `(sin(2θ) ∂_θ)^i B`, the one-variable version of the angular operator `D_θ`. -/
def TIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, B => B
  | i + 1, B => fun θ => Real.sin (2 * θ) * deriv (TIter i B) θ

@[simp] theorem ZIter_zero (A : ℝ → ℝ) : ZIter 0 A = A := rfl

@[simp] theorem ZIter_succ (j : ℕ) (A : ℝ → ℝ) :
    ZIter (j + 1) A = fun z => z * deriv (ZIter j A) z := rfl

@[simp] theorem TIter_zero (B : ℝ → ℝ) : TIter 0 B = B := rfl

@[simp] theorem TIter_succ (i : ℕ) (B : ℝ → ℝ) :
    TIter (i + 1) B = fun θ => Real.sin (2 * θ) * deriv (TIter i B) θ := rfl

theorem ZIter_succ_apply (j : ℕ) (A : ℝ → ℝ) (z : ℝ) :
    ZIter (j + 1) A z = z * deriv (ZIter j A) z := rfl

theorem TIter_succ_apply (i : ℕ) (B : ℝ → ℝ) (θ : ℝ) :
    TIter (i + 1) B θ = Real.sin (2 * θ) * deriv (TIter i B) θ := rfl

/-- Constants pass through `ZIter`. -/
theorem ZIter_const_mul (c : ℝ) (A : ℝ → ℝ) (j : ℕ) :
    ZIter j (fun z => c * A z) = fun z => c * ZIter j A z := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [ZIter_succ, ih, ZIter_succ]
      funext z
      rw [deriv_const_mul_field]
      ring

/-- `D_z^j` of a product `A(z)·C(θ)` only sees the radial factor. -/
theorem DzIter_sep (j : ℕ) (A C : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A z * C θ) = fun z θ => ZIter j A z * C θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp only [ZIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_mul_const_field]
      ring

/-- `D_θ^i` of a product `A(z)·B(θ)` only sees the angular factor. -/
theorem DthIter_sep (i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => A z * B θ) = fun z θ => A z * TIter i B θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [TIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- **The mixed jets of a separable datum split.**  For `A·B : (z,θ) ↦ A z * B θ`,

  `D_z^j D_θ^i (A·B) z θ = (ZIter j A z) · (TIter i B θ)`.

This is the identity in which every pointwise estimate of `explicit_piece_bounds` is applied. -/
theorem mixed_sep (j i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => A z * B θ) = fun z θ => ZIter j A z * TIter i B θ := by
  rw [Work.Spaces.mixed, DthIter_sep i A B, DzIter_sep j A (TIter i B)]

end Work.FTS_RegExport.RXT.SysAux
