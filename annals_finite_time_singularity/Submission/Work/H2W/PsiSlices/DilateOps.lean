/-
Copyright: work module for the Elgindi finite-time singularity project.

# Dilation of the self-similar variable, and the operators of the elliptic section

The radial variable of the elliptic chapter is `z`, and the paper's estimates are invariant under
the dilation `z ↦ lam z` (`lam > 0`).  This file collects the *operator* commutation identities
that make that invariance formal.

The key point is that everything is *unconditional*: `deriv` is totalised (it is `0` where the
function is not differentiable), and nevertheless the chain rule

  `deriv (fun z => f (lam * z)) z = lam * deriv f (lam * z)`    (`deriv_comp_mul_left`)

holds for **every** `f : ℝ → ℝ`, `lam`, `z` — for `lam ≠ 0` because the two sides are either both
given by the chain rule or both junk, and for `lam = 0` because both sides are `0`.  Hence
`pz`, `Dz`, and their iterates commute with a dilation, with no smoothness hypothesis.

The angular operators `pth`, `Dth` do not see `z` at all, so their commutation is definitional.

## Contents

* `Dil` — the dilation `(Dil lam F) z θ = F (lam z) θ`;
* `pz_dilate`, `pz_const_mul_dilate`, `dilate_pzIter`, `Dz_dilate`, `DzIter_dilate`;
* `pth_dilate`, `pthIter_dilate`, `Dth_dilate`, `DthIter_dilate`, `mixed_dilate`;
* `Lzero_dilate`, `bslOp_dilate`, `Fstar_dilate`, `OrthCond_dilate`.
-/
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-- The dilation of a datum of the self-similar variable: `(Dil lam F) z θ = F (lam * z) θ`. -/
def Dil (lam : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => F (lam * z) θ

@[simp] theorem Dil_apply (lam : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Dil lam F z θ = F (lam * z) θ := rfl

/-! ## The radial derivative `∂_z` and the Euler operator `D_z` -/

/-- The plain radial derivative of a dilated datum.  No differentiability hypothesis: both
`deriv`'s are junk simultaneously. -/
theorem pz_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Spaces.pz (fun z θ => F (lam * z) θ)
      = fun z θ => lam * Work.Spaces.pz F (lam * z) θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => F ζ θ) z

/-- The radial derivative of `c` times a dilated datum. -/
theorem pz_const_mul_dilate (F : ℝ → ℝ → ℝ) (c lam : ℝ) :
    Work.Spaces.pz (fun z θ => c * F (lam * z) θ)
      = fun z θ => c * (lam * Work.Spaces.pz F (lam * z) θ) := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field (x := z) (v := fun z' => F (lam * z') θ) c]
  congr 1
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => F ζ θ) z

/-- The iterated radial derivative of a dilated datum picks up `lam ^ n`. -/
theorem dilate_pzIter (F : ℝ → ℝ → ℝ) (lam : ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (fun z θ => F (lam * z) θ)
      = fun z θ => lam ^ n * Work.Spaces.pzIter n F (lam * z) θ := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, ih, pz_const_mul_dilate]
      funext z θ
      rw [Work.Spaces.pzIter_succ, pow_succ]
      ring

/-- The Euler operator `D_z = z ∂_z` is invariant under dilation. -/
theorem Dz_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Spaces.Dz (fun z θ => F (lam * z) θ) = fun z θ => Work.Spaces.Dz F (lam * z) θ := by
  funext z θ
  rw [Work.Spaces.Dz, Work.Spaces.Dz]
  rw [show Work.Spaces.pz (fun z θ => F (lam * z) θ) z θ
        = lam * Work.Spaces.pz F (lam * z) θ
      from congrFun (congrFun (pz_dilate F lam) z) θ]
  ring

/-- The iterated Euler operator `D_z^j` is invariant under dilation. -/
theorem DzIter_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Spaces.DzIter j F (lam * z) θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Dz_dilate, ← Work.Spaces.DzIter_succ]

/-! ## The angular operators `∂_θ`, `D_θ` and the mixed operators -/

/-- The angular derivative does not see the dilation (definitional). -/
theorem pth_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Spaces.pth (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Spaces.pth F (lam * z) θ := rfl

/-- The iterated angular derivative does not see the dilation. -/
theorem pthIter_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) (k : ℕ) :
    Work.Spaces.pthIter k (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Spaces.pthIter k F (lam * z) θ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.pthIter_succ, ih, pth_dilate, ← Work.Spaces.pthIter_succ]

/-- `D_θ = sin(2θ) ∂_θ` does not see the dilation. -/
theorem Dth_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Spaces.Dth (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Spaces.Dth F (lam * z) θ := by
  funext z θ
  rw [Work.Spaces.Dth, Work.Spaces.Dth, pth_dilate]

/-- The iterated angular Euler operator does not see the dilation. -/
theorem DthIter_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) (k : ℕ) :
    Work.Spaces.DthIter k (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Spaces.DthIter k F (lam * z) θ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.DthIter_succ, ih, Dth_dilate, ← Work.Spaces.DthIter_succ]

/-- The mixed operators `D_z^j D_θ^i` are invariant under dilation. -/
theorem mixed_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Spaces.mixed j i F (lam * z) θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_dilate, DzIter_dilate]

/-! ## The elliptic operator and the moment condition -/

/-- The `α = 0` part of the elliptic operator is invariant under dilation (definitional, since
it only involves `pthIter` and `tan θ`). -/
theorem Lzero_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Elliptic.Lzero (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Elliptic.Lzero F (lam * z) θ := by
  funext z θ
  rfl

/-- **The elliptic operator `bslOp α` is invariant under dilation of the radial variable**:
it is an Euler-type operator, so `z ↦ lam z` maps it into itself. -/
theorem bslOp_dilate (α lam : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.bslOp α (fun z θ => Ψ (lam * z) θ)
      = fun z θ => Work.Elliptic.bslOp α Ψ (lam * z) θ := by
  funext z θ
  simp only [Work.Elliptic.bslOp]
  rw [show Work.Spaces.pzIter 2 (fun z θ => Ψ (lam * z) θ) z θ
        = lam ^ 2 * Work.Spaces.pzIter 2 Ψ (lam * z) θ from
      congrFun (congrFun (dilate_pzIter Ψ lam 2) z) θ,
      show Work.Spaces.pz (fun z θ => Ψ (lam * z) θ) z θ
        = lam * Work.Spaces.pz Ψ (lam * z) θ from
      congrFun (congrFun (pz_dilate Ψ lam) z) θ,
      show Work.Elliptic.Lzero (fun z θ => Ψ (lam * z) θ) z θ
        = Work.Elliptic.Lzero Ψ (lam * z) θ from
      congrFun (congrFun (Lzero_dilate Ψ lam) z) θ]
  ring

/-- The angular moment of a dilated datum is the moment of the datum at the dilated point. -/
theorem Fstar_dilate (F : ℝ → ℝ → ℝ) (lam z : ℝ) :
    Work.Elliptic.Fstar (fun z θ => F (lam * z) θ) z = Work.Elliptic.Fstar F (lam * z) := rfl

/-- The solvability condition `OrthCond` transfers to a dilated datum (definitionally: the
moment of the dilated datum is the moment of the datum at the dilated point). -/
theorem OrthCond_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond (fun z θ => F (lam * z) θ) :=
  fun h z => h (lam * z)

end Work.H2W.PsiSlices
