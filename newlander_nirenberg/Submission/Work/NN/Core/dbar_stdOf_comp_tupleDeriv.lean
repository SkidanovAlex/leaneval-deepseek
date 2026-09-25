import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Defs

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

variable {n : ℕ}

/-! ## Identities for the coordinate map `tupleDeriv T` -/

/-- `tupleDeriv T` is a left inverse of `tupleDerivInv T`: `T⁻¹` of a coordinate tuple `z` is
sent back to `z`. -/
@[simp] lemma tupleDeriv_tupleDerivInv (T : E n ≃L[ℝ] F n) (z : Cn n) :
    tupleDeriv T (tupleDerivInv T z) = z := by
  simp [tupleDeriv, tupleDerivInv]

/-- `tupleDeriv T` intertwines the standard complex structure `stdOf T` on `E n` with
multiplication by `i` on `ℂⁿ`. -/
@[simp] lemma tupleDeriv_stdOf (T : E n ≃L[ℝ] F n) (y v : E n) :
    tupleDeriv T (stdOf T y v) = Complex.I • tupleDeriv T v := by
  show ecInvL n (T (T.symm (Complex.I • T v))) = Complex.I • ecInvL n (T v)
  rw [ContinuousLinearEquiv.apply_symm_apply, ecInvL_smul]

/-- `tupleDeriv T` as a continuous linear equivalence `E n ≃L[ℝ] ℂⁿ`. -/
noncomputable def tupleDerivEquiv (T : E n ≃L[ℝ] F n) : E n ≃L[ℝ] Cn n :=
  T.trans (ecInv n)

/-- **The chain rule for `g ∘ tupleDeriv T`.**  Since `tupleDeriv T` is a continuous linear
*equivalence*, `fderiv` and precomposition commute unconditionally (no differentiability
hypothesis on `g` is needed: when `g` is not differentiable both sides vanish). -/
lemma fderiv_comp_tupleDeriv (T : E n ≃L[ℝ] F n) (g : Cn n → ℂ) (x : E n) :
    fderiv ℝ (fun y : E n => g (tupleDeriv T y)) x
      = (fderiv ℝ g (tupleDeriv T x)).comp (tupleDeriv T) := by
  have h := ContinuousLinearEquiv.comp_right_fderiv (iso := tupleDerivEquiv T) (f := g) (x := x)
  rw [show (g ∘ ⇑(tupleDerivEquiv T)) = fun y : E n => g (tupleDeriv T y) from by
        funext y; rfl] at h
  rw [show (tupleDerivEquiv T) x = tupleDeriv T x from rfl] at h
  rw [show (↑(tupleDerivEquiv T) : E n →L[ℝ] Cn n) = tupleDeriv T from rfl] at h
  exact h

/-- Pointwise form of `fderiv_comp_tupleDeriv`. -/
lemma fderiv_comp_tupleDeriv_apply (T : E n ≃L[ℝ] F n) (g : Cn n → ℂ) (x v : E n) :
    fderiv ℝ (fun y : E n => g (tupleDeriv T y)) x v
      = fderiv ℝ g (tupleDeriv T x) (tupleDeriv T v) := by
  rw [fderiv_comp_tupleDeriv, ContinuousLinearMap.comp_apply]

/-! ## The flat model `ℂⁿ` -/

/-- `dbarCn Jstd` of the standard structure, applied to a vector. -/
lemma dbarCn_std_apply {n : ℕ} (g : Cn n → ℂ) (z w : Cn n) :
    dbarCn (JstdCn n) g z w
      = (1/2 : ℂ) * (fderiv ℝ g z w + Complex.I * fderiv ℝ g z (Complex.I • w)) := by
  simp only [dbarCn, add_apply, smul_apply, ContinuousLinearMap.comp_apply, JstdCn_apply]
  rw [Complex.real_smul]
  push_cast
  ring

/-- The `∂̄` of the flat model with the standard structure, written with the standard coefficients
`dbarCoord j g` of the `(0,1)`-form `Σ_j ∂̄_j g dz̄_j`. -/
lemma dbarCn_std_apply_eq_stdForm {n : ℕ} (g : Cn n → ℂ) (z w : Cn n) :
    (1/2 : ℂ) * (fderiv ℝ g z w + Complex.I * fderiv ℝ g z (Complex.I • w))
      = stdForm (fun j (z' : Cn n) => Work.CR.Flat.dbarCoord j g z') z w := by
  rw [← dbarCn_std_apply, dbarCn_std_eq_stdForm]
  exact congrArg (fun F : Cn n →L[ℝ] ℂ => F w)
    (stdForm_ext (f := fun j _ => Work.CR.Flat.dbarCoord j g z)
      (g := fun j (z' : Cn n) => Work.CR.Flat.dbarCoord j g z') (fun j => rfl))

/-! ## The main identity -/

theorem dbar_stdOf_comp_tupleDeriv {n : ℕ} (T : LeanEval.Geometry.NewlanderNirenberg.E n ≃L[ℝ] Submission.F n) (g : (Fin n → ℂ) → ℂ) (z w : Fin n → ℂ) :
    Submission.dbar (Submission.stdOf T)
        (fun y : LeanEval.Geometry.NewlanderNirenberg.E n => g (Work.NN.Core.tupleDeriv T y))
        (Work.NN.Core.tupleDerivInv T z) (Work.NN.Core.tupleDerivInv T w)
      = Work.NN.Core.stdForm (fun j (z' : Fin n → ℂ) => Work.CR.Flat.dbarCoord j g z') z w := by
  rw [Submission.dbar_apply]
  rw [fderiv_comp_tupleDeriv_apply, fderiv_comp_tupleDeriv_apply]
  simp only [tupleDeriv_tupleDerivInv, tupleDeriv_stdOf]
  exact dbarCn_std_apply_eq_stdForm g z w

end Work.NN.Core
