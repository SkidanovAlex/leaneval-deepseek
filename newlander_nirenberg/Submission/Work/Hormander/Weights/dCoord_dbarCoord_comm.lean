/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `∂` and `∂̄` commute on `ℂⁿ`

For `u : ℂⁿ → ℂ` of class `C²` the `(1,0)`- and `(0,1)`-derivatives
`∂_i = dCoord n i` and `∂̄_j = dbarCoord n j` of
`Work.Hormander.Weights.Defs` commute:

  `∂_i (∂̄_j u) = ∂̄_j (∂_i u)`.

This is the mixed part of `∂∂̄ = ∂̄∂`; the `∂̄∂̄` case is
`Work.Hormander.Weights.dbarCoord_comm`.

## Proof strategy

Both operators factor through the differential: for a complex number `s`,
`C_s := coordCLM n s j : (ℂⁿ →L[ℝ] ℂ) →L[ℝ] ℂ` is the continuous linear map
`T ↦ (1/2)(T e_j + s · T(i e_j))`, and

  `∂̄_j u = C_I ∘ du`,   `∂_j u = C_{-I} ∘ du`.

The chain rule gives `d(∂̄_j u) z = C_I ∘ d(du) z` and `d(∂_j u) z = C_{-I} ∘ d(du) z`
(`fderiv_dbarCoord_CLM`, `fderiv_dCoord_CLM`), and the second derivative
`A := d(du) z` is symmetric (`ContDiffAt.isSymmSndFDerivAt`).  The two sides are
then, in turn, `C_{-I} ∘ (C_I ∘ A)` and `C_I ∘ (C_{-I} ∘ A)`, and these agree
for *any* two scalars `s`, `t` by the symmetry of `A` alone
(`coordCLM_comp_swap`), because both sides expand to

  `(1/4)·(A e_i e_j + t·(A i e_i) e_j + s·(A e_i)(i e_j) + s t·(A i e_i)(i e_j))`.

Indeed, after rewriting every `A v w` as `A w v` the two expressions are equal
by `ring`.  The constants `s = -I`, `t = I` only matter for the sign convention,
never for the commutation.
-/
import Mathlib
import Submission.Work.Hormander.Weights.Basic
import Submission.Work.Hormander.Weights.dbarCoord_comm

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

/-! ### The `∂`- and `∂̄`-derivatives as continuous linear maps of the differential -/

/-- `T ↦ (1/2)(T e_j + s·T(i e_j))`: the `j`-th complex derivative `(1/2)(∂_{x_j}
+ s ∂_{y_j})` in the `j`-th coordinate, as a continuous linear map of the
differential `T = du`.  For `s = i` this is `∂̄_j`, for `s = -i` it is `∂_j`. -/
private noncomputable def coordCLM (n : ℕ) (s : ℂ) (j : Fin n) : (Cn n →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (1/2 : ℂ)).comp
    ((ContinuousLinearMap.apply ℝ ℂ (evec n j)) +
      (ContinuousLinearMap.mul ℝ ℂ s).comp (ContinuousLinearMap.apply ℝ ℂ (ivec n j)))

/-- The value of `coordCLM`: `C_s T = (1/2)(T e_j + s·T(i e_j))`. -/
private lemma coordCLM_apply (n : ℕ) (s : ℂ) (j : Fin n) (T : Cn n →L[ℝ] ℂ) :
    coordCLM n s j T = (1/2 : ℂ) * (T (evec n j) + s * T (ivec n j)) := by
  simp only [coordCLM, ContinuousLinearMap.mul_apply', ContinuousLinearMap.comp_apply,
    add_apply, ContinuousLinearMap.apply_apply]

/-! ### The operators as compositions with `coordCLM` -/

/-- Evaluation form: `∂̄_j u z = C_i (du z)`. -/
private lemma dbarCoord_eq_coordCLM (n : ℕ) (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dbarCoord n j u z = coordCLM n Complex.I j (fderiv ℝ u z) := by
  rw [coordCLM_apply]; rfl

/-- Evaluation form: `∂_j u z = C_{-i} (du z)`. -/
private lemma dCoord_eq_coordCLM (n : ℕ) (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dCoord n j u z = coordCLM n (-Complex.I) j (fderiv ℝ u z) := by
  rw [coordCLM_apply]; simp only [dCoord]; ring

/-! ### The derivatives of `∂̄_j u` and `∂_j u` -/

/-- The derivative of `w ↦ C_s (du w)` is `C_s` applied to the second derivative
of `u`. -/
private lemma fderiv_coordCLM (n : ℕ) (s : ℂ) (j : Fin n) (u : Cn n → ℂ)
    (hu : ContDiff ℝ 2 u) (z : Cn n) :
    fderiv ℝ (fun w => coordCLM n s j (fderiv ℝ u w)) z
      = (coordCLM n s j).comp (fderiv ℝ (fderiv ℝ u) z) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) z := hu.contDiffAt.fderiv_right (m := 1) (by norm_num)
    exact h1.differentiableAt one_ne_zero
  change fderiv ℝ ((coordCLM n s j) ∘ (fderiv ℝ u)) z
      = (coordCLM n s j).comp (fderiv ℝ (fderiv ℝ u) z)
  rw [fderiv_comp z (coordCLM n s j).differentiableAt hd, ContinuousLinearMap.fderiv]

/-- Chain rule form: the derivative of `∂̄_j u` is `C_i` applied to the second
derivative of `u`. -/
private lemma fderiv_dbarCoord_CLM (n : ℕ) (j : Fin n) (u : Cn n → ℂ)
    (hu : ContDiff ℝ 2 u) (z : Cn n) :
    fderiv ℝ (dbarCoord n j u) z = (coordCLM n Complex.I j).comp (fderiv ℝ (fderiv ℝ u) z) := by
  have hfun : dbarCoord n j u = fun w => coordCLM n Complex.I j (fderiv ℝ u w) :=
    funext fun w => dbarCoord_eq_coordCLM n j u w
  rw [hfun, fderiv_coordCLM n Complex.I j u hu z]

/-- Chain rule form: the derivative of `∂_j u` is `C_{-i}` applied to the second
derivative of `u`. -/
private lemma fderiv_dCoord_CLM (n : ℕ) (j : Fin n) (u : Cn n → ℂ)
    (hu : ContDiff ℝ 2 u) (z : Cn n) :
    fderiv ℝ (dCoord n j u) z = (coordCLM n (-Complex.I) j).comp (fderiv ℝ (fderiv ℝ u) z) := by
  have hfun : dCoord n j u = fun w => coordCLM n (-Complex.I) j (fderiv ℝ u w) :=
    funext fun w => dCoord_eq_coordCLM n j u w
  rw [hfun, fderiv_coordCLM n (-Complex.I) j u hu z]

/-! ### The algebraic core -/

/-- If `A` is a symmetric second derivative, then the two ways of composing the
maps `C_s` and `C_t` with it agree: `C_s (C_t ∘ A) = C_t (C_s ∘ A)`.  The two
sides are both `(1/4)(A e_i e_j + t·A e_i (i e_j) + s·A (i e_i) e_j
+ s t·A (i e_i)(i e_j))`. -/
private lemma coordCLM_comp_swap (n : ℕ) (s t : ℂ) (i j : Fin n)
    (A : Cn n →L[ℝ] (Cn n →L[ℝ] ℂ)) (hA : ∀ v w, A v w = A w v) :
    coordCLM n s i ((coordCLM n t j).comp A) = coordCLM n t j ((coordCLM n s i).comp A) := by
  simp only [coordCLM_apply, ContinuousLinearMap.comp_apply]
  rw [hA (evec n i) (evec n j), hA (evec n i) (ivec n j),
      hA (ivec n i) (evec n j), hA (ivec n i) (ivec n j)]
  ring

/-! ### The main statement -/

theorem dCoord_dbarCoord_comm {n : ℕ} (i j : Fin n) (u : Cn n → ℂ) (hu : ContDiff ℝ 2 u) (z : Cn n) :
    dCoord n i (dbarCoord n j u) z = dbarCoord n j (dCoord n i u) z := by
  have hA : ∀ v w, fderiv ℝ (fderiv ℝ u) z v w = fderiv ℝ (fderiv ℝ u) z w v :=
    fun v w => (ContDiffAt.isSymmSndFDerivAt hu.contDiffAt (by simp)).eq v w
  rw [dCoord_eq_coordCLM n i (dbarCoord n j u) z,
      dbarCoord_eq_coordCLM n j (dCoord n i u) z,
      fderiv_dbarCoord_CLM n j u hu z,
      fderiv_dCoord_CLM n i u hu z]
  exact coordCLM_comp_swap n (-Complex.I) Complex.I i j _ hA

end Work.Hormander.Weights
