/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `∂̄`-derivatives on `ℂⁿ` commute

For `u : ℂⁿ → ℂ` of class `C²`, the `(0,1)`-derivatives `∂̄_j = dbarCoord n j`
of `Work.Hormander.Weights.Defs` commute:

  `∂̄_k (∂̄_j u) = ∂̄_j (∂̄_k u)`.

This is the coordinate form of `∂̄² = 0`, and it holds because the second
derivatives of a `C²` function are symmetric (`ContDiffAt.isSymmSndFDerivAt`).

## Proof strategy

The `j`-th `(0,1)`-derivative factors through the differential,
`∂̄_j u = D_j ∘ fderiv ℝ u`, where `D_j : (ℂⁿ →L[ℝ] ℂ) →L[ℝ] ℂ` is the
continuous linear map `T ↦ (1/2)(T e_j + i·T(i e_j))` (`dbarCoordCLM`).
By the chain rule `fderiv ℝ (∂̄_j u) z = D_j ∘ fderiv ℝ (fderiv ℝ u) z`, so both
sides are built out of the symmetric bilinear form `A = fderiv ℝ (fderiv ℝ u) z`
by applying the maps `D_j` and `D_k`; the remaining algebraic identity is
`dbarCoord_CLM_comp_swap`, whose proof invokes only the symmetry of `A`.
-/
import Mathlib
import Submission.Work.Hormander.Weights.Basic

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

/-! ### The `(0,1)`-derivative as a continuous linear map of the differential -/

/-- `T ↦ (1/2)(T e_j + i·T(i e_j))`: the `(0,1)`-derivative in the `j`-th
coordinate, as a continuous linear map of the differential `T = du`.  Composed
with `fderiv ℝ u` it is `dbarCoord n j u`. -/
private noncomputable def dbarCoordCLM (n : ℕ) (j : Fin n) : (Cn n →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (1/2 : ℂ)).comp
    ((ContinuousLinearMap.apply ℝ ℂ (evec n j)) +
      (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ (ivec n j)))

/-- The value of `dbarCoordCLM`: `D_j T = (1/2)(T e_j + i·T(i e_j))`. -/
private lemma dbarCoordCLM_apply (n : ℕ) (j : Fin n) (T : Cn n →L[ℝ] ℂ) :
    dbarCoordCLM n j T = (1/2 : ℂ) * (T (evec n j) + Complex.I * T (ivec n j)) := by
  simp only [dbarCoordCLM, ContinuousLinearMap.mul_apply', ContinuousLinearMap.comp_apply,
    add_apply, ContinuousLinearMap.apply_apply]

/-- Evaluation form: `∂̄_j u z = D_j (du z)`. -/
private lemma dbarCoord_eq_dbarCoordCLM (n : ℕ) (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dbarCoord n j u z = dbarCoordCLM n j (fderiv ℝ u z) := by
  rw [dbarCoordCLM_apply]
  rfl

/-! ### The derivative of `dbarCoord` -/

/-- Chain rule form: the derivative of `∂̄_j u` is `D_j` applied to the second
derivative of `u`. -/
private lemma fderiv_dbarCoord_CLM (n : ℕ) (j : Fin n) (u : Cn n → ℂ)
    (hu : ContDiff ℝ 2 u) (z : Cn n) :
    fderiv ℝ (dbarCoord n j u) z = (dbarCoordCLM n j).comp (fderiv ℝ (fderiv ℝ u) z) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) z := hu.contDiffAt.fderiv_right (m := 1) (by norm_num)
    exact h1.differentiableAt one_ne_zero
  rw [show dbarCoord n j u = dbarCoordCLM n j ∘ fderiv ℝ u from rfl,
    fderiv_comp z (dbarCoordCLM n j).differentiableAt hd, ContinuousLinearMap.fderiv]

/-! ### The algebraic core -/

/-- If `A` is a symmetric second derivative, then the two ways of composing the
`D`'s with it agree: `D_i (D_j ∘ A) = D_j (D_i ∘ A)`. -/
private lemma dbarCoord_CLM_comp_swap (n : ℕ) (i j : Fin n) (A : Cn n →L[ℝ] (Cn n →L[ℝ] ℂ))
    (hA : ∀ v w, A v w = A w v) :
    dbarCoordCLM n i ((dbarCoordCLM n j).comp A)
      = dbarCoordCLM n j ((dbarCoordCLM n i).comp A) := by
  simp only [dbarCoordCLM_apply, ContinuousLinearMap.comp_apply]
  rw [hA (evec n i) (evec n j), hA (evec n i) (ivec n j),
      hA (ivec n i) (evec n j), hA (ivec n i) (ivec n j)]
  ring

/-! ### The main statement -/

theorem dbarCoord_comm {n : ℕ} (j k : Fin n) (u : Cn n → ℂ) (hu : ContDiff ℝ 2 u) (z : Cn n) :
    dbarCoord n k (dbarCoord n j u) z = dbarCoord n j (dbarCoord n k u) z := by
  have hA : ∀ v w, fderiv ℝ (fderiv ℝ u) z v w = fderiv ℝ (fderiv ℝ u) z w v :=
    fun v w => (ContDiffAt.isSymmSndFDerivAt hu.contDiffAt (by simp)).eq v w
  rw [dbarCoord_eq_dbarCoordCLM n k (dbarCoord n j u) z,
      dbarCoord_eq_dbarCoordCLM n j (dbarCoord n k u) z,
      fderiv_dbarCoord_CLM n j u hu z,
      fderiv_dbarCoord_CLM n k u hu z]
  exact dbarCoord_CLM_comp_swap n k j _ hA

end Work.Hormander.Weights
