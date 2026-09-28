import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace Work.HP.MDEstimates

/-!
# Bilinearity of the polar form of a homogeneous quadratic form

This file proves `polar_basic`: the polar form `polQ Q x y = (Q(x+y) - Q(x) - Q(y))/2`
of a homogeneous degree-`2` polynomial `Q : MvPolynomial (Fin 5) ℚ` is a symmetric
bilinear form, satisfies `polQ Q x x = Q x`, and the evaluation `x ↦ Q x` is
homogeneous of degree two.

The mathematical content is that a homogeneous polynomial of degree two is a
quadratic form.  The construction is as follows.

* `hess Q j i` is the second partial derivative `∂_j ∂_i Q` evaluated at a point
  (it is a constant, being homogeneous of degree `0`).
* Euler's identity `∑_i X_i ∂_i Q = 2 Q`, applied once more to each `∂_i Q`
  (which is homogeneous of degree `1`), gives the "Hessian identity"
  `∑_{i,j} X_i X_j ∂_j ∂_i Q = 2 Q` (`sum_hessian`).
* Evaluating this identity exhibits `Q x` as the diagonal of the explicit
  bilinear form `(x,y) ↦ (1/2) ∑_{i,j} x_i y_j ∂_j ∂_i Q`, whose matrix is
  `polarMat Q` (`polarMat_self`).
* Feeding this bilinear form to `LinearMap.BilinMap.toQuadraticMap` produces a
  genuine `QuadraticMap` (a quadratic form), whose polar form Mathlib already
  knows to be bilinear (`polarQuad`).  Since `polQ Q` is half of that polar
  form, all the required properties follow.
-/

/-- A homogeneous polynomial of degree `0` is a constant. -/
lemma isHomogeneous_zero_eq_C {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℚ}
    (h : p.IsHomogeneous 0) : p = MvPolynomial.C (p.coeff 0) := by
  ext d
  rw [MvPolynomial.coeff_C]
  split_ifs with h0
  · rw [← h0]
  · exact h.coeff_eq_zero (fun hd0 => h0 (by
      rw [Finsupp.degree_eq_zero_iff] at hd0
      exact hd0.symm))

/-- The evaluation of a homogeneous polynomial of degree `0` is its constant term. -/
lemma eval_eq_coeff_zero {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℚ}
    (h : p.IsHomogeneous 0) (x : σ → ℚ) : MvPolynomial.eval x p = p.coeff 0 := by
  rw [isHomogeneous_zero_eq_C h]
  simp

/-- The second partial derivative `∂_j ∂_i Q` of a homogeneous quadratic form,
evaluated at any point (it is a constant). -/
def hess (Q : MvPolynomial (Fin 5) ℚ) (j i : Fin 5) : ℚ :=
  (pderiv j (pderiv i Q)).coeff 0

lemma hess_isHomogeneous (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (j i : Fin 5) : (pderiv j (pderiv i Q)).IsHomogeneous 0 :=
  (hQ.pderiv (i := i)).pderiv (i := j)

/-- Euler's identity, applied twice: the Hessian recovers `2 Q`. -/
lemma sum_hessian (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) :
    (∑ i, ∑ j, X i * X j * pderiv j (pderiv i Q)) = 2 • Q := by
  have h2 : ∑ i, X i * pderiv i Q = 2 • Q := hQ.sum_X_mul_pderiv
  have h1 : ∀ i : Fin 5, ∑ j, X j * pderiv j (pderiv i Q) = pderiv i Q := by
    intro i
    have := (hQ.pderiv (i := i)).sum_X_mul_pderiv
    simpa using this
  calc (∑ i, ∑ j, X i * X j * pderiv j (pderiv i Q))
      = ∑ i, X i * (∑ j, X j * pderiv j (pderiv i Q)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ = ∑ i, X i * pderiv i Q := by simp [h1]
    _ = 2 • Q := h2

/-- Evaluation of the Hessian identity. -/
lemma eval_sum_hess (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x : Fin 5 → ℚ) :
    MvPolynomial.eval x (∑ i, ∑ j, (X i : MvPolynomial (Fin 5) ℚ) * X j * pderiv j (pderiv i Q))
      = ∑ i, ∑ j, x i * x j * hess Q j i := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X,
    eval_eq_coeff_zero (hess_isHomogeneous Q hQ j i) x]
  rfl

/-- `2 * Q x` expressed through the second derivatives of `Q`. -/
lemma two_mul_eval (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x : Fin 5 → ℚ) :
    2 * MvPolynomial.eval x Q = ∑ i, ∑ j, x i * x j * hess Q j i := by
  have h := congrArg (MvPolynomial.eval x) (sum_hessian Q hQ)
  rw [eval_sum_hess Q hQ x] at h
  rw [h]
  simp [nsmul_eq_mul]

/-- The matrix of the polar bilinear form of `Q`: half the Hessian of `Q`. -/
def polarMat (Q : MvPolynomial (Fin 5) ℚ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => (1/2) * hess Q j i

/-- The diagonal of the polar bilinear form recovers `Q`. -/
lemma polarMat_self (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x : Fin 5 → ℚ) :
    (Matrix.toBilin' (polarMat Q) x) x = MvPolynomial.eval x Q := by
  rw [Matrix.toBilin'_apply]
  have h := two_mul_eval Q hQ x
  have hsum : (∑ i, ∑ j, x i * polarMat Q i j * x j)
      = (1/2) * ∑ i, ∑ j, x i * x j * hess Q j i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [polarMat]
    ring
  rw [hsum, ← h]
  ring

/-- The quadratic form `x ↦ Q x` attached to `Q`, obtained as the diagonal of the
explicit polar bilinear form `polarMat Q`. -/
def polarQuad (Q : MvPolynomial (Fin 5) ℚ) : QuadraticMap ℚ (Fin 5 → ℚ) ℚ :=
  (Matrix.toBilin' (polarMat Q)).toQuadraticMap

lemma polarQuad_apply (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x : Fin 5 → ℚ) : polarQuad Q x = MvPolynomial.eval x Q := by
  rw [polarQuad, LinearMap.BilinMap.toQuadraticMap_apply]
  exact polarMat_self Q hQ x

/-- `polQ Q` is half the polar form of the quadratic form `polarQuad Q`. -/
lemma polQ_eq_half_polar (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (a b : Fin 5 → ℚ) :
    polQ Q a b = (1/2) * QuadraticMap.polar (⇑(polarQuad Q)) a b := by
  rw [polQ, QuadraticMap.polar, polarQuad_apply Q hQ a, polarQuad_apply Q hQ b,
    polarQuad_apply Q hQ (a + b)]
  ring

theorem polar_basic (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) :
    (∀ x y z : Fin 5 → ℚ, polQ Q (x + y) z = polQ Q x z + polQ Q y z) ∧
    (∀ (c : ℚ) (x y : Fin 5 → ℚ), polQ Q (c • x) y = c * polQ Q x y) ∧
    (∀ x y : Fin 5 → ℚ, polQ Q x y = polQ Q y x) ∧
    (∀ x : Fin 5 → ℚ, polQ Q x x = MvPolynomial.eval x Q) ∧
    (∀ (c : ℚ) (x : Fin 5 → ℚ), MvPolynomial.eval (c • x) Q = c ^ 2 * MvPolynomial.eval x Q) ∧
    (∀ x y : Fin 5 → ℚ,
      MvPolynomial.eval (x + y) Q = MvPolynomial.eval x Q + MvPolynomial.eval y Q + 2 * polQ Q x y)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    rw [polQ_eq_half_polar Q hQ (x + y) z, polQ_eq_half_polar Q hQ x z,
      polQ_eq_half_polar Q hQ y z, QuadraticMap.polar_add_left]
    ring
  · intro c x y
    rw [polQ_eq_half_polar Q hQ (c • x) y, polQ_eq_half_polar Q hQ x y,
      QuadraticMap.polar_smul_left, smul_eq_mul]
    ring
  · intro x y
    rw [polQ_eq_half_polar Q hQ x y, polQ_eq_half_polar Q hQ y x, QuadraticMap.polar_comm]
  · intro x
    rw [polQ_eq_half_polar Q hQ x x, QuadraticMap.polar_self, polarQuad_apply Q hQ x]
    ring
  · intro c x
    rw [← polarQuad_apply Q hQ (c • x), ← polarQuad_apply Q hQ x, QuadraticMap.map_smul]
    ring
  · intro x y
    rw [← polarQuad_apply Q hQ (x + y), ← polarQuad_apply Q hQ x, ← polarQuad_apply Q hQ y,
      polQ_eq_half_polar Q hQ x y]
    rw [show QuadraticMap.polar (⇑(polarQuad Q)) x y
        = polarQuad Q (x + y) - polarQuad Q x - polarQuad Q y from rfl]
    ring

end Work.HP.MDEstimates
