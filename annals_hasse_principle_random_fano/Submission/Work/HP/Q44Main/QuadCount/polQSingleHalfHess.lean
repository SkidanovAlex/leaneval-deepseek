import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polar_basic

namespace Work.HP.Q44Main.QuadCount

open MvPolynomial
open Work.HP.MDEstimates

/-!
# The polar form evaluated on a coordinate vector

For a homogeneous quadratic form `Q` in five variables the polar form
`polQ Q v w = (Q(v+w) - Q(v) - Q(w))/2` is the bilinear form whose matrix is half the Hessian:
`polQ Q v (Pi.single i 1) = (1/2) * ∑_j hess Q i j * v j`.

The proof does not go through `polarLM`: it polarises directly from the identity
`2 * Q x = ∑_i ∑_j x_i x_j hess Q j i` (`two_mul_eval`), expanding
`4 * polQ Q v w = 2*(Q(v+w) - Q(v) - Q(w))`.  Coefficientwise the cross terms give
`∑_i ∑_j (v_i w_j + w_i v_j) hess Q j i`, and symmetry of the Hessian (`hess` is a mixed
second partial derivative, so the order does not matter) turns this into
`2 * ∑_i ∑_j v_i w_j hess Q j i`.  Specialising `w = Pi.single i 1` collapses the sum over
`j` and yields the claim.
-/

/-- The Hessian of a polynomial is symmetric: mixed second partial derivatives commute. -/
lemma hess_comm (Q : MvPolynomial (Fin 5) ℚ) (i j : Fin 5) :
    hess Q i j = hess Q j i := by
  unfold hess
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv,
      MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
  simp only [Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]
  rw [add_comm (Finsupp.single i 1) (Finsupp.single j 1)]
  congr 1
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Polarisation of the quadratic form against the Hessian: `polQ Q v w` is half the pairing of
`v` with the Hessian acting on `w`. -/
lemma two_mul_polQ (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (v w : Fin 5 → ℚ) :
    2 * polQ Q v w = ∑ i, ∑ j, v i * w j * hess Q j i := by
  have e1 : 2 * MvPolynomial.eval (v + w) Q
      = ∑ i, ∑ j, (v i + w i) * (v j + w j) * hess Q j i := by
    rw [two_mul_eval Q hQ (v + w)]
    simp only [Pi.add_apply]
  have e2 : 2 * MvPolynomial.eval v Q = ∑ i, ∑ j, v i * v j * hess Q j i := two_mul_eval Q hQ v
  have e3 : 2 * MvPolynomial.eval w Q = ∑ i, ∑ j, w i * w j * hess Q j i := two_mul_eval Q hQ w
  have hA : (∑ i, ∑ j, (v i + w i) * (v j + w j) * hess Q j i)
      = (∑ i, ∑ j, v i * v j * hess Q j i) + (∑ i, ∑ j, w i * w j * hess Q j i)
        + (∑ i, ∑ j, (v i * w j + w i * v j) * hess Q j i) := by
    have hinner : ∀ i, (∑ j, (v i + w i) * (v j + w j) * hess Q j i)
        = (∑ j, v i * v j * hess Q j i) + (∑ j, w i * w j * hess Q j i)
          + (∑ j, (v i * w j + w i * v j) * hess Q j i) := by
      intro i
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hD : (∑ i, ∑ j, (v i * w j + w i * v j) * hess Q j i)
      = 2 * (∑ i, ∑ j, v i * w j * hess Q j i) := by
    have hinner : ∀ i, (∑ j, (v i * w j + w i * v j) * hess Q j i)
        = (∑ j, v i * w j * hess Q j i) + (∑ j, w i * v j * hess Q j i) := by
      intro i
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [Finset.sum_add_distrib, two_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hess_comm Q b a]
    ring
  have h4 : 4 * polQ Q v w
      = 2 * MvPolynomial.eval (v + w) Q - 2 * MvPolynomial.eval v Q - 2 * MvPolynomial.eval w Q := by
    rw [polQ]; ring
  have key : 4 * polQ Q v w = 2 * (∑ i, ∑ j, v i * w j * hess Q j i) := by
    rw [h4, e1, e2, e3, hA, hD]
    ring
  linarith [key]

theorem polQSingleHalfHess (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (v : Fin 5 → ℚ) (i : Fin 5) :
    Work.HP.MDEstimates.polQ Q v (Pi.single i 1)
      = (1/2) * ∑ j : Fin 5, Work.HP.MDEstimates.hess Q i j * v j := by
  have hcollapse : ∀ a : Fin 5,
      (∑ b : Fin 5, v a * (Pi.single i (1 : ℚ) : Fin 5 → ℚ) b * hess Q b a)
        = v a * hess Q i a := by
    intro a
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsum :
      (∑ a : Fin 5, ∑ b : Fin 5, v a * (Pi.single i (1 : ℚ) : Fin 5 → ℚ) b * hess Q b a)
        = ∑ j : Fin 5, hess Q i j * v j := by
    rw [Finset.sum_congr rfl (fun a _ => hcollapse a)]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have h2 := two_mul_polQ Q hQ v (Pi.single i (1 : ℚ))
  rw [hsum] at h2
  rw [← h2]
  ring

end Work.HP.Q44Main.QuadCount
