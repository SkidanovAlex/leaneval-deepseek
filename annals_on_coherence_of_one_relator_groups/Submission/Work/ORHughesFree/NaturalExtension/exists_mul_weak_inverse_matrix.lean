import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORVonNeumann.Regular.matrix_vonNeumannRegular
import Submission.Work.ORHughesFree.NaturalExtension.rk_add_rk_of_ker

namespace Work.ORHughesFree.NaturalExtension

universe u

open Work.ORHughesFree

/-- **Every (not necessarily square) matrix over a von Neumann regular ring has a weak
inverse.**  For `A : Matrix (Fin n) (Fin m) R` over a von Neumann regular ring `R` there is
`X : Matrix (Fin m) (Fin n) R` with `A * X * A = A`.

Apply `Work.ORVonNeumann.Regular.exists_idempotent_of_vectors` to the *rows* of `A`: it produces
an idempotent `P : Matrix (Fin m) (Fin m) R` whose range contains all the rows of `A` and is
contained in their span, i.e. `A * P = A`, and every row of `P` is a combination of the rows of
`A`, so `X * A = P` for some `X : Matrix (Fin m) (Fin n) R`; then
`A * X * A = A * (X * A) = A * P = A`. -/
theorem exists_mul_weak_inverse_matrix {R : Type u} [Ring R] [VonNeumannRegularRing R] (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) R) : ∃ X : Matrix (Fin m) (Fin n) R, A * X * A = A := by
  have hreg : Work.ORVonNeumann.VonNeumannRegular R :=
    fun x => (inferInstance : VonNeumannRegularRing R).exists_mul_inverse x
  obtain ⟨P, _hPP, hspan, hfix⟩ :=
    Work.ORVonNeumann.Regular.exists_idempotent_of_vectors (R := R) hreg m n (fun i j => A i j)
  -- the rows of `A` are fixed by `P`: `A * P = A`
  have hAP : A * P = A := by
    ext i j
    have h := congrFun (hfix i) j
    simp only [Matrix.vecMul_apply, Matrix.col_apply, dotProduct, Matrix.mul_apply] at h ⊢
    exact h
  -- every row of `P` is a combination of the rows of `A`
  have hrow : ∀ l : Fin m, ∃ c : Fin n → R, ∑ i, c i • (fun j => A i j) = P l := by
    intro l
    have h := (Submodule.mem_span_range_iff_exists_fun R).mp (hspan (Pi.single l 1))
    rwa [Work.ORVonNeumann.Regular.row_eq_single_vecMul P l] at h
  choose c hc using hrow
  set X : Matrix (Fin m) (Fin n) R := fun l i => c l i with hX
  have hXA : X * A = P := by
    ext l j
    rw [Matrix.mul_apply, hX]
    have h := congrFun (hc l) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simpa using h
  exact ⟨X, by rw [Matrix.mul_assoc, hXA, hAP]⟩

end Work.ORHughesFree.NaturalExtension
