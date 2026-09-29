import Mathlib
import Submission.Work.TMC14Core.detExpandXsmulOne
import Submission.Work.TMC14Core.adjugateSelfEqMinor

/-!
# The trace-of-adjugate formula for the derivative of the characteristic polynomial

For a square matrix `M` over a commutative ring `R`, the classical Jacobi-type identity

`(charpoly M)'(z) = trace (adjugate (z • 1 - M))`

holds.  We prove it by writing `charpoly M = det (B)` with `B = A.map C + X • 1`
(`A = z • 1 - M`) and using the multilinear expansion of `det (A + X • 1)` in the rows,
whose `X ^ 1` coefficient is the trace of the adjugate of `A`.
-/

namespace Work.TMC14Core

open Polynomial Matrix Finset

/-- The `k = 1` case of the multilinear expansion: singletons of a finite type reindex
the `1`-element subsets. -/
lemma sum_singletons_eq_sum_powersetCard_one {α : Type*} [Fintype α] [DecidableEq α]
    {M : Type*} [AddCommMonoid M] (f : Finset α → M) :
    (∑ i : α, f {i}) = ∑ s ∈ (Finset.univ : Finset α).powersetCard 1, f s := by
  refine Finset.sum_bij (fun i _ => ({i} : Finset α)) ?_ ?_ ?_ ?_
  · intro i _; simp [Finset.mem_powersetCard]
  · intro a _ b _ h; simpa using h
  · intro b hb
    simp only [Finset.mem_powersetCard] at hb
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hb.2
    exact ⟨i, Finset.mem_univ i, hi.symm⟩
  · intro i _; rfl

/-- The coefficient of `X ^ 1` in `det (A.map C + X • 1)` is the trace of the
adjugate of `A`. -/
theorem coeff_one_det_map_C_add_X_smul_one {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    ((A.map Polynomial.C + (Polynomial.X : Polynomial R) •
        (1 : Matrix (Fin n) (Fin n) (Polynomial R))).det).coeff 1
      = (Matrix.adjugate A).trace := by
  rw [detExpandXsmulOne A]
  simp only [Polynomial.finsetSum_coeff]
  have h2 : ∀ t : Finset (Fin n),
      ((Polynomial.X : Polynomial R) ^ t.card *
        Polynomial.C ((Matrix.of (t.piecewise (1 : Matrix (Fin n) (Fin n) R).row A.row)).det)).coeff 1
      = if 1 = t.card then
          ((Matrix.of (t.piecewise (1 : Matrix (Fin n) (Fin n) R).row A.row)).det) else 0 := by
    intro t
    rw [mul_comm, Polynomial.coeff_C_mul_X_pow]
  simp only [h2]
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun a : Finset (Fin n) => 1 = a.card)
      = (Finset.univ : Finset (Fin n)).powersetCard 1 := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨Finset.subset_univ s, h.symm⟩, fun h => h.2.symm⟩
  rw [hset]
  rw [← sum_singletons_eq_sum_powersetCard_one
    (fun s : Finset (Fin n) => (Matrix.of (s.piecewise (1 : Matrix (Fin n) (Fin n) R).row A.row)).det)]
  rw [Finset.sum_congr rfl (fun x _ => (adjugateSelfEqMinor A x).symm), Matrix.trace]
  rfl

/-- The derivative at `0` of `det (A.map C + X • 1)` is the trace of the adjugate
of `A` (Jacobi's formula in its polynomial form). -/
theorem key {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    (Polynomial.derivative (A.map Polynomial.C + (Polynomial.X : Polynomial R) •
        (1 : Matrix (Fin n) (Fin n) (Polynomial R))).det).eval 0
      = (Matrix.adjugate A).trace := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  norm_num
  exact coeff_one_det_map_C_add_X_smul_one A

/-- Differentiating `p` at `z` equals differentiating `p.comp (X + C z)` at `0`. -/
theorem deriv_comp_X_add_C {p : Polynomial ℂ} {z : ℂ} :
    (p.comp (Polynomial.X + Polynomial.C z)).derivative.eval 0 = p.derivative.eval z := by
  rw [Polynomial.derivative_comp]
  simp only [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
    one_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]

/-- `charpoly M`, composed with the shift `X ↦ X + z`, is the determinant of
`(z • 1 - M).map C + X • 1`. -/
theorem charpoly_comp_X_add_C {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpoly.comp (Polynomial.X + Polynomial.C z)
      = ((z • 1 - M).map Polynomial.C +
          (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ))).det := by
  rw [← Matrix.charpoly_sub_scalar M z, Matrix.charpoly]
  have hmat : Matrix.charmatrix (M - Matrix.scalar (Fin n) z)
      = ((z • 1 - M).map Polynomial.C) +
          (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.charmatrix, Matrix.map_apply, Matrix.smul_apply, Matrix.scalar_apply]
      ring
    · simp [Matrix.charmatrix, Matrix.map_apply, Matrix.smul_apply, Matrix.scalar_apply,
        hij]
  rw [hmat]

theorem charpolyDerivAdj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (z : ℂ) :
    (M.charpoly).derivative.eval z = (Matrix.adjugate (z • 1 - M)).trace := by
  have hcomp := charpoly_comp_X_add_C M z
  have hderiv : (M.charpoly.comp (Polynomial.X + Polynomial.C z)).derivative.eval 0
      = (M.charpoly).derivative.eval z := deriv_comp_X_add_C
  rw [← hderiv, hcomp]
  exact key (z • 1 - M)

end Work.TMC14Core
