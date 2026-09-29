import Mathlib
import Submission.Work.TMC14Core.AdjBase

/-!
# `Work.TMC14Core.adjugateTraceCharpolyDeriv`

We prove Jacobi's formula for the derivative of a determinant over a polynomial ring,

  `(det A).derivative = (A' * adjugate A).trace`,  where `A'` is the entrywise derivative,

and specialise it to `A = charmatrix M`.  Since `charmatrix M = X • 1 - M` has entrywise
derivative `1`, and evaluation at `z` commutes with `adjugate` and `trace`, this yields

  `(M.charpoly).derivative.eval z = (adjugate (z • 1 - M)).trace`.
-/

open Polynomial Matrix Finset

namespace Work.TMC14Core

/-- **Jacobi's formula**, in the form needed here: for a matrix `A` over `R[X]`,
the derivative of `det A` is the trace of the entrywise derivative of `A` times
the adjugate of `A`. -/
theorem det_derivative_eq_trace_mul_adjugate {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) (Polynomial R)) :
    (A.det).derivative = ((A.map Polynomial.derivative) * A.adjugate).trace := by
  -- Replacing column `i` of `A` by the `i`-th column of `A'` gives, by Cramer's rule,
  -- the `i`-th column of `A' * adjugate A`.
  have hdet : ∀ (i : Fin n) (u : Fin n → Polynomial R),
      (A.updateCol i u).det = ∑ k : Fin n, A.adjugate i k * u k := by
    intro i u
    rw [← Matrix.cramer_apply A u i, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_apply]
    rfl
  -- Expanding `det (A.updateCol i u)` along permutations splits off the `i`-th factor.
  have hprod : ∀ (i : Fin n) (u : Fin n → Polynomial R) (σ : Equiv.Perm (Fin n)),
      (∏ j ∈ Finset.univ.erase i, A (σ j) j) * u (σ i)
        = ∏ j : Fin n, (A.updateCol i u) (σ j) j := by
    intro i u σ
    rw [← Finset.prod_erase_mul Finset.univ
      (fun j => (A.updateCol i u) (σ j) j) (Finset.mem_univ i)]
    congr 1
    · refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [Finset.mem_erase] at hj
      rw [Matrix.updateCol_ne (M := A) (i := σ j) (j := i) (c := u) (j' := j) hj.1]
    · rw [Matrix.updateCol_self]
  have key : ∀ (i : Fin n) (u : Fin n → Polynomial R),
      (∑ σ : Equiv.Perm (Fin n),
          Polynomial.C ((Equiv.Perm.sign σ : ℤ) : R) *
            ((∏ j ∈ Finset.univ.erase i, A (σ j) j) * u (σ i)))
        = ∑ k : Fin n, A.adjugate i k * u k := by
    intro i u
    rw [← hdet i u, Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Polynomial.C_eq_intCast, ← hprod i u σ]
  -- Leibniz formula, then differentiate the product termwise.
  rw [Matrix.det_apply', Polynomial.derivative_sum]
  trans ∑ σ : Equiv.Perm (Fin n), Polynomial.C ((Equiv.Perm.sign σ : ℤ) : R) *
        (∑ i ∈ Finset.univ,
          (∏ j ∈ Finset.univ.erase i, A (σ j) j) * (A.map Polynomial.derivative) (σ i) i)
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Polynomial.C_eq_intCast, Polynomial.derivative_C_mul,
      Polynomial.derivative_prod_finset]
    congr 1
  -- Interchange the two finite sums.
  trans ∑ i ∈ Finset.univ, ∑ σ : Equiv.Perm (Fin n),
        Polynomial.C ((Equiv.Perm.sign σ : ℤ) : R) *
          ((∏ j ∈ Finset.univ.erase i, A (σ j) j) * (A.map Polynomial.derivative) (σ i) i)
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  -- Identify each inner sum using `key`.
  trans ∑ i ∈ Finset.univ, ∑ k : Fin n, A.adjugate i k * (A.map Polynomial.derivative) k i
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact key i (fun k => (A.map Polynomial.derivative) k i)
  · rw [Matrix.trace_mul_comm, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]

/-- Avila–Jitomirskaya, *The Ten Martini Problem*: the derivative of the characteristic
polynomial of `M` at `z` is the trace of the adjugate of `z • 1 - M`. -/
theorem adjugateTraceCharpolyDeriv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (M.charpoly).derivative.eval z = (Matrix.adjugate (z • (1 : Matrix (Fin n) (Fin n) ℂ) - M)).trace := by
  -- The characteristic matrix `X • 1 - M` has entrywise derivative `1`.
  have hderiv : (M.charmatrix).map Polynomial.derivative = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.map_apply, Matrix.charmatrix_apply_eq]
    · simp [Matrix.map_apply, Matrix.charmatrix_apply_ne M i j h, h]
  have hpoly : (M.charpoly).derivative = (M.charmatrix).adjugate.trace := by
    have h := det_derivative_eq_trace_mul_adjugate (M.charmatrix)
    rw [hderiv, Matrix.one_mul] at h
    exact h
  -- Evaluation at `z` commutes with `trace` and with `adjugate`.
  have h1 : ((M.charmatrix).adjugate.trace).eval z
      = ((M.charmatrix).adjugate.map (Polynomial.eval z)).trace := by
    simpa using
      AddMonoidHom.map_trace (Polynomial.evalRingHom z) ((M.charmatrix).adjugate)
  have h2 : ((M.charmatrix).adjugate.map (Polynomial.eval z))
      = ((M.charmatrix).map (Polynomial.eval z)).adjugate := by
    have := RingHom.map_adjugate (Polynomial.evalRingHom z) (M.charmatrix)
    simpa [RingHom.mapMatrix_apply] using this
  have h3 : (M.charmatrix).map (Polynomial.eval z)
      = z • (1 : Matrix (Fin n) (Fin n) ℂ) - M := map_charmatrix M z
  rw [hpoly, h1, h2, h3]

end Work.TMC14Core
