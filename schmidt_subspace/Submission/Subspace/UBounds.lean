import Mathlib
import Submission.Subspace.GridRefine
import Submission.Commons.Algebra.MvPolynomial.pderivIter_map

/-!
# The `U`-coordinates (`A`-bounds, step E of the subspace theorem)

The `A`-bounds compare two evaluations of the auxiliary polynomial: the *small* one in the
`U`-coordinates `u (h,k) = L_k(X_h)` (the values of the linear forms, which are small on the
approximation domain) and the *integral* one in the coordinate variables `x (h,j) ∈ ℤ`.

This file sets up the change of variables

`X (h,j) ↦ ∑ k, Λ k j · U (h,k)`

(`Λ` = the inverse of the matrix of the forms) and proves the basic evaluation identity
`aeval u (aeval Φ_Λ Q) = aeval x Q` whenever `x (h,j) = ∑ k, Λ k j · u (h,k)`,
together with the behaviour of `Φ_Λ` under a change of base ring and the integrality of
`aeval x (∂^e F)` for an integral `F` and an integral point.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {m N : ℕ}

/-- The block-diagonal linear substitution `X (h,j) ↦ ∑ k, Λ k j · X (h,k)`. -/
noncomputable def PhiL {R : Type*} [CommSemiring R] (Λ : Matrix (Fin N) (Fin N) R) :
    Fin m × Fin N → MvPolynomial (Fin m × Fin N) R :=
  fun x => ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)

/-- **The evaluation identity.**  If `x` is the `Λ`-image of `u` (i.e.
`x (h,j) = ∑ k, Λ k j · u (h,k)`), then evaluating the `Λ`-expansion of `Q` at `u` gives the
evaluation of `Q` at `x`. -/
theorem aeval_PhiL_eq {R : Type*} [CommSemiring R] (Λ : Matrix (Fin N) (Fin N) R)
    (u x : Fin m × Fin N → R)
    (hx : ∀ q : Fin m × Fin N, x q = ∑ k : Fin N, Λ k q.2 * u (q.1, k))
    (Q : MvPolynomial (Fin m × Fin N) R) :
    MvPolynomial.aeval u (MvPolynomial.aeval (PhiL Λ) Q) = MvPolynomial.aeval x Q := by
  rw [MvPolynomial.comp_aeval_apply (f := PhiL Λ) (φ := MvPolynomial.aeval u) Q]
  have hfun : (fun z : Fin m × Fin N => MvPolynomial.aeval u (PhiL Λ z)) = x := by
    funext z
    rw [PhiL, map_sum]
    simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self_apply]
    exact (hx z).symm
  rw [hfun]

/-- `Φ_Λ` commutes with a change of base ring. -/
theorem map_PhiL {K R : Type*} [CommSemiring K] [CommSemiring R] [Algebra K R]
    (Λ : Matrix (Fin N) (Fin N) K) (z : Fin m × Fin N) :
    (PhiL Λ z).map (algebraMap K R) = PhiL (Λ.map (algebraMap K R)) z := by
  rw [PhiL, PhiL, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rfl

/-- The `Λ`-expansion commutes with a change of base ring. -/
theorem map_aeval_PhiL {K R : Type*} [CommSemiring K] [CommSemiring R] [Algebra K R]
    (Λ : Matrix (Fin N) (Fin N) K) (Q : MvPolynomial (Fin m × Fin N) K) :
    (MvPolynomial.aeval (PhiL Λ) Q).map (algebraMap K R) =
      MvPolynomial.aeval (PhiL (Λ.map (algebraMap K R))) (Q.map (algebraMap K R)) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
        MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X]
      rw [hp, map_PhiL]

/-- Values of an integral polynomial with iterated derivatives at an integral point are
integers. -/
theorem aeval_pderivIter_int {S : Type*} [CommRing S] [Algebra ℤ S]
    (F : MvPolynomial (Fin m × Fin N) ℤ)
    (e : (Fin m × Fin N) →₀ ℕ) (x : Fin m × Fin N → ℤ) :
    ∃ n : ℤ, MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ S (x q))
      (Commons.Algebra.MvPolynomial.pderivIter e (F.map (algebraMap ℤ S))) =
        algebraMap ℤ S n := by
  refine ⟨MvPolynomial.aeval x (Commons.Algebra.MvPolynomial.pderivIter e F), ?_⟩
  rw [Commons.Algebra.MvPolynomial.pderivIter_map]
  have h1 : MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ S (x q))
      ((Commons.Algebra.MvPolynomial.pderivIter e F).map (algebraMap ℤ S)) =
      MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ S (x q))
        (Commons.Algebra.MvPolynomial.pderivIter e F) :=
    MvPolynomial.aeval_map_algebraMap S _ _
  rw [h1, MvPolynomial.aeval_eq_eval₂Hom]
  have h2 := MvPolynomial.map_aeval (R := ℤ) (σ := Fin m × Fin N)
    (g := x) (φ := algebraMap ℤ S) (p := Commons.Algebra.MvPolynomial.pderivIter e F)
  rw [show (algebraMap ℤ S).comp (algebraMap ℤ ℤ) = (algebraMap ℤ S) from by
    ext n; simp] at h2
  exact h2.symm

end Submission.Subspace
