import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_map
import Submission.Commons.Algebra.MvPolynomial.pderivIter_rename

/-!
# The `finSuccEquiv` dictionary for the multivariate Roth lemma

Two presentations of "polynomials in `n+1` variables with a distinguished variable":

* `MvPolynomial (Fin (n+1)) K`, with the distinguished variable `X 0` (the image of
  `Fin.succ` gives the remaining variables);
* `Polynomial (MvPolynomial (Fin n) K)`, related to the first by `MvPolynomial.finSuccEquiv`.

A decomposition `f = ∑ j, C (φ j) * (ψ j).map C` in the second presentation transports to
`P = ∑ j, (rename Fin.succ (φ j)) * (aeval (X 0) (ψ j))` in the first.  This file records the
two halves of that dictionary (plus the bookkeeping for the "one-variable" factor) that the
multivariate Roth lemma needs.
-/

open MvPolynomial

namespace Submission.Subspace

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- The `K`-algebra hom `MvPolynomial (Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin n) K)`
sending `X i` to the constant polynomial `C (X i)`. -/
noncomputable def constAlgHom (K : Type*) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  MvPolynomial.aeval fun i => Polynomial.C (MvPolynomial.X i)

lemma constAlgHom_X (K : Type*) [CommSemiring K] (n : ℕ) (i : Fin n) :
    constAlgHom K n (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i) :=
  MvPolynomial.aeval_X _ i

lemma constAlgHom_apply (φ : MvPolynomial (Fin n) K) :
    constAlgHom K n φ = Polynomial.C φ := by
  induction φ using MvPolynomial.induction_on with
  | C a =>
    show MvPolynomial.aeval (fun i : Fin n => Polynomial.C (MvPolynomial.X i))
        (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a)
    rw [MvPolynomial.aeval_C]
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (Polynomial _),
      Polynomial.algebraMap_eq, ← MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, hp, constAlgHom_X, Polynomial.C_mul]

/-- `finSuccEquiv` of `rename Fin.succ φ` is the constant polynomial `C φ`. -/
lemma finSuccEquiv_rename_succ (φ : MvPolynomial (Fin n) K) :
    MvPolynomial.finSuccEquiv K n (MvPolynomial.rename Fin.succ φ) = Polynomial.C φ := by
  have h := AlgHom.congr_fun
    (show (MvPolynomial.finSuccEquiv K n).toAlgHom.comp (MvPolynomial.rename Fin.succ)
        = constAlgHom K n from by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, MvPolynomial.rename_X, constAlgHom_X]
      exact MvPolynomial.finSuccEquiv_X_succ) φ
  rw [AlgHom.comp_apply] at h
  rw [constAlgHom_apply] at h
  exact h

/-- The converse form: the constant polynomial `C φ` is the image of `rename Fin.succ φ`. -/
lemma finSuccEquiv_symm_C (φ : MvPolynomial (Fin n) K) :
    (MvPolynomial.finSuccEquiv K n).symm (Polynomial.C φ) = MvPolynomial.rename Fin.succ φ :=
  (AlgEquiv.symm_apply_eq _).mpr (finSuccEquiv_rename_succ φ).symm

/-- `finSuccEquiv` of `aeval (X 0) ψ` is `ψ.map C`. -/
lemma finSuccEquiv_aeval_X_zero (ψ : Polynomial K) :
    MvPolynomial.finSuccEquiv K n
        (Polynomial.aeval (A := MvPolynomial (Fin (n + 1)) K) (MvPolynomial.X 0) ψ) =
      ψ.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) := by
  induction ψ using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.aeval_add, map_add, Polynomial.map_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.map_monomial]
    rw [map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero]
    rw [AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (Polynomial _),
      Polynomial.algebraMap_eq, ← MvPolynomial.algebraMap_eq,
      ← Polynomial.C_mul_X_pow_eq_monomial]

/-- The converse form: `(finSuccEquiv).symm (ψ.map C) = aeval (X 0) ψ`. -/
lemma finSuccEquiv_symm_map_C (ψ : Polynomial K) :
    (MvPolynomial.finSuccEquiv K n).symm
        (ψ.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) =
      Polynomial.aeval (A := MvPolynomial (Fin (n + 1)) K) (MvPolynomial.X 0) ψ :=
  (AlgEquiv.symm_apply_eq _).mpr (finSuccEquiv_aeval_X_zero ψ).symm

/-- The "one variable" factor: `aeval (X 0) ψ` in `MvPolynomial (Fin (n+1)) K` is the rename of
the corresponding element of `MvPolynomial (Fin 1) K`. -/
lemma rename_algebraMap {m : ℕ} (e : Fin m → Fin (n + 1)) (a : K) :
    MvPolynomial.rename e (algebraMap K (MvPolynomial (Fin m) K) a) =
      algebraMap K (MvPolynomial (Fin (n + 1)) K) a :=
  AlgHom.commutes (MvPolynomial.rename e) a

lemma aeval_X_zero_eq_rename (ψ : Polynomial K) :
    Polynomial.aeval (A := MvPolynomial (Fin (n + 1)) K) (MvPolynomial.X (0 : Fin (n + 1))) ψ =
      MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1)))
        (Polynomial.aeval (A := MvPolynomial (Fin 1) K) (MvPolynomial.X (0 : Fin 1)) ψ) := by
  induction ψ using Polynomial.induction_on' with
  | add p q hp hq =>
    have hp' := hp
    have hq' := hq
    simp only [Polynomial.aeval_add]
    rw [map_add]
    rw [← hp', ← hq']
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    rw [map_mul, map_pow, MvPolynomial.rename_X]
    rw [rename_algebraMap]

end Submission.Subspace
