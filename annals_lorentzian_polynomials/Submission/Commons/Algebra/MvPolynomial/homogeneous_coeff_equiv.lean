import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open MvPolynomial Finsupp

namespace Commons.Algebra.MvPolynomial

set_option linter.style.haveILetI false in
theorem homogeneous_coeff_equiv (n d : ℕ) :
  ∃ e : homogeneousSubmodule (Fin n) ℝ d ≃ₗ[ℝ]
      ({m : Fin n →₀ ℕ // Finsupp.weight 1 m = d} → ℝ),
    ∀ (f : homogeneousSubmodule (Fin n) ℝ d)
      (m : {m : Fin n →₀ ℕ // Finsupp.weight 1 m = d}),
      e f m = MvPolynomial.coeff m.1 f.1 := by
  classical
  let S : Set (Fin n →₀ ℕ) := {m | Finsupp.weight (1 : Fin n → ℕ) m = d}
  have hsub : homogeneousSubmodule (Fin n) ℝ d = MvPolynomial.restrictSupport ℝ S := by
    dsimp [S, MvPolynomial.restrictSupport]
    calc
      homogeneousSubmodule (Fin n) ℝ d
          = MvPolynomial.weightedHomogeneousSubmodule ℝ (1 : Fin n → ℕ) d := by
            rw [MvPolynomial.weightedHomogeneousSubmodule_one]
      _ = AddMonoidAlgebra.supported ℝ ℝ
          {m : Fin n →₀ ℕ | Finsupp.weight (1 : Fin n → ℕ) m = d} := by
            rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  let eSub : homogeneousSubmodule (Fin n) ℝ d ≃ₗ[ℝ] MvPolynomial.restrictSupport ℝ S :=
    LinearEquiv.ofEq _ _ hsub
  haveI : Finite S := by
    have hfin : S.Finite := by
      dsimp [S]
      exact Finsupp.finite_of_nat_weight_eq (1 : Fin n → ℕ) (by intro x; simp) d
    exact hfin.to_subtype
  let b : Module.Basis S ℝ (MvPolynomial.restrictSupport ℝ S) :=
    MvPolynomial.basisRestrictSupport ℝ S
  let e : homogeneousSubmodule (Fin n) ℝ d ≃ₗ[ℝ] S → ℝ :=
    eSub.trans (Module.Basis.equivFun b)
  refine ⟨e, ?_⟩
  intro f m
  dsimp [e, eSub, b]
  rfl

end Commons.Algebra.MvPolynomial