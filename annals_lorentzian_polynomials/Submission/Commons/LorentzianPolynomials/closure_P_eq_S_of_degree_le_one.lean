import Mathlib
import Submission.Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv
import Submission.Commons.Analysis.MvPolynomial.isStable_of_degree_le_one
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.Topology.Module.closure_preimage_positive_orthant

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

/-- The set of degree `d` homogeneous polynomials in `ℝ[w₁,...,wₙ]` with nonnegative
coefficients. -/
private abbrev nonnegCoeff (n d : ℕ) : Set (H n d) :=
  { f | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m }

/-- The closure of the positive orthant `P n d` is the nonnegative orthant. -/
private theorem closure_P_eq_nonneg (n d : ℕ) :
    closure (P n d) = nonnegCoeff n d := by
  classical
  -- the finite type of degree-`d` monomials
  let S : Set (Fin n →₀ ℕ) := {m | Finsupp.weight (1 : Fin n → ℕ) m = d}
  have hfinS : S.Finite := by
    dsimp [S]
    exact Finsupp.finite_of_nat_weight_eq (1 : Fin n → ℕ) (by intro x; simp) d
  haveI : Fintype S := hfinS.fintype
  -- coefficient coordinates
  rcases Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv n d with ⟨e, he⟩
  letI : AddCommGroup (H n d) := by
    dsimp [H]
    exact (homogeneousSubmodule (Fin n) ℝ d).addCommGroup
  letI : Module ℝ (H n d) := by
    dsimp [H]
    exact (homogeneousSubmodule (Fin n) ℝ d).module
  haveI : IsModuleTopology ℝ (H n d) := ⟨rfl⟩
  let eH : H n d ≃ₗ[ℝ] (S → ℝ) := e
  have heH : ∀ (f : H n d) (m : S), eH f m = f.1.coeff m.1 := by
    intro f m
    exact he f m
  have hcl := Commons.Topology.Module.closure_preimage_positive_orthant
    (E := H n d) (ι := S) (e := eH)
  have hP : P n d = { f : H n d | ∀ m : S, 0 < eH f m } := by
    ext f
    constructor
    · intro hf m
      rw [heH f m]
      exact hf m.1 m.2
    · intro hf m hm
      have h := hf ⟨m, hm⟩
      rw [heH f ⟨m, hm⟩] at h
      exact h
  rw [hP, hcl]
  ext f
  constructor
  · intro hf m
    by_cases hm : Finsupp.weight (1 : Fin n → ℕ) m = d
    · have h := hf ⟨m, hm⟩
      rwa [heH f ⟨m, hm⟩] at h
    · have hcoeff : f.1.coeff m = 0 := by
        exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero (w := 1) f.2 m hm
      exact le_of_eq hcoeff.symm
  · intro hf m
    rw [heH f m]
    exact hf m.1

/-- For degree at most one, nonnegative coefficients already imply stability. -/
private theorem nonnegCoeff_eq_S_of_degree_le_one (n d : ℕ) (hd : d ≤ 1) :
    nonnegCoeff n d = S n d := by
  ext f
  constructor
  · intro hf
    constructor
    · exact Commons.Analysis.MvPolynomial.isStable_of_degree_le_one n d hd f hf
    · exact hf
  · intro hf
    exact hf.2

theorem closure_P_eq_S_of_degree_le_one (n d : ℕ) (hd : d ≤ 1) :
    closure (P n d) = S n d := by
  rw [closure_P_eq_nonneg, nonnegCoeff_eq_S_of_degree_le_one n d hd]

end Commons.LorentzianPolynomials
