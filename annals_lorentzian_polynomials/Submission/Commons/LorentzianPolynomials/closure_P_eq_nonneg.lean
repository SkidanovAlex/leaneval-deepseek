import Mathlib
import Submission.Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv
import Submission.Commons.Topology.Module.closure_preimage_positive_orthant
import Submission.Commons.LorentzianPolynomials.S_closed

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

theorem closure_P_eq_nonneg (n d : ℕ) :
    closure (P n d) = {f : H n d | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m} := by
  classical
  change closure (P n d) =
      {f : homogeneousSubmodule (Fin n) ℝ d | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m}
  let E := homogeneousSubmodule (Fin n) ℝ d
  letI : TopologicalSpace E := moduleTopology ℝ E
  letI : IsModuleTopology ℝ E := ⟨rfl⟩
  let ι : Type := {m : Fin n →₀ ℕ // weight 1 m = d}
  haveI : Fintype ι := by
    dsimp [ι]
    let S : Set (Fin n →₀ ℕ) := {m | weight 1 m = d}
    have hfin : S.Finite := by
      apply Set.Finite.subset (Finsupp.finite_of_nat_weight_le (w := 1) (n := d) ?_)
      · intro m hm
        exact le_of_eq hm
      · intro x
        exact Nat.one_ne_zero
    exact hfin.fintype
  let e : E ≃ₗ[ℝ] (ι → ℝ) :=
    Classical.choose (Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv n d)
  have he : ∀ (f : E) (m : ι), e f m = f.1.coeff m.1 := by
    intro f m
    have h := Classical.choose_spec (Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv n d)
    simpa [e, ι, E] using (h f m)
  have hcl := Commons.Topology.Module.closure_preimage_positive_orthant (e := e)
  have hP : P n d = {f : E | ∀ m : ι, 0 < e f m} := by
    ext f
    constructor
    · intro hf m
      dsimp [P] at hf
      have hcoeff : 0 < f.1.coeff m.1 := hf m.1 m.2
      rw [he f m]
      exact hcoeff
    · intro hf m hm
      have h := hf ⟨m, hm⟩
      rw [he f ⟨m, hm⟩] at h
      exact h
  have hmain : closure (P n d) = {f : E | ∀ m : ι, 0 ≤ e f m} := by
    rw [hP]
    exact hcl
  ext f
  rw [hmain]
  constructor
  · intro hf m
    by_cases hm : weight 1 m = d
    · have h := hf ⟨m, hm⟩
      rw [he f ⟨m, hm⟩] at h
      exact h
    · have hcoeff : f.1.coeff m = 0 := by
        have hd : Finsupp.weight (1 : Fin n → ℕ) m ≠ d := by simpa using hm
        exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero (w := 1) f.2 m hd
      exact le_of_eq hcoeff.symm
  · intro hf m
    have h : 0 ≤ f.1.coeff m.1 := hf m.1
    rw [he f m]
    exact h

end Commons.LorentzianPolynomials
