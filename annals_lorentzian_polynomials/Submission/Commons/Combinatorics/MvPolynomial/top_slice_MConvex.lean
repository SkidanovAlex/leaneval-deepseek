import Mathlib
import Submission.Commons.Combinatorics.MvPolynomial.interval_convex_of_rayleigh
import Submission.Commons.LorentzianPolynomials.strict_subset_L

namespace Commons.Combinatorics.MvPolynomial

open Finsupp
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Let `T ⊆ ℕⁿ` be a down-closed set whose elements have total weight at most `d`.  If `T`
satisfies the augmentation property (every α, β ∈ T with |α| < |β| can be augmented), then
the top layer `{α ∈ T | |α| = d}` is M-convex. -/
theorem top_slice_MConvex (n d : ℕ) (T : Set (Fin n →₀ ℕ))
    (hclosed : ∀ α ∈ T, (∑ i : Fin n, α i) ≤ d)
    (hdown : ∀ α ∈ T, ∀ γ : Fin n →₀ ℕ, (∀ k : Fin n, γ k ≤ α k) → γ ∈ T)
    (haug : ∀ α ∈ T, ∀ β ∈ T, (∑ i : Fin n, α i) < (∑ i : Fin n, β i) →
      ∃ j : Fin n, α j < β j ∧ α + Finsupp.single j 1 ∈ T) :
    Commons.LorentzianPolynomials.IsMConvex {m : Fin n →₀ ℕ | m ∈ T ∧ (∑ i : Fin n, m i) = d} := by
  classical
  unfold Commons.LorentzianPolynomials.IsMConvex
  intro α hαJ β hβJ i hgt
  change (α ∈ T ∧ (∑ k : Fin n, α k) = d) at hαJ
  change (β ∈ T ∧ (∑ k : Fin n, β k) = d) at hβJ
  rcases hαJ with ⟨hαT, hαw⟩
  rcases hβJ with ⟨hβT, hβw⟩
  have hαi_ne0 : α i ≠ 0 := by
    intro hzi
    omega
  have hdegα : degN α = d := by
    rw [degN_eq_sum]
    exact hαw
  have hd_pos : 1 ≤ d := by
    have hαi_le : α i ≤ degN α := coord_le_degN α i
    have hαi_pos : 1 ≤ α i := by omega
    omega
  -- `α - eᵢ` is coordinatewise ≤ `α`, hence in `T` by downward closure.
  have hα'T : α - e i ∈ T :=
    hdown α hαT (α - e i) (sub_e_le_self α i)
  -- its total weight is `d - 1 < d = |β|`, so augmentation applies
  have hsumα' : (∑ k : Fin n, (α - e i) k) = d - 1 := by
    rw [← degN_eq_sum, degN_sub_single α i hαi_ne0, hdegα]
  have hlt : (∑ k : Fin n, (α - e i) k) < (∑ k : Fin n, β k) := by
    rw [hsumα', hβw]
    omega
  rcases haug (α - e i) hα'T β hβT hlt with ⟨j, hjlt, hmemT⟩
  -- the augmentation index `j` cannot be `i`, because `αᵢ - 1 ≥ βᵢ`
  have hji : j ≠ i := by
    intro hjeq
    subst j
    have hαi_sub : (α - e i) i = α i - 1 := by simp [e]
    rw [hαi_sub] at hjlt
    omega
  refine ⟨j, ?_, ?_⟩
  · -- `αⱼ < βⱼ`
    have hαj : (α - e i) j = α j := by
      simp [e, hji]
    rw [hαj] at hjlt
    exact hjlt
  · -- `α - eᵢ + eⱼ` lies in the top layer: it is in `T` and has weight `d`
    change (α - e i + e j) ∈ T ∧ (∑ k : Fin n, (α - e i + e j) k) = d
    constructor
    · simpa using hmemT
    · rw [← degN_eq_sum, degN_add, degN_e, degN_sub_single α i hαi_ne0, hdegα]
      omega

end Commons.Combinatorics.MvPolynomial
