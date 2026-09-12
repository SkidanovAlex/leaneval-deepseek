import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.Combinatorics.MvPolynomial.union_shift_mconvex

open Finsupp MvPolynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

open Commons.Combinatorics.MvPolynomial

/-- Coordinate contraction of an M-convex set is M-convex: if `A` satisfies the
exchange property then so does `{m | m + eᵢ ∈ A}`. -/
lemma contraction_mconvex {n : ℕ} (i : Fin n) (A : Set (Fin n →₀ ℕ))
    (hA : IsMConvex A) : IsMConvex {m : Fin n →₀ ℕ | m + e i ∈ A} := by
  classical
  unfold IsMConvex
  intro α hα β hβ k hgt
  have hαA : α + e i ∈ A := by simpa using hα
  have hβA : β + e i ∈ A := by simpa using hβ
  by_cases hki : k = i
  · -- exchange at coordinate k = i
    subst k
    have hgtA : (α + e i) i > (β + e i) i := by
      simp [e, Finsupp.add_apply]
      omega
    rcases hA (α + e i) hαA (β + e i) hβA i hgtA with ⟨j, hltA, hmemA⟩
    have hji : j ≠ i := by
      intro hj
      subst j
      simp [e, Finsupp.add_apply] at hltA
      omega
    refine ⟨j, ?_, ?_⟩
    · have hltj : (α + e i) j < (β + e i) j := hltA
      have hαj : (α + e i) j = α j := by simp [e, Finsupp.add_apply, hji]
      have hβj : (β + e i) j = β j := by simp [e, Finsupp.add_apply, hji]
      rwa [hαj, hβj] at hltj
    · change (α - e i + e j) + e i ∈ A
      have hαi1 : 1 ≤ α i := by
        simp [e, Finsupp.add_apply] at hgt
        omega
      have hγeq : (α - e i + e j) + e i = (α + e i) - e i + e j := by
        calc
          ((α - e i) + e j) + e i = (α - e i) + (e j + e i) := by rw [add_assoc]
          _ = (α - e i) + (e i + e j) := by rw [add_comm (e j) (e i)]
          _ = ((α - e i) + e i) + e j := by rw [← add_assoc]
          _ = α + e j := by rw [sub_single_add_self α i hαi1]
          _ = (α + e i) - e i + e j := by rw [add_sub_single α i]
      rwa [hγeq]
  · -- exchange at coordinate k ≠ i
    have hgtA : (α + e i) k > (β + e i) k := by
      have hαk : (α + e i) k = α k := by simp [e, Finsupp.add_apply, hki]
      have hβk : (β + e i) k = β k := by simp [e, Finsupp.add_apply, hki]
      rwa [hαk, hβk]
    rcases hA (α + e i) hαA (β + e i) hβA k hgtA with ⟨j, hltA, hmemA⟩
    refine ⟨j, ?_, ?_⟩
    · have hltj : (α + e i) j < (β + e i) j := hltA
      by_cases hji : j = i
      · subst j
        have h1 : (α + e i) i = α i + 1 := by simp [e, Finsupp.add_apply]
        have h2 : (β + e i) i = β i + 1 := by simp [e, Finsupp.add_apply]
        rw [h1, h2] at hltj
        omega
      · have hαj : (α + e i) j = α j := by simp [e, Finsupp.add_apply, hji]
        have hβj : (β + e i) j = β j := by simp [e, Finsupp.add_apply, hji]
        rwa [hαj, hβj] at hltj
    · change (α - e k + e j) + e i ∈ A
      have hγeq : (α - e k + e j) + e i = (α + e i) - e k + e j := by
        calc
          ((α - e k) + e j) + e i = (α - e k) + (e j + e i) := by rw [add_assoc]
          _ = (α - e k) + (e i + e j) := by rw [add_comm (e j) (e i)]
          _ = ((α - e k) + e i) + e j := by rw [← add_assoc]
          _ = ((α + e i) - e k) + e j := by rw [← add_sub_swap α i k (Ne.symm hki)]
          _ = (α + e i) - e k + e j := rfl
      rwa [hγeq]

/-- The support of a partial derivative of a homogeneous polynomial with M-convex
support is again M-convex (coordinate contraction of an M-convex set). -/
theorem deriv_support_MConvex (n d : ℕ) (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous d)
    (hM : Commons.LorentzianPolynomials.IsMConvex (p.support : Set (Fin n →₀ ℕ))) :
    Commons.LorentzianPolynomials.IsMConvex
      (((MvPolynomial.pderiv i p).support) : Set (Fin n →₀ ℕ)) := by
  have hsupp : ((pderiv i p).support : Set (Fin n →₀ ℕ)) =
      {m : Fin n →₀ ℕ | m + e i ∈ (p.support : Set (Fin n →₀ ℕ))} := by
    ext m
    simp only [Finset.mem_coe]
    exact mem_support_pderiv i p m
  rw [hsupp]
  exact contraction_mconvex i (p.support : Set (Fin n →₀ ℕ)) hM

end Commons.LorentzianPolynomials
