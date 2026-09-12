import Mathlib

open Finsupp Matrix MvPolynomial UpperHalfPlane

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

private def H (n d : ℕ) : Type := homogeneousSubmodule (Fin n) ℝ d

private def IsMConvex {n : ℕ} (J : Set (Fin n →₀ ℕ)) : Prop :=
  ∀ α ∈ J, ∀ β ∈ J, ∀ i, α i > β i → ∃ j, α j < β j ∧ α - single i 1 + single j 1 ∈ J

private abbrev P (n d : ℕ) : Set (H n d) :=
  { f | ∀ m : Fin n →₀ ℕ, weight 1 m = d → 0 < f.1.coeff m }

private abbrev M (n d : ℕ) : Set (H n d) :=
  { f | IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) ∧ ∀ m, 0 ≤ f.1.coeff m }

private lemma weight_one_eq_sum {n : ℕ} (m : Fin n →₀ ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) m = ∑ i : Fin n, m i := by
  have h := Finsupp.weight_eq_sum (w := (1 : Fin n → ℕ)) (f := m)
  simpa using h

private lemma exists_lt_of_weight_eq_of_lt {n : ℕ} {α β : Fin n →₀ ℕ}
    (h : Finsupp.weight (1 : Fin n → ℕ) α = Finsupp.weight (1 : Fin n → ℕ) β)
    {i : Fin n} (hi : α i > β i) : ∃ j : Fin n, α j < β j := by
  by_contra hnot
  have hle : ∀ j : Fin n, β j ≤ α j := by
    intro j
    have hnotj : ¬ α j < β j := by
      intro hj
      exact hnot ⟨j, hj⟩
    exact not_lt.mp hnotj
  have hlt_sum : (∑ j : Fin n, β j) < (∑ j : Fin n, α j) := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro j hj
      exact hle j
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      exact hi
  have hsum_alpha : Finsupp.weight (1 : Fin n → ℕ) α = ∑ j : Fin n, α j := by
    simpa using (Finsupp.weight_eq_sum (w := (1 : Fin n → ℕ)) (f := α))
  have hsum_beta : Finsupp.weight (1 : Fin n → ℕ) β = ∑ j : Fin n, β j := by
    simpa using (Finsupp.weight_eq_sum (w := (1 : Fin n → ℕ)) (f := β))
  rw [hsum_alpha, hsum_beta] at h
  exact (not_lt_of_ge (le_of_eq h)) hlt_sum

private lemma weight_sub_single_add_single_eq {n : ℕ} {α : Fin n →₀ ℕ}
    {i j : Fin n} (hi : α i ≠ 0) :
    Finsupp.weight (1 : Fin n → ℕ) (α - Finsupp.single i 1 + Finsupp.single j 1) =
      Finsupp.weight (1 : Fin n → ℕ) α := by
  have hsub := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ)) (f := α) (i := i) hi
  rw [map_add]
  rw [Finsupp.weight_single]
  simpa using hsub

theorem P_subset_M (n d : ℕ) : P n d ⊆ M n d := by
  intro f hf
  constructor
  · intro α hα β hβ i hi
    have hcoeff_ne_α : f.1.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    have hcoeff_ne_β : f.1.coeff β ≠ 0 := MvPolynomial.mem_support_iff.mp hβ
    have hαdeg : Finsupp.weight (1 : Fin n → ℕ) α = d := f.2 hcoeff_ne_α
    have hβdeg : Finsupp.weight (1 : Fin n → ℕ) β = d := f.2 hcoeff_ne_β
    have hweight_eq : Finsupp.weight (1 : Fin n → ℕ) α =
        Finsupp.weight (1 : Fin n → ℕ) β := by
      rw [hαdeg, hβdeg]
    rcases exists_lt_of_weight_eq_of_lt hweight_eq hi with ⟨j, hj⟩
    refine ⟨j, hj, ?_⟩
    have hαi_ne : α i ≠ 0 := by
      exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le (β i)) hi)
    have hshift_weight : Finsupp.weight (1 : Fin n → ℕ)
        (α - Finsupp.single i 1 + Finsupp.single j 1) = d := by
      rw [weight_sub_single_add_single_eq hαi_ne]
      exact hαdeg
    have hpos : 0 < f.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) :=
      hf (α - Finsupp.single i 1 + Finsupp.single j 1) hshift_weight
    exact MvPolynomial.mem_support_iff.mpr (ne_of_gt hpos)
  · intro m
    by_cases hm : Finsupp.weight (1 : Fin n → ℕ) m = d
    · exact le_of_lt (hf m hm)
    · have hcoeff_zero : f.1.coeff m = 0 :=
        MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero f.2 m hm
      exact le_of_eq hcoeff_zero.symm

end Commons.LorentzianPolynomials
