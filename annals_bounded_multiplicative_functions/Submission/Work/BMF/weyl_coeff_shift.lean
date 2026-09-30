import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset Real

/-- The `l`-th Taylor coefficient of a polynomial `Q` (of `natDegree ≤ k`) at the base
point `c`, expanded as a finite binomial sum in the coefficients of `Q`. This is the
coefficient form of Taylor's formula `taylor c Q = Q(X + c)`. -/
lemma taylor_coeff_Icc (Q : ℝ[X]) (c : ℝ) (l k : ℕ) (hk : Q.natDegree ≤ k) :
    (Polynomial.taylor c Q).coeff l =
      ∑ i ∈ Finset.Icc l k, Q.coeff i * c ^ (i - l) * (i.choose l : ℝ) := by
  have key : (Polynomial.taylor c Q).coeff l =
      ∑ i ∈ Q.support, Q.coeff i * c ^ (i - l) * (i.choose l : ℝ) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply, Polynomial.sum_def,
        Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.eval_monomial]
    ring
  rw [key]
  have hsub : Q.support ⊆ Finset.range (k+1) := by
    intro i hi
    rw [Finset.mem_range]
    have := Polynomial.le_natDegree_of_mem_supp i hi
    omega
  have hzero : ∀ x ∈ Finset.range (k+1), x ∉ Q.support →
      Q.coeff x * c ^ (x - l) * (x.choose l : ℝ) = 0 := by
    intro x _ hxs
    have hc : Q.coeff x = 0 := by
      by_contra h
      exact hxs (Polynomial.mem_support_iff.mpr h)
    simp [hc]
  rw [Finset.sum_subset hsub hzero]
  symm
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
  · intro x hx hxnot
    rw [Finset.mem_range] at hx
    have hxl : x < l := by
      by_contra h
      push Not at h
      exact hxnot (by rw [Finset.mem_Icc]; omega)
    simp [Nat.choose_eq_zero_of_lt hxl]

lemma weyl_coeff_shift (R : Polynomial ℝ) (k b n₀ l : ℕ) (hk : R.natDegree ≤ k) :
    (Polynomial.taylor (n₀ : ℝ) R).coeff l =
      ∑ i ∈ Finset.Icc l k,
        (Polynomial.taylor (b : ℝ) R).coeff i *
          (((n₀ : ℝ) - (b : ℝ)) ^ (i - l)) * (i.choose l : ℝ) := by
  have hdeg : (Polynomial.taylor (b : ℝ) R).natDegree ≤ k := by
    rw [Polynomial.natDegree_taylor]; exact hk
  have ht := Polynomial.taylor_taylor R ((n₀ : ℝ) - (b : ℝ)) (b : ℝ)
  rw [show ((n₀ : ℝ) - (b : ℝ)) + (b : ℝ) = (n₀ : ℝ) by ring] at ht
  rw [← ht]
  exact taylor_coeff_Icc (Polynomial.taylor (b : ℝ) R) ((n₀ : ℝ) - (b : ℝ)) l k hdeg

end Work.BMF
