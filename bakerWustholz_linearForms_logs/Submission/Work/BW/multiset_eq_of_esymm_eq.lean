import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- Two families of `N` complex numbers with the same elementary symmetric
functions `e_1, …, e_N` have the same multiset of values: both are the root
multiset of the monic polynomial `∏ (X - vᵢ)`, whose coefficients are, by
Vieta's formula, the elementary symmetric functions. -/
theorem multiset_eq_of_esymm_eq {N : ℕ} (z w : Fin N → ℂ)
    (h : ∀ k, k ≤ N → (Finset.univ.val.map z).esymm k = (Finset.univ.val.map w).esymm k) :
    (Finset.univ.val.map z : Multiset ℂ) = (Finset.univ.val.map w) := by
  set s : Multiset ℂ := Finset.univ.val.map z with hs
  set t : Multiset ℂ := Finset.univ.val.map w with ht
  have hscard : s.card = N := by simp [s]
  have htcard : t.card = N := by simp [t]
  have hes : ∀ k, k ≤ N → s.esymm k = t.esymm k := by
    intro k hk
    rw [hs, ht]; exact h k hk
  have hpoly : (s.map (fun a => (X - C a : ℂ[X]))).prod
      = (t.map (fun a => (X - C a : ℂ[X]))).prod := by
    apply Polynomial.ext
    intro k
    rcases lt_or_ge N k with hk | hk
    · rw [coeff_eq_zero_of_natDegree_lt
          (by rw [natDegree_multiset_prod_X_sub_C_eq_card, hscard]; exact hk),
        coeff_eq_zero_of_natDegree_lt
          (by rw [natDegree_multiset_prod_X_sub_C_eq_card, htcard]; exact hk)]
    · have hks : k ≤ Multiset.card s := by rw [hscard]; exact hk
      have hkt : k ≤ Multiset.card t := by rw [htcard]; exact hk
      rw [Multiset.prod_X_sub_C_coeff s hks, Multiset.prod_X_sub_C_coeff t hkt]
      rw [hscard, htcard, hes (N - k) (Nat.sub_le N k)]
  calc s = (s.map (fun a => (X - C a : ℂ[X]))).prod.roots :=
        (roots_multiset_prod_X_sub_C s).symm
    _ = (t.map (fun a => (X - C a : ℂ[X]))).prod.roots := by rw [hpoly]
    _ = t := roots_multiset_prod_X_sub_C t

end Work.BW
