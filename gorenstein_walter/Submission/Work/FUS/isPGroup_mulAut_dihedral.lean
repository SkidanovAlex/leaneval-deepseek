/-
# `Aut(D_{2^j})` is a 2-group

`DihedralGroup (2^j)` (`j ≥ 2`) is the dihedral group of order `2^(j+1)`.  Its automorphism
group is `Hol(Z/2^j)`, of order `2^j · 2^(j-1) = 2^(2j-1)`, which is a 2-group.

Rather than computing the order of `Aut(D_{2^j})` we use the (already available) fact
`Work.FUS.AutFacts.mulAut_dihedral_eq_one_of_odd`: every automorphism of odd order is trivial.
An element `β` of a finite group whose order has an odd part `m' > 1` would have
`β ^ (2-part of orderOf β)` of odd order `m'`, hence trivial; but that forces `m' = 1`.  So the
order of every `β` is a power of `2`, which is exactly `IsPGroup 2 (D ≃* D)`.
-/
import Mathlib
import Submission.Work.FUS.AutFacts.mulAut_dihedral_eq_one_of_odd

namespace Work.FUS

/-- Every automorphism of `DihedralGroup (2^j)`, `j ≥ 2`, has order a power of two. -/
lemma mulAut_dihedral_orderOf_eq_two_pow (j : ℕ) (hj : 2 ≤ j)
    (β : DihedralGroup (2 ^ j) ≃* DihedralGroup (2 ^ j)) :
    ∃ k : ℕ, orderOf β = 2 ^ k := by
  -- `β` lives in a finite group, so its order is nonzero.
  have hm0 : orderOf β ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite β)
  -- Split `orderOf β = e * m'` with `e = 2 ^ (orderOf β).factorization 2` the exact power of two
  -- dividing it and `m' = orderOf β / e` odd.
  have hmult : 2 ^ (orderOf β).factorization 2 *
      (orderOf β / 2 ^ (orderOf β).factorization 2) = orderOf β :=
    Nat.ordProj_mul_ordCompl_eq_self (orderOf β) 2
  -- `γ = β ^ e` then satisfies `γ ^ m' = 1`.
  have hγm' : (β ^ 2 ^ (orderOf β).factorization 2) ^
      (orderOf β / 2 ^ (orderOf β).factorization 2) = 1 := by
    rw [← pow_mul, hmult, pow_orderOf_eq_one]
  -- Hence `orderOf γ ∣ m'`, and `m'` is odd, so `orderOf γ` is odd.
  have hγodd : Odd (orderOf (β ^ 2 ^ (orderOf β).factorization 2)) := by
    have hdvd : orderOf (β ^ 2 ^ (orderOf β).factorization 2) ∣
        orderOf β / 2 ^ (orderOf β).factorization 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr hγm'
    have hnodd : Odd (orderOf β / 2 ^ (orderOf β).factorization 2) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact Nat.not_dvd_ordCompl Nat.prime_two hm0
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd] at hnodd ⊢
    intro h2
    exact hnodd (h2.trans hdvd)
  -- An automorphism of odd order is trivial (`Work.FUS.AutFacts`), so `β ^ e = 1`.
  have hγ1 : β ^ 2 ^ (orderOf β).factorization 2 = 1 :=
    AutFacts.mulAut_dihedral_eq_one_of_odd j hj _ hγodd
  -- Therefore `orderOf β ∣ e`, and `e ∣ orderOf β` by construction: `orderOf β` is the power of
  -- two `e`.
  have hdvd : orderOf β ∣ 2 ^ (orderOf β).factorization 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr hγ1
  exact ⟨(orderOf β).factorization 2,
    Nat.dvd_antisymm hdvd (Nat.ordProj_dvd (orderOf β) 2)⟩

/-- The automorphism group of the dihedral 2-group `DihedralGroup (2^j)` (`j ≥ 2`) is a 2-group. -/
theorem isPGroup_mulAut_dihedral (j : ℕ) (hj : 2 ≤ j) :
    IsPGroup 2 (DihedralGroup (2 ^ j) ≃* DihedralGroup (2 ^ j)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro β
  obtain ⟨k, hk⟩ := mulAut_dihedral_orderOf_eq_two_pow j hj β
  exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one β⟩

end Work.FUS
