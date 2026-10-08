import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- For a finite group `H` with normal subgroup `N` and prime `p` dividing `N.index`, there is
`y ∉ N` whose order is a power of `p`.

Route: Cauchy in `H ⧸ N` (`p ∣ Nat.card (H ⧸ N)` since `N.index = Nat.card (H ⧸ N)`) gives
`x : H ⧸ N` of order `p`; lift it to `a : H` along the surjective `QuotientGroup.mk' N`.  Write
`orderOf a = p ^ e * m` with `p ∤ m` (`Nat.exists_eq_pow_mul_and_not_dvd`, `orderOf a ≠ 0` since `H`
is finite) and put `y = a ^ m`.  Then `y ^ (p ^ e) = a ^ (orderOf a) = 1`, so `orderOf y ∣ p ^ e`
and hence `orderOf y = p ^ k` for some `k` (`Nat.dvd_prime_pow`); and `y ∉ N` because the image of
`y` in `H ⧸ N` is `x ^ m ≠ 1` (`x ^ m = 1 ↔ p ∣ m`), via `QuotientGroup.eq_one_iff` /
`QuotientGroup.ker_mk'`.  (Note: the naive "`y` has order exactly `p`" is false, e.g. `H = ZMod 6`,
`N = {0,2,4}`, `p = 2`, `y = 3`; only the `∃ k, orderOf y = p ^ k` form is claimed.) -/
theorem exists_ppow_notMem_of_dvd_index {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal] {p : ℕ} (hp : p.Prime) (hdiv : p ∣ N.index) : ∃ y : H, y ∉ N ∧ ∃ k : ℕ, orderOf y = p ^ k := by
  -- `N.index` is the cardinality of the quotient `H ⧸ N`, so Cauchy applies there.
  rw [Subgroup.index_eq_card] at hdiv
  -- Cauchy's theorem in `H ⧸ N`: an element `x` of order exactly `p`.
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ N) p hdiv (hp := ⟨hp⟩)
  -- Lift `x` to `a : H` along the surjective quotient map.
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  -- Decompose `orderOf a = p ^ e * m` with `p ∤ m` (`orderOf a ≠ 0` as `H` is finite).
  have ha0 : orderOf a ≠ 0 := (orderOf_pos a).ne'
  obtain ⟨e, m, hmp, ham⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.ne_one
  refine ⟨a ^ m, ?_, ?_⟩
  · -- `a ^ m ∉ N`: its image `x ^ m` in the quotient is nontrivial since `p ∤ m`.
    intro hmem
    have h1 : (QuotientGroup.mk' N) (a ^ m) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_pow] at h1
    have hd : p ∣ m := by
      have := (orderOf_dvd_iff_pow_eq_one).mpr h1
      rwa [hx] at this
    exact hmp hd
  · -- `(a ^ m) ^ (p ^ e) = a ^ (orderOf a) = 1`, hence `orderOf (a ^ m) ∣ p ^ e`.
    have hpow : (a ^ m) ^ (p ^ e) = 1 := by
      rw [← pow_mul, mul_comm, ← ham, pow_orderOf_eq_one]
    have hdvd : orderOf (a ^ m) ∣ p ^ e := (orderOf_dvd_iff_pow_eq_one).mpr hpow
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact ⟨k, hk⟩

end Work.NormalComplement
