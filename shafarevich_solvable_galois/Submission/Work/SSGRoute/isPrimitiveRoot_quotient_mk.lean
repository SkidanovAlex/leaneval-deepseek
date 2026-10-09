import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- A power of a primitive `m`-th root of unity is a primitive `m / gcd m l`-th root of unity. -/
lemma pow_div_gcd {M : Type*} [CommMonoid M] {ζ : M} {m l : ℕ} (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m) : IsPrimitiveRoot (ζ ^ l) (m / Nat.gcd m l) := by
  rcases eq_or_ne l 0 with rfl | hl
  · rw [pow_zero, Nat.gcd_zero_right, Nat.div_self hm]
    exact IsPrimitiveRoot.one
  · rw [IsPrimitiveRoot.iff_orderOf, orderOf_pow' ζ hl, ← hζ.eq_orderOf]

/-- If `ξ` is a primitive `n`-th root of unity, `ξ - 1` lies in an ideal `P` whose intersection
with the image of `ℕ` is contained in `pℤ`, and `p ∤ n`, then `n = 1`. -/
lemma eq_one_of_isPrimitiveRoot_of_sub_one_mem {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) {p n : ℕ} (hdvd : ∀ k : ℕ, (k : R) ∈ P → p ∣ k) (hpn : ¬ p ∣ n)
    {ξ : R} (hξ : IsPrimitiveRoot ξ n) (hξP : ξ - 1 ∈ P) : n = 1 := by
  by_contra hn
  have hn0 : n ≠ 0 := fun h => hpn (h.symm ▸ Nat.dvd_zero p)
  have hn1 : 1 < n := by omega
  obtain ⟨u, hu⟩ := hξ.sub_one_dvd_natCast hn1
  exact hpn (hdvd n (hu.symm ▸ Ideal.mul_mem_right u P hξP))

theorem isPrimitiveRoot_quotient_mk {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R)
    {p m : ℕ} (hm : 0 < m)
    (hdvd : ∀ n : ℕ, (n : R) ∈ P → p ∣ n) (hpm : ¬ p ∣ m)
    {ζ : R} (hζ : IsPrimitiveRoot ζ m) :
    IsPrimitiveRoot (Ideal.Quotient.mk P ζ) m := by
  refine ⟨?_, ?_⟩
  · rw [← map_pow, hζ.pow_eq_one, map_one]
  · intro l hl
    have hmem : ζ ^ l - 1 ∈ P := by
      have h1 : (Ideal.Quotient.mk P) (ζ ^ l) = 1 := by
        rw [map_pow]; exact hl
      have h0 : (Ideal.Quotient.mk P) (ζ ^ l - 1) = 0 := by
        rw [map_sub, h1, map_one, sub_self]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h0
    have hξ : IsPrimitiveRoot (ζ ^ l) (m / Nat.gcd m l) := pow_div_gcd hm hζ
    have hpn : ¬ p ∣ m / Nat.gcd m l :=
      fun h => hpm (h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m l)))
    have hn1 := eq_one_of_isPrimitiveRoot_of_sub_one_mem P hdvd hpn hξ hmem
    have hg : Nat.gcd m l = m := by
      have hd : Nat.gcd m l ∣ m := Nat.gcd_dvd_left m l
      have h := Nat.mul_div_cancel' hd
      rw [hn1, mul_one] at h
      exact h
    exact hg ▸ Nat.gcd_dvd_right m l

end Work.SSGRoute
