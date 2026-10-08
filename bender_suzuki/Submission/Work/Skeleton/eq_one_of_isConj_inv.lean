import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- In a finite group of odd order, an element conjugate to its own inverse is the
identity.

If `g * x * g⁻¹ = x⁻¹`, then conjugating by `g` is an automorphism `σ` of `G`
that sends `x` to `x⁻¹`; in particular `σ²` fixes `x`.  Since `g` has odd order,
`σ = MulAut.conj g` has odd order, so `σ ^ orderOf g = 1`.  Writing
`orderOf g = 2 * s + 1` shows that `σ ^ orderOf g = σ * (σ²)^s`, whence
`x = σ ^ orderOf g x = σ x = x⁻¹`.  Thus `x² = 1`, and since the order of `x`
divides the odd group order, `x` has order `1`. -/
theorem eq_one_of_isConj_inv {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    {x : G} (h : IsConj x x⁻¹) : x = 1 := by
  rw [isConj_iff] at h
  obtain ⟨g, hg⟩ := h
  -- `hg : g * x * g⁻¹ = x⁻¹`
  have hσ : (MulAut.conj g) x = x⁻¹ := by
    rw [MulAut.conj_apply]; exact hg
  -- conjugation by `g` inverts `x`, so doing it twice fixes `x`
  have hσ2 : ((MulAut.conj g)^2) x = x := by
    rw [pow_two, MulAut.mul_apply, hσ, MulAut.conj_apply, ← conj_inv, hg]
    simp
  -- hence every even power of `σ` fixes `x`
  have hfix : ∀ s : ℕ, (((MulAut.conj g)^2)^s) x = x := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ', MulAut.mul_apply, ih, hσ2]
  -- the order of `g` is odd, so it is `2 * s + 1`
  obtain ⟨s, hs⟩ := hodd.of_dvd_nat (orderOf_dvd_natCard g)
  -- the automorphism `σ = conj g` has order dividing `orderOf g`
  have hσn : (MulAut.conj g) ^ (orderOf g) = 1 := by
    rw [← map_pow MulAut.conj g (orderOf g), pow_orderOf_eq_one, map_one]
  have h1 : ((MulAut.conj g) ^ (orderOf g)) x = x := by
    rw [hσn, MulAut.one_apply]
  have h2 : ((MulAut.conj g) ^ (orderOf g)) x = x⁻¹ := by
    rw [hs, pow_succ', MulAut.mul_apply, pow_mul, hfix s, hσ]
  have hx : x = x⁻¹ := h1.symm.trans h2
  -- so `x` is an involution, and an involution in an odd order group is trivial
  have hxx : x * x = 1 := mul_eq_one_iff_eq_inv.mpr hx
  have hdvd2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hxx
  have hdvdG : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have hgcd2 : orderOf x ∣ Nat.gcd 2 (Nat.card G) := Nat.dvd_gcd hdvd2 hdvdG
  have hgcd : Nat.gcd 2 (Nat.card G) = 1 := (Nat.coprime_two_left.mpr hodd).gcd_eq_one
  rw [hgcd] at hgcd2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd2)

end Work.Skeleton
