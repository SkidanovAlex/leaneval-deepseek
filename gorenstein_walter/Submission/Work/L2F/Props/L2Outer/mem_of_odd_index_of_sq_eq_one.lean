import Mathlib

namespace Work.L2F.Props.L2Outer

/-- If `H` is a normal subgroup of odd index and `x ^ 2 = 1`, then `x ∈ H`.

In the quotient `G ⧸ H` (a group of odd order) the image of `x` satisfies `x̄ ^ 2 = 1`, so
its order divides `2`; being a divisor of the odd number `H.index = Nat.card (G ⧸ H)` the
order is also odd, hence equal to `1`. Thus `x̄ = 1`, i.e. `x ∈ H`. -/
theorem mem_of_odd_index_of_sq_eq_one {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    [H.Normal] (h : Odd H.index) {x : G} (hx : x ^ 2 = 1) : x ∈ H := by
  -- It suffices to show that the image of `x` in the quotient `G ⧸ H` is trivial.
  have hmem : x ∈ H ↔ QuotientGroup.mk' H x = 1 := by
    have h1 := MonoidHom.mem_ker (f := QuotientGroup.mk' H) (x := x)
    rw [QuotientGroup.ker_mk' H] at h1
    exact h1
  rw [hmem]
  -- `x̄ ^ 2 = 1` in the quotient.
  have hpow : (QuotientGroup.mk' H x) ^ 2 = 1 := by
    rw [← map_pow (QuotientGroup.mk' H) x 2, hx, map_one]
  -- Hence `orderOf x̄` divides `2`.
  have hdvd : orderOf (QuotientGroup.mk' H x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  -- And it divides the odd number `H.index = Nat.card (G ⧸ H)`, so it is odd.
  have hodd : Odd (orderOf (QuotientGroup.mk' H x)) := by
    apply Odd.of_dvd_nat _ (orderOf_dvd_natCard _)
    rw [← Subgroup.index_eq_card H]
    exact h
  -- An odd divisor of `2` must be `1`.
  have h1 : orderOf (QuotientGroup.mk' H x) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have hle : orderOf (QuotientGroup.mk' H x) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact orderOf_eq_one_iff.mp h1

end Work.L2F.Props.L2Outer
