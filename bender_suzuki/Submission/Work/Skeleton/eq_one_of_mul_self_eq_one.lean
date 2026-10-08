import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- In a finite group of odd order the only element of order dividing two is the
identity: an involution has order `2`, which would divide the (odd) group order. -/
theorem eq_one_of_mul_self_eq_one {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    {x : G} (h : x * x = 1) : x = 1 := by
  -- `x^2 = 1`, hence the order of `x` divides `2`
  have h2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact h
  -- and the order of `x` divides the group order
  have hc : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  -- so it divides their gcd, which is `1` because the group order is odd
  have hg : orderOf x ∣ Nat.gcd 2 (Nat.card G) := Nat.dvd_gcd h2 hc
  have hgcd : Nat.gcd 2 (Nat.card G) = 1 :=
    (Nat.coprime_two_left.mpr hodd).gcd_eq_one
  rw [hgcd] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

end Work.Skeleton
