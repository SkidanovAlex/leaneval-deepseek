import Mathlib
import Submission.Work.Reductions.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Reductions

/-- In a group, an element of order `2` is not contained in a subgroup of odd order. -/
theorem notMem_of_orderOf_eq_two {G : Type} [Group G] {N : Subgroup G} {x : G}
    (hx : orderOf x = 2) (hodd : Odd (Nat.card N)) : x ∉ N := fun hmem => by
  have h2 : 2 ∣ Nat.card N := by rw [← hx]; exact Subgroup.orderOf_dvd_natCard N hmem
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

/-- Two distinct commuting involutions have product of order `2`. -/
theorem orderOf_mul_eq_two_of_commute {G : Type} [Group G] {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hne : x ≠ y) (hc : x * y = y * x) :
    orderOf (x * y) = 2 := by
  have hx2 : x ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hy2 : y ^ 2 = 1 := by rw [← hy, pow_orderOf_eq_one]
  have hsq : (x * y) ^ 2 = 1 := by rw [Commute.mul_pow hc 2, hx2, hy2, one_mul]
  have hdvd : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have h1 : x * y = 1 := orderOf_eq_one_iff.mp h
    have hxy : x = y⁻¹ := (mul_eq_one_iff_eq_inv).mp h1
    have hyi : y⁻¹ = y := (mul_eq_one_iff_inv_eq).mp (show y * y = 1 from by
      rw [← pow_two]; exact hy2)
    exact hne (by rw [hxy, hyi])
  · exact h

/-- The image in `G ⧸ N` of an involution, when `N` has odd order, is again an involution. -/
theorem orderOf_mk'_eq_two {G : Type} [Group G] (N : Subgroup G) [N.Normal] {x : G}
    (hx : orderOf x = 2) (hodd : Odd (Nat.card N)) :
    orderOf (QuotientGroup.mk' N x) = 2 := by
  have hdvd : orderOf (QuotientGroup.mk' N x) ∣ 2 := by
    rw [← hx]; exact orderOf_map_dvd (QuotientGroup.mk' N) x
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have hmem : x ∈ N := by
      have hx1 : QuotientGroup.mk' N x = 1 := orderOf_eq_one_iff.mp h
      rw [QuotientGroup.mk'_apply] at hx1
      exact (QuotientGroup.eq_one_iff x).mp hx1
    have h2 : 2 ∣ Nat.card N := by rw [← hx]; exact Subgroup.orderOf_dvd_natCard N hmem
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · exact h

theorem hasFourGroup_quotient {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (hfour : Submission.Blueprint.HasFourGroup G) (hodd : Odd (Nat.card N)) :
    Submission.Blueprint.HasFourGroup (G ⧸ N) := by
  obtain ⟨a, b, ha2, hb2, hab_ne, hab_comm⟩ := hfour
  refine ⟨QuotientGroup.mk' N a, QuotientGroup.mk' N b,
    orderOf_mk'_eq_two N ha2 hodd, orderOf_mk'_eq_two N hb2 hodd, ?_, ?_⟩
  · -- the two images are distinct: otherwise `a * b ∈ N`, but `a * b` is an involution
    intro h
    have hmem : a⁻¹ * b ∈ N := QuotientGroup.eq.mp h
    have hai : a⁻¹ = a := by
      have h : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
      exact (mul_eq_one_iff_inv_eq).mp h
    rw [hai] at hmem
    exact notMem_of_orderOf_eq_two (orderOf_mul_eq_two_of_commute ha2 hb2 hab_ne hab_comm) hodd hmem
  · -- the images commute
    rw [← map_mul, ← map_mul, hab_comm]

end Work.Reductions
