import Mathlib
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.stronglyEmbedded_index_odd
import Submission.Work.Reductions.stronglyEmbedded_normalizer_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Reductions

/-!
# `stronglyEmbedded_exists_conj_mem`

Every involution of a finite group lies in a conjugate of a strongly embedded subgroup.

The argument is Bender's elementary one (Peterfalvi I §1 (3) and §2 Prop. 1 (a)).  Let `H` be
strongly embedded and `u ∈ H` an involution (Cauchy, using `Even |H|`).  For an involution `t`:

* if `x ∈ H` is an involution and `z` commutes with `x`, then `z ∈ H`: otherwise
  `⟨x⟩ ≤ H ⊓ H^z` is a nontrivial 2-subgroup of a group of odd order;
* hence, if `u t` had even order `2j`, the central involution `(ut)^j` of the dihedral group
  `⟨u,t⟩` would commute with `u` and with `t`, forcing first `(ut)^j ∈ H` and then `t ∈ H` — so
  `m = orderOf (u t)` is odd;
* for `m = 2k+1` one checks by a direct computation in the dihedral group that
  `g = (ut)^k u` conjugates `u` to `t`, so `t ∈ H^g`.
-/

/-- A strongly embedded subgroup of even order contains an involution (Cauchy). -/
private theorem exists_involution_mem {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) : ∃ x ∈ H, orderOf x = 2 := by
  obtain ⟨-, heven, -⟩ := hH
  have h2 : 2 ∣ Nat.card ↥H := even_iff_two_dvd.mp heven
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' : 2 ∣ Fintype.card ↥H := by
    rw [Fintype.card_eq_nat_card]; exact h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥H) 2 h2'
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

/-- If `X ≤ H` has even order and `z` centralises `X`, then `z ∈ H`.  Otherwise
`X ≤ H ⊓ H^z` is a subgroup of even order in the intersection of two distinct conjugates, which
the strong embedding of `H` forbids. -/
private theorem mem_of_le_centralizer {G : Type} [Group G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X : Subgroup G} (hXH : X ≤ H)
    (hXeven : Even (Nat.card X)) {z : G}
    (hZ : X ≤ Subgroup.centralizer ({z} : Set G)) : z ∈ H := by
  obtain ⟨-, -, hodd⟩ := hH
  by_contra hzH
  have hXK : X ≤ H ⊓ Submission.Blueprint.conj z H := by
    intro x hx
    have hzx : z * x = x * z := (Subgroup.mem_centralizer_singleton_iff.mp (hZ hx)).symm
    refine ⟨hXH hx, ?_⟩
    change x ∈ H.map (MulAut.conj z).toMonoidHom
    rw [Subgroup.mem_map]
    refine ⟨x, hXH hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hzx]
    group
  have hdvd : Nat.card X ∣ Nat.card (H ⊓ Submission.Blueprint.conj z H : Subgroup G) :=
    Subgroup.card_dvd_of_le hXK
  have hEven : Even (Nat.card (H ⊓ Submission.Blueprint.conj z H : Subgroup G)) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hXeven).trans hdvd)
  exact (Nat.not_even_iff_odd.mpr (hodd z hzH)) hEven

/-- If `a ∈ H` is an involution and `w` commutes with `a`, then `w ∈ H`. -/
private theorem mem_of_commute {G : Type} [Group G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {a w : G} (haH : a ∈ H)
    (ha : orderOf a = 2) (hcomm : a * w = w * a) : w ∈ H := by
  refine mem_of_le_centralizer hH (X := Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haH)
    ?_ (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcomm))
  rw [Nat.card_zpowers, ha]
  exact ⟨1, rfl⟩

/-- If the involution `u` inverts `c` then it inverts every power of `c`. -/
private theorem mul_pow_mul_eq_inv_pow {G : Type} [Group G] {u c : G} (hu : u * u = 1)
    (hc : u * c * u = c⁻¹) (n : ℕ) : u * c ^ n * u = (c ^ n)⁻¹ := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hconj : (MulAut.conj u) c = c⁻¹ := by
    rw [MulAut.conj_apply, hu']; exact hc
  have h2 : (MulAut.conj u) (c ^ n) = (c ^ n)⁻¹ := by
    rw [map_pow, hconj, inv_pow]
  simpa [MulAut.conj_apply, hu'] using h2

/-- **Dihedral computation.**  If `u`, `t` are involutions and `u * t` has odd order `2k+1`, then
`(u t)^k u` conjugates `u` to `t`. -/
private theorem dihedral_conj {G : Type} [Group G] {u t : G} (hu : u * u = 1) (ht : t * t = 1)
    {k : ℕ} (hk : orderOf (u * t) = 2 * k + 1) :
    ((u * t) ^ k * u) * u * ((u * t) ^ k * u)⁻¹ = t := by
  let c : G := u * t
  have hk' : orderOf c = 2 * k + 1 := hk
  have hcu : u * c * u = c⁻¹ := by
    change u * (u * t) * u = (u * t)⁻¹
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right hu]
    calc u * (u * t) * u = (u * u) * (t * u) := by group
      _ = t * u := by rw [hu, one_mul]
  have h1 : u * c ^ k * u = (c ^ k)⁻¹ := mul_pow_mul_eq_inv_pow hu hcu k
  have h3 : c ^ k * u = u * (c ^ k)⁻¹ := by
    have key : u * (u * c ^ k * u) = c ^ k * u := by
      calc u * (u * c ^ k * u) = (u * u) * (c ^ k * u) := by group
        _ = c ^ k * u := by rw [hu, one_mul]
    rw [h1] at key
    exact key.symm
  have h5 : c ^ (2 * k) * c = 1 := by
    rw [← pow_succ, ← hk']
    exact pow_orderOf_eq_one c
  have h4 : c ^ (2 * k) = c⁻¹ := eq_inv_of_mul_eq_one_left h5
  have hR : (c ^ k * u)⁻¹ = u * (c ^ k)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu]
  rw [hR]
  calc (c ^ k * u) * u * (u * (c ^ k)⁻¹)
      = c ^ k * (u * u * u) * (c ^ k)⁻¹ := by group
    _ = c ^ k * u * (c ^ k)⁻¹ := by
        have huu : u * u * u = u := by rw [hu, one_mul]
        rw [huu]
    _ = c ^ k * (u * (c ^ k)⁻¹) := by rw [mul_assoc]
    _ = c ^ k * (c ^ k * u) := by rw [← h3]
    _ = c ^ k * c ^ k * u := by rw [mul_assoc]
    _ = c ^ (2 * k) * u := by rw [← pow_add, two_mul]
    _ = c⁻¹ * u := by rw [h4]
    _ = t := by
        change (u * t)⁻¹ * u = t
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right hu,
          mul_assoc, hu, mul_one]

theorem stronglyEmbedded_exists_conj_mem {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, t ∈ Submission.Blueprint.conj g H := by
  obtain ⟨u, huH, hu2⟩ := exists_involution_mem hH
  by_cases htH : t ∈ H
  · refine ⟨1, ?_⟩
    rw [Subgroup.mem_map]
    refine ⟨t, htH, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · let c : G := u * t
    have hu2' : u * u = 1 := by
      have h := pow_orderOf_eq_one u
      rw [hu2, pow_two] at h
      exact h
    have ht2' : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rw [ht, pow_two] at h
      exact h
    have hcu : u * c * u = c⁻¹ := by
      change u * (u * t) * u = (u * t)⁻¹
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2', inv_eq_of_mul_eq_one_right hu2']
      calc u * (u * t) * u = (u * u) * (t * u) := by group
        _ = t * u := by rw [hu2', one_mul]
    have hct : t * c * t = c⁻¹ := by
      change t * (u * t) * t = (u * t)⁻¹
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2', inv_eq_of_mul_eq_one_right hu2']
      calc t * (u * t) * t = (t * u) * (t * t) := by group
        _ = t * u := by rw [ht2', mul_one]
    have hcodd : Odd (orderOf c) := by
      rcases Nat.even_or_odd (orderOf c) with hE | hO
      · exfalso
        obtain ⟨j, hj⟩ := hE
        have hjpos : 0 < j := by
          rcases Nat.eq_zero_or_pos j with h | h
          · rw [h, add_zero] at hj
            exact absurd hj (orderOf_pos c).ne'
          · exact h
        let z : G := c ^ j
        have hz2 : z * z = 1 := by
          change c ^ j * c ^ j = 1
          rw [← pow_two, ← pow_mul]
          have hjm : j * 2 = j + j := by ring
          rw [hjm, ← hj]
          exact pow_orderOf_eq_one c
        have hzne : z ≠ 1 := by
          intro hz1
          have hcj : c ^ j = 1 := hz1
          have hdvd : orderOf c ∣ j := orderOf_dvd_iff_pow_eq_one.mpr hcj
          have hlt : j < orderOf c := by rw [hj]; omega
          have hle := Nat.le_of_dvd hjpos hdvd
          omega
        have hzord : orderOf z = 2 := by
          have hzsq : z ^ 2 = 1 := by rw [pow_two]; exact hz2
          have hdvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hzsq
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
          · exact absurd h (fun h1 => hzne (orderOf_eq_one_iff.mp h1))
          · exact h
        have hzu : u * z * u = z := by
          have h1 : u * c ^ j * u = (c ^ j)⁻¹ := mul_pow_mul_eq_inv_pow hu2' hcu j
          change u * c ^ j * u = c ^ j
          rw [h1, inv_eq_of_mul_eq_one_right hz2]
        have hzu' : u * z = z * u := by
          have h1 : (u * z) * u = (z * u) * u := by
            rw [hzu, mul_assoc, hu2', mul_one]
          exact mul_right_cancel h1
        have hzt : t * z * t = z := by
          have h1 : t * c ^ j * t = (c ^ j)⁻¹ := mul_pow_mul_eq_inv_pow ht2' hct j
          change t * c ^ j * t = c ^ j
          rw [h1, inv_eq_of_mul_eq_one_right hz2]
        have hzt' : z * t = t * z := by
          have h1 : (t * z) * t = (z * t) * t := by
            rw [hzt, mul_assoc, ht2', mul_one]
          exact (mul_right_cancel h1).symm
        have hzH : z ∈ H := mem_of_commute hH huH hu2 hzu'
        exact htH (mem_of_commute hH hzH hzord hzt')
      · exact hO
    obtain ⟨k, hk⟩ := hcodd
    refine ⟨c ^ k * u, ?_⟩
    rw [Subgroup.mem_map]
    refine ⟨u, huH, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact dihedral_conj hu2' ht2' hk

end Work.Reductions
