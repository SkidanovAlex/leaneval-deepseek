import Mathlib

namespace Work.BSW.S3

theorem prime_orderOf_of_centralizer_subset {G : Type} [Group G] [Finite G] {Y : Set G}
    {y : G} {a : ℕ} (hy1 : y ≠ 1) (ha : orderOf y = a)
    (hYord : ∀ z : G, z ∈ Y → orderOf z = a)
    (hC : ∀ z : G, z ∈ Subgroup.centralizer ({y} : Set G) → z ≠ 1 → z ∈ Y) :
    a.Prime := by
  have hyfin : IsOfFinOrder y := isOfFinOrder_of_finite y
  -- `a` is neither `0` (finite group) nor `1` (y ≠ 1), so it is at least `2`.
  have ha0 : a ≠ 0 := by
    rw [← ha]
    exact ne_of_gt hyfin.orderOf_pos
  have ha1 : a ≠ 1 := by
    rw [← ha]
    exact fun h => hy1 (orderOf_eq_one_iff.mp h)
  rw [Nat.prime_def_lt]
  refine ⟨by omega, ?_⟩
  -- Any proper divisor `m < a` of `a` must be `1`.
  intro m hm hmdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact ha0 (Nat.eq_zero_of_zero_dvd hmdvd)
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  -- `y ^ m` lies in the centralizer of `y`.
  have hmem : y ^ m ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.refl y).pow_left m).eq
  -- and it is nontrivial because `a ∤ m`.
  have hpne : y ^ m ≠ 1 := by
    intro h
    have hdvd : orderOf y ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [ha] at hdvd
    exact absurd (Nat.le_of_dvd hmpos hdvd) (not_le.mpr hm)
  have hYm : y ^ m ∈ Y := hC (y ^ m) hmem hpne
  -- hence `orderOf (y ^ m) = a`, while it also equals `a / m`.
  have horder : orderOf (y ^ m) = a / m := by
    rw [orderOf_pow, ha, Nat.gcd_eq_right hmdvd]
  have hdiv : a / m = a := by rw [← horder, hYord (y ^ m) hYm]
  exact (Nat.div_eq_self.mp hdiv).resolve_left ha0

end Work.BSW.S3
