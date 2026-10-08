import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.DoubleTransitivity.Sec5

/-- If `D` has odd order and `u` is an involution normalizing `D`, then for any two
`D`-conjugates `a = d₁⁻¹ u d₁`, `b = d₂⁻¹ u d₂` of `u`, the product `a * b` lies in `D`
and hence has odd order; so `orderOf (a * b) = 2` is impossible. -/
theorem no_involution_in_normalizer_of_odd {G : Type} [Group G] {D : Subgroup G} {u : G}
    (hodd : Odd (Nat.card ↥D))
    (hu : orderOf u = 2)
    (hnorm : u ∈ Subgroup.normalizer (D : Set G))
    {a b : G} (ha : ∃ d ∈ D, d⁻¹ * u * d = a) (hb : ∃ d ∈ D, d⁻¹ * u * d = b)
    (hab : orderOf (a * b) = 2) : False := by
  obtain ⟨d1, hd1D, hd1⟩ := ha
  obtain ⟨d2, hd2D, hd2⟩ := hb
  -- `u ^ 2 = 1`, hence `u⁻¹ = u`.
  have hu2 : u * u = 1 := by
    rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  -- `u` normalizes `D`: conjugation by `u` preserves `D`.
  have hconj : ∀ h ∈ D, u * h * u⁻¹ ∈ D :=
    fun h hh => (Subgroup.mem_normalizer_iff.mp hnorm h).mp hh
  have hw : u * (d1 * d2⁻¹) * u⁻¹ ∈ D :=
    hconj (d1 * d2⁻¹) (mul_mem hd1D (inv_mem hd2D))
  -- `a * b ∈ D`.
  have hab_mem : a * b ∈ D := by
    rw [← hd1, ← hd2]
    have key : (d1⁻¹ * u * d1) * (d2⁻¹ * u * d2)
        = d1⁻¹ * (u * (d1 * d2⁻¹) * u⁻¹) * d2 := by
      rw [hu_inv]; group
    rw [key]
    exact mul_mem (mul_mem (inv_mem hd1D) hw) hd2D
  -- Membership in `D` forces the order of `a * b` to divide `Nat.card D`, which is odd.
  have hob : orderOf (a * b) ∣ Nat.card ↥D := by
    have h := orderOf_dvd_natCard (G := ↥D) ⟨a * b, hab_mem⟩
    rwa [Subgroup.orderOf_mk] at h
  have hodd_ab : Odd (orderOf (a * b)) := Odd.of_dvd_nat hodd hob
  rw [hab] at hodd_ab
  exact (by decide : ¬ Odd (2 : ℕ)) hodd_ab

end Work.DoubleTransitivity.Sec5
