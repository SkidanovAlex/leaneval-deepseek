import Mathlib

set_option linter.unusedVariables false

namespace Work.CORE3

/-- In a group, if `I = {1, a, a*a, b1, b2, x}` with `orderOf a = 3`, `orderOf b1 = 2`,
`orderOf b2 = 2`, `I` closed under inversion, and `x` is none of the first five
elements, then necessarily `orderOf x = 2`.

Indeed `x⁻¹ ∈ I`, so `x⁻¹` is one of `1, a, a*a, b1, b2, x`. The first five options
force `x ∈ {1, a, a*a, b1, b2}`, contradicting `hx`; hence `x⁻¹ = x`, i.e. `x*x = 1`,
and since `x ≠ 1` we get `orderOf x = 2`. -/
theorem SixSetSixthInvolution {G : Type} [Group G] {I : Set G} {a b1 b2 x : G}
    (hmem : ∀ z : G, z ∈ I ↔ z = 1 ∨ z = a ∨ z = a * a ∨ z = b1 ∨ z = b2 ∨ z = x)
    (ha3 : orderOf a = 3) (hb1 : orderOf b1 = 2) (hb2 : orderOf b2 = 2)
    (hinv : ∀ z ∈ I, z⁻¹ ∈ I) (hsq : ∀ z ∈ I, z * z ∈ I)
    (hx : x ∉ ({1, a, a * a, b1, b2} : Set G)) :
    orderOf x = 2 := by
  -- Unfold the non-membership hypothesis into its five components.
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  obtain ⟨hx1, hxa, hxaa, hxb1, hxb2⟩ := hx
  -- `x` belongs to `I`, hence so does `x⁻¹`.
  have hxI : x ∈ I := (hmem x).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hxinvI : x⁻¹ ∈ I := hinv x hxI
  -- Elementary power/inverse facts.
  have ha3pow : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have hb1sq : b1 * b1 = 1 := by rw [← pow_two, ← hb1]; exact pow_orderOf_eq_one b1
  have hb2sq : b2 * b2 = 1 := by rw [← pow_two, ← hb2]; exact pow_orderOf_eq_one b2
  have haa' : (a * a) * a = 1 := by
    rw [← pow_two, ← pow_succ]; exact ha3pow
  have haa : a * (a * a) = 1 := by
    rw [← mul_assoc]; exact haa'
  have ha_inv : a⁻¹ = a * a := inv_eq_iff_mul_eq_one.mpr haa
  have haa_inv : (a * a)⁻¹ = a := inv_eq_iff_mul_eq_one.mpr haa'
  have hb1inv : b1⁻¹ = b1 := inv_eq_of_mul_eq_one_right hb1sq
  have hb2inv : b2⁻¹ = b2 := inv_eq_of_mul_eq_one_right hb2sq
  -- `x⁻¹ ∈ I` splits into six cases.
  have hcases := (hmem x⁻¹).mp hxinvI
  have hxx : x * x = 1 := by
    rcases hcases with h | h | h | h | h | h
    · exact absurd (inv_eq_one.mp h) hx1
    · exact absurd (show x = a * a by rw [← inv_inv x, h, ha_inv]) hxaa
    · exact absurd (show x = a by rw [← inv_inv x, h, haa_inv]) hxa
    · exact absurd (show x = b1 by rw [← inv_inv x, h, hb1inv]) hxb1
    · exact absurd (show x = b2 by rw [← inv_inv x, h, hb2inv]) hxb2
    · have hm := mul_inv_cancel x
      rwa [h] at hm
  exact orderOf_eq_prime (by simpa [pow_two] using hxx) hx1

end Work.CORE3
