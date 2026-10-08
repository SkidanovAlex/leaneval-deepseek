import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove

set_option linter.style.haveILetI false

/-- If `a > 0`, `a ∣ b` and `b ∣ 2 * a`, then `b = a` or `b = 2 * a`. -/
lemma eq_or_two_mul_of_dvd_of_dvd {a b : ℕ} (ha : 0 < a) (hab : a ∣ b) (hb : b ∣ 2 * a) :
    b = a ∨ b = 2 * a := by
  obtain ⟨k, rfl⟩ := hab
  obtain ⟨m, hm⟩ := hb
  have h2 : a * (k * m) = a * 2 := by
    rw [← mul_assoc, ← hm, Nat.mul_comm]
  have hkm : k * m = 2 := Nat.mul_left_cancel ha h2
  have hk : k = 1 ∨ k = 2 := (Nat.dvd_prime Nat.prime_two).mp ⟨m, hkm.symm⟩
  rcases hk with hk | hk
  · left; rw [hk, mul_one]
  · right; rw [hk]; ring

/-- If `φ : A →* G` is injective, `1 < |A|` is odd, and every non-identity element of `A`
maps to an element of `G` whose order is `|G|` or `|G| / 2`, then `|A|` is prime and
`|G| = |A|` or `|G| = 2 * |A|`. -/
theorem cyclic_orders_prime {A G : Type} [Group A] [Finite A] [Group G] [Finite G]
    (φ : A →* G) (hφ : Function.Injective φ)
    (hm1 : 1 < Nat.card A) (hodd : Odd (Nat.card A))
    (h : ∀ a : A, a ≠ 1 → orderOf (φ a) = Nat.card G ∨ 2 * orderOf (φ a) = Nat.card G) :
    (Nat.card A).Prime ∧ (Nat.card G = Nat.card A ∨ Nat.card G = 2 * Nat.card A) := by
  classical
  have hpos : 0 < Nat.card A := by omega
  -- `|A|` divides `|G|` because `A` embeds into `G` via `φ`.
  have hcard_dvd : Nat.card A ∣ Nat.card G := by
    have hbij : Function.Bijective (MonoidHom.rangeRestrict φ) := by
      refine ⟨?_, MonoidHom.rangeRestrict_surjective φ⟩
      intro x y hxy
      apply hφ
      have := congrArg Subtype.val hxy
      simpa using this
    have hA : Nat.card A = Nat.card φ.range := Nat.card_eq_of_bijective _ hbij
    rw [hA]
    exact Subgroup.card_subgroup_dvd_card φ.range
  haveI : Fintype A := Fintype.ofFinite A
  have hnt : Nontrivial A := by
    have : 1 < Fintype.card A := by rw [← Nat.card_eq_fintype_card]; exact hm1
    exact Fintype.one_lt_card_iff_nontrivial.mp this
  obtain ⟨a0, ha0⟩ := exists_ne (1 : A)
  -- Applying `h` at one non-identity element gives `|G| ∣ 2 * |A|`.
  have hG_dvd : Nat.card G ∣ 2 * Nat.card A := by
    have hd : orderOf (φ a0) = orderOf a0 := orderOf_injective φ hφ a0
    rcases h a0 ha0 with hh | hh
    · have hG : Nat.card G = orderOf a0 := by rw [← hh, hd]
      rw [hG]
      exact dvd_mul_of_dvd_right (orderOf_dvd_natCard a0) 2
    · rw [hd] at hh
      rw [← hh]
      exact mul_dvd_mul_left 2 (orderOf_dvd_natCard a0)
  -- Hence `|G| = |A|` or `|G| = 2 * |A|`.
  have hG_eq : Nat.card G = Nat.card A ∨ Nat.card G = 2 * Nat.card A :=
    eq_or_two_mul_of_dvd_of_dvd hpos hcard_dvd hG_dvd
  -- Every non-identity element has order `|A|`.
  have horder : ∀ a : A, a ≠ 1 → orderOf a = Nat.card A := by
    intro a ha
    have hdvd : orderOf a ∣ Nat.card A := orderOf_dvd_natCard a
    have hd : orderOf (φ a) = orderOf a := orderOf_injective φ hφ a
    rcases h a ha with hh | hh
    · rcases hG_eq with hG | hG
      · rw [hd, hG] at hh; exact hh
      · rw [hd, hG] at hh
        rw [hh] at hdvd
        have hle := Nat.le_of_dvd hpos hdvd
        omega
    · rw [hd] at hh
      rcases hG_eq with hG | hG
      · rw [hG] at hh
        exact absurd (even_iff_two_dvd.mpr ⟨orderOf a, hh.symm⟩) (Nat.not_even_iff_odd.mpr hodd)
      · rw [hG] at hh
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) hh
  refine ⟨?_, hG_eq⟩
  rw [Nat.prime_def_lt]
  refine ⟨?_, ?_⟩
  · rcases hodd with ⟨k, hk⟩; omega
  · -- If some `1 < m < |A|` divided `|A|`, we would get a non-identity element of order `m`.
    intro m hm hm_dvd
    by_contra hm_ne
    have hmn : m = Nat.card A := by
      obtain ⟨q, hq⟩ := hm_dvd
      have hqpos : 0 < q := by
        rw [Nat.pos_iff_ne_zero]
        intro hq0
        rw [hq0, mul_zero] at hq
        omega
      have hb_ord : orderOf (a0 ^ q) = m := by
        rw [orderOf_pow, horder a0 ha0]
        have hgd : (Nat.card A).gcd q = q := Nat.gcd_eq_right ⟨m, by rw [hq, Nat.mul_comm]⟩
        rw [hgd, hq]
        exact Nat.mul_div_left m hqpos
      have hb_ne : a0 ^ q ≠ 1 := by
        intro hc
        have h1 : orderOf (a0 ^ q) = 1 := by rw [hc, orderOf_one]
        rw [hb_ord] at h1
        exact hm_ne h1
      have h2 := horder (a0 ^ q) hb_ne
      omega
    omega

end Work.ThmF.Prove
