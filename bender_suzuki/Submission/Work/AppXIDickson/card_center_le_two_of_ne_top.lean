import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.AppXIDickson

/-- In a finite type with at least three elements, there are two distinct elements
different from any prescribed element. -/
lemma exists_two_ne_of_three_le_card {α : Type*} [Finite α] (e : α) (h : 3 ≤ Nat.card α) :
    ∃ a b : α, a ≠ e ∧ b ≠ e ∧ a ≠ b := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hcard : 3 ≤ (Finset.univ : Finset α).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h
  have herase : 2 ≤ ((Finset.univ : Finset α).erase e).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ e)]
    omega
  have herase' : 1 < ((Finset.univ : Finset α).erase e).card := by omega
  rw [Finset.one_lt_card] at herase'
  obtain ⟨a, ha, b, hb, hab⟩ := herase'
  rw [Finset.mem_erase] at ha hb
  exact ⟨a, b, ha.1, hb.1, hab⟩

/-- If `x⁴ = 1`, `x ≠ 1` and the order of `x` is not `4`, then `x` has order `2`. -/
lemma orderOf_eq_two_of_dvd_four {G : Type*} [Group G] {x : G}
    (h4 : x ^ 4 = 1) (h1 : x ≠ 1) (hne4 : orderOf x ≠ 4) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr h4
  have hdvd2 : orderOf x ∣ 2 ^ 2 := by simpa using hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 2)).mp hdvd2
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h
  · rw [h] at hk'; simp only [pow_zero] at hk'; exact absurd (orderOf_eq_one_iff.mp hk') h1
  · rw [h] at hk'; simpa using hk'
  · rw [h] at hk'; norm_num at hk'; exact absurd hk' hne4

/-- If every element of a finite group `G` satisfies `x ^ 4 = 1`, there is a unique
element of order `2`, and the centre of `G` is not the whole group, then the centre
has at most two elements. -/
theorem card_center_le_two_of_ne_top {G : Type*} [Group G] [Finite G]
    (hpow : ∀ x : G, x ^ 4 = 1)
    (huniq : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (hne : Subgroup.center G ≠ ⊤) :
    Nat.card (Subgroup.center G) ≤ 2 := by
  classical
  by_contra hle
  rw [not_le] at hle
  -- The centre has at least three elements, hence two distinct nonidentity elements.
  have hS3 : 3 ≤ Nat.card (Subgroup.center G) := Nat.succ_le_of_lt hle
  obtain ⟨a, b, ha1, hb1, hab⟩ :=
    exists_two_ne_of_three_le_card (1 : Subgroup.center G) hS3
  have hane : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hbne : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  -- One of them has order `4`.
  have hd4 : orderOf (a : G) = 4 ∨ orderOf (b : G) = 4 := by
    by_contra h
    push Not at h
    exact hab (Subtype.ext (huniq (a : G) (b : G)
      (orderOf_eq_two_of_dvd_four (hpow _) hane h.1)
      (orderOf_eq_two_of_dvd_four (hpow _) hbne h.2)))
  -- An element of the centre of order `4` yields a contradiction.
  have step : ∀ z : Subgroup.center G, orderOf (z : G) = 4 → False := by
    intro z hz4
    have ht2 : ((z : G) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show (2 : ℕ) * 2 = 4 from by norm_num]
      exact hpow (z : G)
    have htne : (z : G) ^ 2 ≠ 1 := by
      intro h
      have hd : orderOf (z : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hz4] at hd
      exact absurd (Nat.le_of_dvd (by norm_num) hd) (by norm_num)
    have htord : orderOf ((z : G) ^ 2) = 2 := orderOf_eq_prime ht2 htne
    have hteq : ∀ y : G, orderOf y = 2 → y = (z : G) ^ 2 := fun y hy => huniq y _ hy htord
    -- There is an element outside the centre.
    obtain ⟨x, hx⟩ : ∃ x : G, x ∉ Subgroup.center G := by
      by_contra h
      push Not at h
      exact hne ((Subgroup.eq_top_iff' (Subgroup.center G)).mpr h)
    have hx1 : x ≠ 1 := by
      intro h
      apply hx
      rw [h]
      exact Subgroup.one_mem _
    have hx2sq : (x ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show (2 : ℕ) * 2 = 4 from by norm_num]
      exact hpow x
    rcases eq_or_ne (x ^ 2) 1 with hx2 | hx2
    · -- `x ^ 2 = 1` makes `x` an involution, hence central.
      have hxz : x = (z : G) ^ 2 := hteq x (orderOf_eq_prime hx2 hx1)
      exact hx (by rw [hxz]; exact Subgroup.pow_mem _ z.2 2)
    · -- `x ^ 2 = z ^ 2`; then `x * z⁻¹` is an involution, hence central.
      have hx2ord : orderOf (x ^ 2) = 2 := orderOf_eq_prime hx2sq hx2
      have hx2eq : x ^ 2 = (z : G) ^ 2 := hteq (x ^ 2) hx2ord
      have hcomm : Commute x (z : G) :=
        (commute_iff_eq x (z : G)).mpr ((Subgroup.mem_center_iff.mp z.2) x)
      have hy2 : (x * (z : G)⁻¹) ^ 2 = 1 := by
        rw [hcomm.inv_right.mul_pow 2, hx2eq, inv_pow]
        exact mul_inv_cancel _
      have hy1 : x * (z : G)⁻¹ ≠ 1 := by
        intro h
        apply hx
        have hxz : x = (z : G) := by
          have := congrArg (fun t => t * (z : G)) h
          simpa using this
        rw [hxz]; exact z.2
      have hyeq : x * (z : G)⁻¹ = (z : G) ^ 2 := hteq _ (orderOf_eq_prime hy2 hy1)
      have hxz2z : x = (z : G) ^ 2 * (z : G) := by
        have := congrArg (fun t => t * (z : G)) hyeq
        simpa using this
      exact hx (by rw [hxz2z]; exact Subgroup.mul_mem _ (Subgroup.pow_mem _ z.2 2) z.2)
  exact hd4.elim (step a) (step b)

end Work.AppXIDickson
