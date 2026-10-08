import Mathlib
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.SixSetSixthInvolution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.CORE3

/-- An element of order `3`: its square again has order `3`. -/
private theorem orderOf_sq_of_orderOf_three {G : Type} [Group G] {a : G}
    (ha : orderOf a = 3) : orderOf (a * a) = 3 := by
  have ha3p : a * a * a = 1 := by
    have h : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    rwa [pow_three, ← mul_assoc] at h
  have h6 : (a * a) ^ 3 = 1 := by
    rw [pow_three]
    have hkey : a * a * (a * a * (a * a)) = a * a * a * (a * a * a) := by group
    rw [hkey, ha3p, one_mul]
  have hdvd : orderOf (a * a) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h6
  have hne : orderOf (a * a) ≠ 1 := by
    intro h
    have h1 : a * a = 1 := orderOf_eq_one_iff.mp h
    have h2 : orderOf a ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact h1
    rw [ha] at h2
    exact absurd h2 (by norm_num)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne
  · exact h

theorem SixInvSetEnumeration {G : Type} [Group G] {Hh : Subgroup G} {y a b1 b2 : G}
    (hy : y * y = 1) (haI : a ∈ Work.CORE3.invSetIn Hh y) (ha3 : orderOf a = 3)
    (hb1I : b1 ∈ Work.CORE3.invSetIn Hh y) (hb1o : orderOf b1 = 2)
    (hb2I : b2 ∈ Work.CORE3.invSetIn Hh y) (hb2o : orderOf b2 = 2) (h12 : b1 ≠ b2)
    (hsix : (Work.CORE3.invSetIn Hh y).ncard = 6) :
    ∃ c : G, c ∈ Work.CORE3.invSetIn Hh y ∧ orderOf c = 2 ∧
      (∀ z : G, z ∈ Work.CORE3.invSetIn Hh y ↔
        z = 1 ∨ z = a ∨ z = a * a ∨ z = b1 ∨ z = b2 ∨ z = c) := by
  classical
  have h1I : (1 : G) ∈ invSetIn Hh y := one_mem_invSetIn hy
  have hsq : ∀ z, z ∈ invSetIn Hh y → z * z ∈ invSetIn Hh y := by
    intro z hz
    simpa [pow_two] using pow_mem_invSetIn hy hz 2
  have hinv : ∀ z, z ∈ invSetIn Hh y → z⁻¹ ∈ invSetIn Hh y :=
    fun z hz => inv_mem_invSetIn hy hz
  have ha3p : a * a * a = 1 := by
    have h : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
    rwa [pow_three, ← mul_assoc] at h
  have ha_ne1 : a ≠ 1 := by
    intro hh
    rw [hh, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  have ha2_ord : orderOf (a * a) = 3 := orderOf_sq_of_orderOf_three ha3
  have ha2_ne1 : a * a ≠ 1 := by
    intro hh
    rw [hh, orderOf_one] at ha2_ord
    exact absurd ha2_ord (by norm_num)
  have ha2_ne_a : a * a ≠ a := by
    intro hh
    exact ha_ne1 (mul_left_cancel (by rw [mul_one]; exact hh))
  have hb1_sq : b1 * b1 = 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).1
  have hb1_ne1 : b1 ≠ 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).2
  have hb2_sq : b2 * b2 = 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2o).1
  have hb2_ne1 : b2 ≠ 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2o).2
  have hb1_ne_a : b1 ≠ a := by
    intro hh
    rw [hh, ha3] at hb1o
    exact absurd hb1o (by norm_num)
  have hb1_ne_a2 : b1 ≠ a * a := by
    intro hh
    rw [hh, ha2_ord] at hb1o
    exact absurd hb1o (by norm_num)
  have hb2_ne_a : b2 ≠ a := by
    intro hh
    rw [hh, ha3] at hb2o
    exact absurd hb2o (by norm_num)
  have hb2_ne_a2 : b2 ≠ a * a := by
    intro hh
    rw [hh, ha2_ord] at hb2o
    exact absurd hb2o (by norm_num)
  have hSsub : ({1, a, a * a, b1, b2} : Set G) ⊆ invSetIn Hh y := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact h1I
    · exact haI
    · exact hsq a haI
    · exact hb1I
    · exact hb2I
  have hScoe : (({1, a, a * a, b1, b2} : Finset G) : Set G)
      = ({1, a, a * a, b1, b2} : Set G) := by simp
  have hScard : ({1, a, a * a, b1, b2} : Set G).ncard = 5 := by
    rw [← hScoe, Set.ncard_coe_finset]
    simp [ha_ne1, ha_ne1.symm, ha2_ne1, ha2_ne1.symm, hb1_ne1, hb1_ne1.symm,
      hb2_ne1, hb2_ne1.symm, ha2_ne_a, ha2_ne_a.symm, hb1_ne_a, hb1_ne_a.symm,
      hb1_ne_a2, hb1_ne_a2.symm, hb2_ne_a, hb2_ne_a.symm, hb2_ne_a2, hb2_ne_a2.symm,
      h12, h12.symm]
  have hdiff : (invSetIn Hh y \ ({1, a, a * a, b1, b2} : Set G)).ncard = 1 := by
    rw [Set.ncard_sdiff hSsub, hsix, hScard]
  obtain ⟨c, hceq⟩ := Set.ncard_eq_one.mp hdiff
  have hcmem : c ∈ invSetIn Hh y \ ({1, a, a * a, b1, b2} : Set G) := by
    rw [hceq]; exact Set.mem_singleton_iff.mpr rfl
  have hcI : c ∈ invSetIn Hh y := hcmem.1
  have hcnot : c ∉ ({1, a, a * a, b1, b2} : Set G) := hcmem.2
  have hmem : ∀ z : G, z ∈ invSetIn Hh y ↔
      z = 1 ∨ z = a ∨ z = a * a ∨ z = b1 ∨ z = b2 ∨ z = c := by
    intro z
    constructor
    · intro hz
      by_cases hzS : z ∈ ({1, a, a * a, b1, b2} : Set G)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzS
        rcases hzS with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · have hz' : z ∈ invSetIn Hh y \ ({1, a, a * a, b1, b2} : Set G) := ⟨hz, hzS⟩
        rw [hceq, Set.mem_singleton_iff] at hz'
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hz'))))
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact h1I
      · exact haI
      · exact hsq a haI
      · exact hb1I
      · exact hb2I
      · exact hcI
  have hc_ord : orderOf c = 2 :=
    SixSetSixthInvolution (I := invSetIn Hh y) (x := c) hmem ha3 hb1o hb2o hinv hsq hcnot
  exact ⟨c, hcI, hc_ord, hmem⟩

end Work.CORE3
