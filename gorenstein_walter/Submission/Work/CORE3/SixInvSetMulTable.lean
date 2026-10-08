import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFiveOf
import Submission.Work.CORE3.SixSetSixthInvolution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.CORE3

open Work.GW2

/-!
# The multiplication table of a six-element inverted set

Bender 1981 §3: for an involution `y ∉ Ĥ` the inverted set `I_Ĥ(y) = {x ∈ Ĥ | y x y = x⁻¹}`
has `cosetInvCount Ĥ y` elements.  For an element `a ∈ I_Ĥ(y)` of order `3` and two distinct
involutions `b₁, b₂ ∈ I_Ĥ(y)`, the six elements `1, a, a², b₁, b₂, x` exhaust `I_Ĥ(y)`, and
they multiply like the elements of `S₃`: `b₁ a b₁ = a⁻¹` and `(b₁ b₂)³ = 1`.

The proof is purely elementary.  If `|I| = 6` then the single element `x` of `I` outside
`{1, a, a², b₁, b₂}` has order `2` (`Work.CORE3.SixSetSixthInvolution`).  Hence the elements
of `I` of order `3` are exactly `a, a²`, and for an involution `z ∈ I` the conjugate
`z a z ∈ I` has order `3`, so it is `a` or `a²`; it cannot be `a` (then `z` commutes with `a`,
so `z a ∈ I` while `(z a)² = a² ≠ 1`).  Finally `b₁ b₂ b₁` and `b₂ b₁ b₂` lie in `I` and are
involutions different from `b₁, b₂`, hence both equal `x`, and
`(b₁ b₂)³ = (b₁ b₂ b₁)(b₂ b₁ b₂) = x² = 1`.
-/

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

/-- If `z * z = 1` and `z` commutes with `a`, then `(z * a)² = a²`. -/
private theorem mul_self_mul_of_commute {G : Type} [Group G] {z a : G} (hz : z * z = 1)
    (hcomm : z * a = a * z) : (z * a) * (z * a) = a * a := by
  have h1 : (z * a) * (z * a) = z * (a * z) * a := by group
  rw [h1, ← hcomm]
  have h2 : z * (z * a) * a = (z * z) * (a * a) := by group
  rw [h2, hz, one_mul]

/-- **The multiplication table of `I_Ĥ(y)` when `|I_Ĥ(y)| = 6`.**  For an involution `y`,
an element `a ∈ I_Ĥ(y)` of order `3` and two distinct involutions `b₁, b₂ ∈ I_Ĥ(y)`, one has
`b₁ a b₁ = a⁻¹` and `(b₁ b₂)³ = 1`. -/
theorem invSetIn_six_mul_table {G : Type} [Group G] [Finite G] {Hh : Subgroup G} {y : G}
    (hy : y * y = 1) (hcard : (invSetIn Hh y).ncard = 6)
    {a b1 b2 : G} (ha : a ∈ invSetIn Hh y) (ha3 : orderOf a = 3)
    (hb1 : b1 ∈ invSetIn Hh y) (hb1_2 : orderOf b1 = 2)
    (hb2 : b2 ∈ invSetIn Hh y) (hb2_2 : orderOf b2 = 2) (h12 : b1 ≠ b2) :
    b1 * a * b1 = a⁻¹ ∧ (b1 * b2) ^ 3 = 1 := by
  classical
  have h1I : (1 : G) ∈ invSetIn Hh y := one_mem_invSetIn hy
  have hsq : ∀ z, z ∈ invSetIn Hh y → z * z ∈ invSetIn Hh y := by
    intro z hz
    simpa [pow_two] using pow_mem_invSetIn hy hz 2
  have hinv : ∀ z, z ∈ invSetIn Hh y → z⁻¹ ∈ invSetIn Hh y := fun z hz => inv_mem_invSetIn hy hz
  have hconj : ∀ z z', z ∈ invSetIn Hh y → z' ∈ invSetIn Hh y → z * z' * z ∈ invSetIn Hh y :=
    fun z z' hz hz' => mul_mem_invSetIn_conj hy hz hz'
  have hmul : ∀ z z', z ∈ invSetIn Hh y → z' ∈ invSetIn Hh y → z * z' = z' * z →
      z * z' ∈ invSetIn Hh y :=
    fun z z' hz hz' hc => mul_mem_invSetIn hy hz hz' hc
  -- elementary order facts
  have ha3p : a * a * a = 1 := by
    have h : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
    rwa [pow_three, ← mul_assoc] at h
  have ha_ne1 : a ≠ 1 := by
    intro hh; rw [hh, orderOf_one] at ha3; exact absurd ha3 (by norm_num)
  have ha_inv : a⁻¹ = a * a := inv_eq_iff_mul_eq_one.mpr (by rw [← mul_assoc]; exact ha3p)
  have ha2_ord : orderOf (a * a) = 3 := orderOf_sq_of_orderOf_three ha3
  have ha2_ne1 : a * a ≠ 1 := by
    intro hh; rw [hh, orderOf_one] at ha2_ord; exact absurd ha2_ord (by norm_num)
  have ha2_ne_a : a * a ≠ a := by
    intro hh; exact ha_ne1 (mul_left_cancel (by rw [mul_one]; exact hh))
  have hb1_sq : b1 * b1 = 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1_2).1
  have hb1_ne1 : b1 ≠ 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1_2).2
  have hb1_inv : b1⁻¹ = b1 := inv_eq_of_mul_eq_one_right hb1_sq
  have hb2_sq : b2 * b2 = 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2_2).1
  have hb2_ne1 : b2 ≠ 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2_2).2
  have hb2_inv : b2⁻¹ = b2 := inv_eq_of_mul_eq_one_right hb2_sq
  have hb1_ne_a : b1 ≠ a := by
    intro hh; rw [hh, ha3] at hb1_2; exact absurd hb1_2 (by norm_num)
  have hb1_ne_a2 : b1 ≠ a * a := by
    intro hh; rw [hh, ha2_ord] at hb1_2; exact absurd hb1_2 (by norm_num)
  have hb2_ne_a : b2 ≠ a := by
    intro hh; rw [hh, ha3] at hb2_2; exact absurd hb2_2 (by norm_num)
  have hb2_ne_a2 : b2 ≠ a * a := by
    intro hh; rw [hh, ha2_ord] at hb2_2; exact absurd hb2_2 (by norm_num)
  -- ## The sixth element `x` of `I`
  have hSsub : ({1, a, a * a, b1, b2} : Set G) ⊆ invSetIn Hh y := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact h1I
    · exact ha
    · exact hsq a ha
    · exact hb1
    · exact hb2
  have hScoe : (({1, a, a * a, b1, b2} : Finset G) : Set G)
      = ({1, a, a * a, b1, b2} : Set G) := by
    simp
  have hScard : ({1, a, a * a, b1, b2} : Set G).ncard = 5 := by
    rw [← hScoe, Set.ncard_coe_finset]
    simp [ha_ne1, ha_ne1.symm, ha2_ne1, ha2_ne1.symm, hb1_ne1, hb1_ne1.symm,
      hb2_ne1, hb2_ne1.symm, ha2_ne_a, ha2_ne_a.symm, hb1_ne_a, hb1_ne_a.symm,
      hb1_ne_a2, hb1_ne_a2.symm, hb2_ne_a, hb2_ne_a.symm, hb2_ne_a2, hb2_ne_a2.symm,
      h12, h12.symm]
  have hdiff : (invSetIn Hh y \ ({1, a, a * a, b1, b2} : Set G)).ncard = 1 := by
    rw [Set.ncard_sdiff hSsub, hcard, hScard]
  obtain ⟨x, hxeq⟩ := Set.ncard_eq_one.mp hdiff
  have hxmem : x ∈ invSetIn Hh y \ ({1, a, a * a, b1, b2} : Set G) := by
    rw [hxeq]; exact Set.mem_singleton_iff.mpr rfl
  have hxI : x ∈ invSetIn Hh y := hxmem.1
  have hxnot : x ∉ ({1, a, a * a, b1, b2} : Set G) := hxmem.2
  have hmem : ∀ z : G, z ∈ invSetIn Hh y ↔
      z = 1 ∨ z = a ∨ z = a * a ∨ z = b1 ∨ z = b2 ∨ z = x := by
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
        rw [hxeq, Set.mem_singleton_iff] at hz'
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hz'))))
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact h1I
      · exact ha
      · exact hsq a ha
      · exact hb1
      · exact hb2
      · exact hxI
  have hx_ord : orderOf x = 2 := SixSetSixthInvolution hmem ha3 hb1_2 hb2_2 hinv hsq hxnot
  have hx_sq : x * x = 1 := ((orderOf_eq_two_iff_mul_self x).mp hx_ord).1
  have hx_ne1 : x ≠ 1 := ((orderOf_eq_two_iff_mul_self x).mp hx_ord).2
  -- ## Classification of the elements of `I` of order `3` and of order `2`
  have hord3 : ∀ z, z ∈ invSetIn Hh y → orderOf z = 3 → z = a ∨ z = a * a := by
    intro z hz hz3
    rcases (hmem z).mp hz with h | h | h | h | h | h
    · rw [h, orderOf_one] at hz3; exact absurd hz3 (by norm_num)
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, hb1_2] at hz3; exact absurd hz3 (by norm_num)
    · rw [h, hb2_2] at hz3; exact absurd hz3 (by norm_num)
    · rw [h, hx_ord] at hz3; exact absurd hz3 (by norm_num)
  have hinv2 : ∀ z, z ∈ invSetIn Hh y → orderOf z = 2 → z = b1 ∨ z = b2 ∨ z = x := by
    intro z hz hz2
    rcases (hmem z).mp hz with h | h | h | h | h | h
    · rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
    · rw [h, ha3] at hz2; exact absurd hz2 (by norm_num)
    · rw [h, ha2_ord] at hz2; exact absurd hz2 (by norm_num)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- ## Every involution of `I` inverts `a`
  have hbinv : ∀ z, z ∈ invSetIn Hh y → orderOf z = 2 → z * a * z = a⁻¹ := by
    intro z hz hz2
    have hzsq : z * z = 1 := ((orderOf_eq_two_iff_mul_self z).mp hz2).1
    have hz_ne1 : z ≠ 1 := ((orderOf_eq_two_iff_mul_self z).mp hz2).2
    have hzI : z * a * z ∈ invSetIn Hh y := hconj z a hz ha
    have hzord : orderOf (z * a * z) = 3 := by
      have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzsq
      have h : z * a * z = (MulAut.conj z) a := by rw [MulAut.conj_apply, hz_inv]
      rw [h, MulEquiv.orderOf_eq, ha3]
    rcases hord3 (z * a * z) hzI hzord with h | h
    · exfalso
      have hcomm : z * a = a * z := by
        have h' : (z * a * z) * z = a * z := by rw [h]
        rwa [mul_assoc, hzsq, mul_one] at h'
      have hmemza : z * a ∈ invSetIn Hh y := hmul z a hz ha hcomm
      have hza_sq : (z * a) * (z * a) = a * a := mul_self_mul_of_commute hzsq hcomm
      rcases (hmem (z * a)).mp hmemza with h1 | h1 | h1 | h1 | h1 | h1
      · rw [h1, one_mul] at hza_sq
        exact ha2_ne1 hza_sq.symm
      · exact hz_ne1 (mul_right_cancel (by rw [h1, one_mul]))
      · have hza : z = a := mul_right_cancel h1
        rw [hza, ha3] at hz2
        exact absurd hz2 (by norm_num)
      · rw [h1, hb1_sq] at hza_sq
        exact ha2_ne1 hza_sq.symm
      · rw [h1, hb2_sq] at hza_sq
        exact ha2_ne1 hza_sq.symm
      · rw [h1, hx_sq] at hza_sq
        exact ha2_ne1 hza_sq.symm
    · rw [h, ← ha_inv]
  have hb1a : b1 * a * b1 = a⁻¹ := hbinv b1 hb1 hb1_2
  have hb2a : b2 * a * b2 = a⁻¹ := hbinv b2 hb2 hb2_2
  -- ## `b₁ b₂ b₁` and `b₂ b₁ b₂`
  have hd_ord : orderOf (b1 * b2 * b1) = 2 := by
    have h : b1 * b2 * b1 = (MulAut.conj b1) b2 := by rw [MulAut.conj_apply, hb1_inv]
    rw [h, MulEquiv.orderOf_eq, hb2_2]
  have hd_cases : b1 * b2 * b1 = b1 ∨ b1 * b2 * b1 = b2 ∨ b1 * b2 * b1 = x :=
    hinv2 (b1 * b2 * b1) (hconj b1 b2 hb1 hb2) hd_ord
  have hd_ne_b1 : b1 * b2 * b1 ≠ b1 := by
    intro hh
    have h' : b1⁻¹ * (b1 * b2 * b1) = b1⁻¹ * b1 := by rw [hh]
    have h2 : b2 * b1 = 1 := by
      have h'' : b1⁻¹ * (b1 * b2 * b1) = b2 * b1 := by group
      rw [h''] at h'
      simpa using h'
    have h3 : b2 = b1 := mul_right_cancel (by rw [h2, hb1_sq])
    exact h12 h3.symm
  have hd_ne_b2 : b1 * b2 * b1 ≠ b2 := by
    intro hh
    have hcomm : b1 * b2 = b2 * b1 := by
      have h' : (b1 * b2 * b1) * b1 = b2 * b1 := by rw [hh]
      have h'' : (b1 * b2 * b1) * b1 = b1 * b2 * (b1 * b1) := by group
      rw [h'', hb1_sq, mul_one] at h'
      exact h'
    have hb12I : b1 * b2 ∈ invSetIn Hh y := hmul b1 b2 hb1 hb2 hcomm
    have hb12_sq : (b1 * b2) * (b1 * b2) = 1 := by
      rw [mul_self_mul_of_commute hb1_sq hcomm, hb2_sq]
    have hb12_ne1 : b1 * b2 ≠ 1 := by
      intro h1'
      have h3 : b2 = b1 := mul_left_cancel (by rw [h1', hb1_sq])
      exact h12 h3.symm
    have hb12_ord : orderOf (b1 * b2) = 2 :=
      (orderOf_eq_two_iff_mul_self (b1 * b2)).mpr ⟨hb12_sq, hb12_ne1⟩
    rcases hinv2 (b1 * b2) hb12I hb12_ord with h1' | h1' | h1'
    · exact hb2_ne1 (mul_left_cancel (by rw [h1', mul_one]))
    · exact hb1_ne1 (mul_right_cancel (by rw [h1', one_mul]))
    · have hxa : x * a * x = a⁻¹ := hbinv x hxI hx_ord
      have hcen_inv : (b1 * b2) * a * (b1 * b2)⁻¹ = a := by
        rw [mul_inv_rev, hb1_inv, hb2_inv]
        calc (b1 * b2) * a * (b2 * b1) = b1 * (b2 * a * b2) * b1 := by group
          _ = b1 * a⁻¹ * b1 := by rw [hb2a]
          _ = (b1 * a * b1)⁻¹ := by
                rw [mul_inv_rev, mul_inv_rev, hb1_inv]; group
          _ = a := by rw [hb1a, inv_inv]
      have hcen : (b1 * b2) * a * (b1 * b2) = a := by
        have hinv : (b1 * b2)⁻¹ = b1 * b2 := inv_eq_of_mul_eq_one_right hb12_sq
        calc (b1 * b2) * a * (b1 * b2) = (b1 * b2) * a * (b1 * b2)⁻¹ := by rw [hinv]
          _ = a := hcen_inv
      have hthis : a⁻¹ = a := by
        rw [← hxa, ← h1']
        exact hcen
      have haa : a * a = 1 := (mul_self_eq_one_iff_eq_inv a).mpr hthis.symm
      have hdvd : orderOf a ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]
        exact haa
      rw [ha3] at hdvd
      exact absurd hdvd (by norm_num)
  have hd_eq_x : b1 * b2 * b1 = x := by
    rcases hd_cases with h | h | h
    · exact absurd h hd_ne_b1
    · exact absurd h hd_ne_b2
    · exact h
  -- the mirror element `b₂ b₁ b₂`
  have he_ord : orderOf (b2 * b1 * b2) = 2 := by
    have h : b2 * b1 * b2 = (MulAut.conj b2) b1 := by rw [MulAut.conj_apply, hb2_inv]
    rw [h, MulEquiv.orderOf_eq, hb1_2]
  have he_cases : b2 * b1 * b2 = b1 ∨ b2 * b1 * b2 = b2 ∨ b2 * b1 * b2 = x :=
    hinv2 (b2 * b1 * b2) (hconj b2 b1 hb2 hb1) he_ord
  have he_ne_b2 : b2 * b1 * b2 ≠ b2 := by
    intro hh
    have h' : b2⁻¹ * (b2 * b1 * b2) = b2⁻¹ * b2 := by rw [hh]
    have h2 : b1 * b2 = 1 := by
      have h'' : b2⁻¹ * (b2 * b1 * b2) = b1 * b2 := by group
      rw [h''] at h'
      simpa using h'
    have h3 : b1 = b2 := mul_right_cancel (by rw [h2, hb2_sq])
    exact h12 h3
  have he_ne_b1 : b2 * b1 * b2 ≠ b1 := by
    intro hh
    have hcomm : b2 * b1 = b1 * b2 := by
      have h' : (b2 * b1 * b2) * b2 = b1 * b2 := by rw [hh]
      have h'' : (b2 * b1 * b2) * b2 = b2 * b1 * (b2 * b2) := by group
      rw [h'', hb2_sq, mul_one] at h'
      exact h'
    have hb12I : b2 * b1 ∈ invSetIn Hh y := hmul b2 b1 hb2 hb1 hcomm
    have hb12_sq : (b2 * b1) * (b2 * b1) = 1 := by
      rw [mul_self_mul_of_commute hb2_sq hcomm, hb1_sq]
    have hb12_ne1 : b2 * b1 ≠ 1 := by
      intro h1'
      have h3 : b1 = b2 := mul_left_cancel (by rw [h1', hb2_sq])
      exact h12 h3
    have hb12_ord : orderOf (b2 * b1) = 2 :=
      (orderOf_eq_two_iff_mul_self (b2 * b1)).mpr ⟨hb12_sq, hb12_ne1⟩
    rcases hinv2 (b2 * b1) hb12I hb12_ord with h1' | h1' | h1'
    · exact hb2_ne1 (mul_right_cancel (by rw [h1', one_mul]))
    · exact hb1_ne1 (mul_left_cancel (by rw [h1', mul_one]))
    · have hxa : x * a * x = a⁻¹ := hbinv x hxI hx_ord
      have hcen_inv : (b2 * b1) * a * (b2 * b1)⁻¹ = a := by
        rw [mul_inv_rev, hb2_inv, hb1_inv]
        calc (b2 * b1) * a * (b1 * b2) = b2 * (b1 * a * b1) * b2 := by group
          _ = b2 * a⁻¹ * b2 := by rw [hb1a]
          _ = (b2 * a * b2)⁻¹ := by
                rw [mul_inv_rev, mul_inv_rev, hb2_inv]; group
          _ = a := by rw [hb2a, inv_inv]
      have hcen : (b2 * b1) * a * (b2 * b1) = a := by
        have hinv : (b2 * b1)⁻¹ = b2 * b1 := inv_eq_of_mul_eq_one_right hb12_sq
        calc (b2 * b1) * a * (b2 * b1) = (b2 * b1) * a * (b2 * b1)⁻¹ := by rw [hinv]
          _ = a := hcen_inv
      have hthis : a⁻¹ = a := by
        rw [← hxa, ← h1']
        exact hcen
      have haa : a * a = 1 := (mul_self_eq_one_iff_eq_inv a).mpr hthis.symm
      have hdvd : orderOf a ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]
        exact haa
      rw [ha3] at hdvd
      exact absurd hdvd (by norm_num)
  have he_eq_x : b2 * b1 * b2 = x := by
    rcases he_cases with h | h | h
    · exact absurd h he_ne_b1
    · exact absurd h he_ne_b2
    · exact h
  refine ⟨hb1a, ?_⟩
  rw [pow_three]
  have h' : b1 * b2 * (b1 * b2 * (b1 * b2)) = (b1 * b2 * b1) * (b2 * b1 * b2) := by group
  rw [h', hd_eq_x, he_eq_x, hx_sq]

theorem SixInvSetMulTable (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y = 6 →
      ∀ a b1 b2 : G, a ∈ Work.CORE3.invSetIn B.Hhat y → orderOf a = 3 →
        b1 ∈ Work.CORE3.invSetIn B.Hhat y → orderOf b1 = 2 →
        b2 ∈ Work.CORE3.invSetIn B.Hhat y → orderOf b2 = 2 → b1 ≠ b2 →
        b1 * a * b1 = a⁻¹ ∧ (b1 * b2) ^ 3 = 1 := by
  intro y hy2 hyH hcount a b1 b2 ha ha3 hb1 hb1_2 hb2 hb2_2 h12
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hcard : (invSetIn B.Hhat y).ncard = 6 := by
    rw [ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH]
    exact hcount
  exact invSetIn_six_mul_table hy hcard ha ha3 hb1 hb1_2 hb2 hb2_2 h12

end Work.CORE3
