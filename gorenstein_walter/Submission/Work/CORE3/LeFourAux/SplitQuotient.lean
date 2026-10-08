import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE3.LeFourAux

/-- In a finite group `M` of order `6`, an element `x` of order `3` and an element `y` with
`y ^ 3 = 1`, `y ≠ 1` satisfy `y = x` or `y = x ^ 2`.

Indeed `x` generates a subgroup of order `3` and index `2`; the corresponding quotient has
order `2`, so `y ^ 2 = 1` modulo `⟨x⟩` while `y ^ 3 = 1` there, forcing `y ∈ ⟨x⟩`; and the
non-identity elements of `⟨x⟩` are exactly `x` and `x ^ 2`. -/
private theorem card_six_pow_three {M : Type*} [Group M] [Finite M] (hM : Nat.card M = 6)
    {x : M} (hx : orderOf x = 3) {y : M} (hy : y ^ 3 = 1) (hy1 : y ≠ 1) :
    y = x ∨ y = x ^ 2 := by
  classical
  have hHcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hx]
  have hHindex : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hHcard, hM] at this
    omega
  have hHn : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hHindex
  let φ : M →* M ⧸ Subgroup.zpowers x := QuotientGroup.mk' _
  have hyQ : (φ y) ^ 3 = 1 := by rw [← map_pow, hy, map_one]
  have hQcard : Nat.card (M ⧸ Subgroup.zpowers x) = 2 := by
    rw [← Subgroup.index_eq_card (Subgroup.zpowers x)]; exact hHindex
  have hyQ2 : (φ y) ^ 2 = 1 := by
    have hdvd : orderOf (φ y) ∣ 2 := by rw [← hQcard]; exact orderOf_dvd_natCard _
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hyQ1 : φ y = 1 := by
    have hdvd3 : orderOf (φ y) ∣ 3 := orderOf_dvd_of_pow_eq_one hyQ
    have hdvd2 : orderOf (φ y) ∣ 2 := orderOf_dvd_of_pow_eq_one hyQ2
    have hd : orderOf (φ y) ∣ Nat.gcd 3 2 := Nat.dvd_gcd hdvd3 hdvd2
    have hg : Nat.gcd 3 2 = 1 := by norm_num
    rw [hg] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hyH : y ∈ Subgroup.zpowers x := by
    have h : (QuotientGroup.mk' (Subgroup.zpowers x)) y = 1 := hyQ1
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff y).mp h
  obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := x)).mp hyH)
  rw [Finset.mem_range, hx] at hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, pow_zero] at hiy; exact absurd hiy.symm hy1
  · left; rw [h1, pow_one] at hiy; exact hiy.symm
  · right; rw [h2] at hiy; exact hiy.symm

/-- Let `W ≤ Hh` be a subgroup of index `6` in `Hh`, with `W` normal in `Hh`. If `a ∈ Hh` has
order `3` and `a ∉ W`, and if `b = b1 * b2 ∈ Hh` has `b ∉ W` and `b ^ 3 = 1`, then `b` is
congruent to `a` or to `a * a` modulo `W`.

Indeed, in the quotient `Hh ⧸ W` of order `6` the images of `a` and `b` are non-trivial
elements of order dividing `3`, and an order `6` group has only the two non-trivial cube roots
of unity, which are `ā` and `ā²`. -/
theorem SplitQuotient {G : Type} [Group G] [Finite G] {Hh W : Subgroup G}
    (hWle : W ≤ Hh) (hWn : (W.subgroupOf Hh).Normal) (hrel : W.relIndex Hh = 6)
    {a b1 b2 : G} (haH : a ∈ Hh) (hb1H : b1 ∈ Hh) (hb2H : b2 ∈ Hh)
    (ha3 : orderOf a = 3) (haW : a ∉ W) (hprod : b1 * b2 ∉ W) (hcube : (b1 * b2) ^ 3 = 1) :
    ∃ h : G, (h = a ∨ h = a * a) ∧ h⁻¹ * (b1 * b2) ∈ W := by
  classical
  let N : Subgroup Hh := W.subgroupOf Hh
  haveI hNn : N.Normal := hWn
  have hNindex : N.index = 6 := hrel
  have hQcard : Nat.card (Hh ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]; exact hNindex
  let x : Hh := ⟨a, haH⟩
  let x2 : Hh := ⟨a * a, mul_mem haH haH⟩
  let y : Hh := ⟨b1 * b2, mul_mem hb1H hb2H⟩
  let φ : Hh →* Hh ⧸ N := QuotientGroup.mk' N
  have ha3one : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simp [x, ha3one]
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    simp [y, hcube]
  have hxord : orderOf (φ x) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hx3, map_one]
    · intro h
      have h1 : (QuotientGroup.mk' N) x = 1 := h
      rw [QuotientGroup.mk'_apply] at h1
      exact haW ((Subgroup.mem_subgroupOf).mp ((QuotientGroup.eq_one_iff x).mp h1))
  have hyc : (φ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hyne : φ y ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk' N) y = 1 := h
    rw [QuotientGroup.mk'_apply] at h1
    exact hprod ((Subgroup.mem_subgroupOf).mp ((QuotientGroup.eq_one_iff y).mp h1))
  have hx2φ : φ x2 = (φ x) ^ 2 := by
    have : x2 = x * x := by apply Subtype.ext; rfl
    rw [this, map_mul, pow_two]
  rcases card_six_pow_three hQcard hxord hyc hyne with hcase | hcase
  · refine ⟨a, Or.inl rfl, ?_⟩
    have hxy : (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) y := hcase.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxy
    have hN : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have hW : (↑(x⁻¹ * y) : G) ∈ W := (Subgroup.mem_subgroupOf).mp hN
    simpa [x, y] using hW
  · refine ⟨a * a, Or.inr rfl, ?_⟩
    have hxy : (QuotientGroup.mk' N) x2 = (QuotientGroup.mk' N) y := by
      rw [hx2φ]; exact hcase.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxy
    have hN : x2⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have hW : (↑(x2⁻¹ * y) : G) ∈ W := (Subgroup.mem_subgroupOf).mp hN
    simpa [x2, y] using hW

end Work.CORE3.LeFourAux
