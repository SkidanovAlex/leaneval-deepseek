import Mathlib
import Submission.Work.CORE3.NoKleinFourOfCardSix
import Submission.Work.CORE3.orderOf_ne_six_of_not_isMulCommutative

/-!
# `Work.CORE3.OrderSixNoFiveSubset`

No non-abelian group `H` of order `6` carries a `5`-element subset `Q` that contains `1`,
is closed under inversion, and is closed under conjugation by its own involutions.

This is the abstract group-theoretic input of Bender 1981 §3 (the "image of `invSetIn Ĥ y`
inside `Ĥ/VU ≅ S₃`" argument): a hypothetical `n = 5` would produce exactly such a subset.

The proof first classifies the non-identity elements of `H`:

* `H` has no element of order `6` (`Work.CORE3.orderOf_ne_six_of_not_isMulCommutative`), since an
  element of order `|H|` generates `H`, making it cyclic and hence abelian;
* by Cauchy there is `a` of order `3`; its cyclic subgroup `P = ⟨a⟩ = {1, a, a²}` has index `2`,
  so `x * x ∈ P` for every `x`;
* therefore the elements of order `3` are exactly `a, a²`, and every element outside `P` is an
  involution.  Hence `H` is the disjoint union of `P` and its `3` involutions.

Counting inside `Q`: `1 ∈ Q`, and `a, a² ∈ Q` (if `a ∉ Q` then also `a² = a⁻¹ ∉ Q`, two elements
outside the `5`-element `Q`); so `P ⊆ Q` and `Q` contains exactly `2` involutions.  Two distinct
involutions `q, q' ∈ Q` give, by the conjugation hypothesis, the involution `q * q' * q⁻¹ ∈ Q`,
distinct from `q`; it must equal `q'`, forcing `q` and `q'` to commute, which is impossible in a
group of order `6` (`Work.CORE3.NoKleinFourOfCardSix`).
-/

namespace Work.CORE3

theorem OrderSixNoFiveSubset (H : Type) [Group H] [Finite H] (hcard : Nat.card H = 6)
    (hnab : ¬ IsMulCommutative H) (Q : Set H) (hQcard : Q.ncard = 5) (hQ1 : (1 : H) ∈ Q)
    (hQinv : ∀ q ∈ Q, q⁻¹ ∈ Q)
    (hQconj : ∀ q ∈ Q, q * q = 1 → ∀ r ∈ Q, q * r * q⁻¹ ∈ Q) : False := by
  classical
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 (by rw [hcard]; norm_num)
  set P : Subgroup H := Subgroup.zpowers a with hPdef
  have ha3 : a ^ 3 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  have ha2ne1 : a ^ 2 ≠ 1 := by
    intro h
    have : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [ha] at this; omega
  have ha2ne : a ^ 2 ≠ a := by
    intro h
    have h2 : a * a = a * 1 := by rw [← pow_two, h, mul_one]
    exact ha1 (mul_left_cancel h2)
  have hcard3 : ({1, a, a ^ 2} : Set H).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, a, a^2, ha1.symm, ha2ne1.symm, (fun h => ha2ne h.symm), rfl⟩
  have hsub : ({1, a, a ^ 2} : Set H) ⊆ (P : Set H) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact P.one_mem
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    · exact Subgroup.mem_zpowers_iff.mpr ⟨2, by simp⟩
  have hPcardNat : Nat.card ↥P = 3 := by rw [hPdef, Nat.card_zpowers, ha]
  have hPcard : (P : Set H).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]; exact hPcardNat
  have hPeq : (P : Set H) = ({1, a, a ^ 2} : Set H) := by
    symm
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hPcard, hcard3])
  have hmemP : ∀ y : H, y ∈ P ↔ y = 1 ∨ y = a ∨ y = a ^ 2 := by
    intro y
    show y ∈ (P : Set H) ↔ _
    rw [hPeq]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hPidx : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hPcardNat, hcard] at h
    omega
  have hsq : ∀ x : H, x * x ∈ P := fun x => Subgroup.mul_self_mem_of_index_two hPidx x
  have ha_sq : a * a ^ 2 = 1 := by
    rw [← pow_succ']
    simpa using ha3
  have ha_inv : a⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right ha_sq
  have ha2_inv : (a ^ 2)⁻¹ = a := inv_eq_of_mul_eq_one_left ha_sq
  have ha2_cube : (a ^ 2) ^ 3 = 1 := by
    calc (a ^ 2) ^ 3 = (a ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [ha3, one_pow]
  have ha2_order : orderOf (a ^ 2) = 3 := by rw [← ha_inv, orderOf_inv, ha]
  have horder3_mem : ∀ x : H, orderOf x = 3 → x ∈ P := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
    have hxxP : x * x ∈ P := hsq x
    have hxx : (x * x)⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_two, ← pow_succ]
      simpa using hx3
    rw [← hxx]
    exact P.inv_mem hxxP
  have horder3_of_mem : ∀ x ∈ P, x ≠ 1 → orderOf x = 3 := by
    intro x hx hx1
    rcases (hmemP x).mp hx with h | h | h
    · exact absurd h hx1
    · rw [h]; exact ha
    · rw [h]; exact ha2_order
  have hnotP : ∀ x : H, x ∉ P → x * x = 1 := by
    intro x hxP
    by_contra hne
    have hxxP : x * x ∈ P := hsq x
    have hxx3 : (x * x) ^ 3 = 1 := by
      rcases (hmemP (x * x)).mp hxxP with h | h | h
      · exact absurd h hne
      · rw [h]; exact ha3
      · rw [h]; exact ha2_cube
    have hx6 : x ^ 6 = 1 := by
      have h1 : (x * x) ^ 3 = x ^ 6 := by rw [← pow_two, ← pow_mul]
      rwa [← h1]
    have hx3ne : x ^ 3 ≠ 1 := by
      intro h3
      have ho : orderOf x = 3 := orderOf_eq_prime h3 (by
        intro h1; rw [h1] at hxP; exact hxP P.one_mem)
      exact hxP (horder3_mem x ho)
    have hdvd : orderOf x ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hx6
    have hne1 : orderOf x ≠ 1 := by
      intro h
      exact hxP (by rw [orderOf_eq_one_iff.mp h]; exact P.one_mem)
    have hne2 : orderOf x ≠ 2 := by
      intro h
      have hd : orderOf x ∣ 2 := by rw [h]
      have h2 : x * x = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hd
      exact hne h2
    have hne3 : orderOf x ≠ 3 := by
      intro h; exact hx3ne (by rw [← h, pow_orderOf_eq_one])
    have hcases : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 6 := by
      have hpos : 0 < orderOf x := orderOf_pos x
      have hle : orderOf x ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases orderOf x
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact absurd hdvd (by norm_num)
      · exact absurd hdvd (by norm_num)
      · exact Or.inr (Or.inr (Or.inr rfl))
    rcases hcases with h | h | h | h
    · exact absurd h hne1
    · exact absurd h hne2
    · exact absurd h hne3
    · exact absurd h (orderOf_ne_six_of_not_isMulCommutative hcard hnab x)
  have hInv_eq : ∀ x : H, (x * x = 1 ∧ x ≠ 1) ↔ x ∉ P := by
    intro x
    constructor
    · rintro ⟨hx2, hx1⟩ hxP
      have ho : orderOf x = 3 := horder3_of_mem x hxP hx1
      have hx3 : x ^ 3 = 1 := by rw [← ho, pow_orderOf_eq_one]
      have hone : x = 1 := by
        have h1 : x ^ 3 = x := by rw [pow_succ, pow_two, hx2, one_mul]
        rw [h1] at hx3; exact hx3
      exact hx1 hone
    · intro hxP
      exact ⟨hnotP x hxP, fun h => hxP (by rw [h]; exact P.one_mem)⟩
  have hcompl : ((Set.univ : Set H) \ Q).ncard = 1 := by
    rw [Set.ncard_sdiff (Set.subset_univ Q), Set.ncard_univ, hcard, hQcard]
  have haQ : a ∈ Q := by
    by_contra haQ
    have ha2Q' : a ^ 2 ∉ Q := by
      intro h
      have h' : (a ^ 2)⁻¹ ∈ Q := hQinv (a ^ 2) h
      rw [ha2_inv] at h'
      exact haQ h'
    have hsub2 : ({a, a ^ 2} : Set H) ⊆ (Set.univ \ Q) := by
      rintro y (hy : y ∈ ({a, a ^ 2} : Set H))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨Set.mem_univ _, haQ⟩
      · exact ⟨Set.mem_univ _, ha2Q'⟩
    have h2 : ({a, a ^ 2} : Set H).ncard = 2 := Set.ncard_pair (ha2ne.symm)
    have hle := Set.ncard_le_ncard hsub2
    rw [h2, hcompl] at hle
    omega
  have ha2Q : a ^ 2 ∈ Q := by
    have h := hQinv a haQ
    rwa [ha_inv] at h
  have hPQ : (P : Set H) ⊆ Q := by
    intro x hx
    rcases (hmemP x).mp hx with h | h | h
    · rw [h]; exact hQ1
    · rw [h]; exact haQ
    · rw [h]; exact ha2Q
  have hQP : Q ∩ (P : Set H) = P := Set.inter_eq_right.mpr hPQ
  set Inv : Set H := {x : H | x * x = 1 ∧ x ≠ 1}
  have hQdecomp : Q = (Q ∩ (P : Set H)) ∪ (Q ∩ Inv) := by
    ext x; constructor
    · intro hx
      by_cases hxP : x ∈ P
      · exact Or.inl ⟨hx, hxP⟩
      · exact Or.inr ⟨hx, (hInv_eq x).mpr hxP⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint (Q ∩ (P : Set H)) (Q ∩ Inv) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact ((hInv_eq x).mp hx'.2) hx.2
  have hQInv_card : (Q ∩ Inv).ncard = 2 := by
    have hsum := Set.ncard_union_eq (s := Q ∩ (P : Set H)) (t := Q ∩ Inv) hdisj
    rw [← hQdecomp, hQcard, hQP, hPcard] at hsum
    omega
  obtain ⟨q, q', hqq', hQInv_eq⟩ := Set.ncard_eq_two.mp hQInv_card
  have hqI : q ∈ Q ∩ Inv := by rw [hQInv_eq]; exact Or.inl rfl
  have hq'I : q' ∈ Q ∩ Inv := by rw [hQInv_eq]; exact Or.inr rfl
  have hqQ : q ∈ Q := hqI.1
  have hq2 : q * q = 1 := hqI.2.1
  have hq1 : q ≠ 1 := hqI.2.2
  have hq'Q : q' ∈ Q := hq'I.1
  have hq'2 : q' * q' = 1 := hq'I.2.1
  have hq'1 : q' ≠ 1 := hq'I.2.2
  set z : H := q * q' * q⁻¹ with hzdef
  have hzQ : z ∈ Q := by rw [hzdef]; exact hQconj q hqQ hq2 q' hq'Q
  have hzz1 : z * z = 1 := by
    rw [hzdef]
    calc (q * q' * q⁻¹) * (q * q' * q⁻¹) = q * (q' * q') * q⁻¹ := by group
      _ = 1 := by rw [hq'2, mul_one, mul_inv_cancel]
  have hz1 : z ≠ 1 := by
    intro h
    rw [hzdef] at h
    have h2 : q' = 1 := by
      have hc := congrArg (fun w => q⁻¹ * w * q) h
      rw [show q⁻¹ * (q * q' * q⁻¹) * q = q' from by group,
          show q⁻¹ * 1 * q = (1 : H) from by group] at hc
      exact hc
    exact hq'1 h2
  have hzm : z ∈ ({q, q'} : Set H) := by
    rw [← hQInv_eq]
    exact ⟨hzQ, hzz1, hz1⟩
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hzm
  rcases hzm with hzq | hzq'
  · rw [hzdef] at hzq
    have h4 : q' = q := by
      have hc := congrArg (fun w => q⁻¹ * w) hzq
      rw [show q⁻¹ * (q * q' * q⁻¹) = q' * q⁻¹ from by group,
          show q⁻¹ * q = (1 : H) from by group] at hc
      have h5 := congrArg (fun w => w * q) hc
      rw [show q' * q⁻¹ * q = q' from by group,
          show (1 : H) * q = q from by group] at h5
      exact h5
    exact hqq' h4.symm
  · rw [hzdef] at hzq'
    have hcomm : q * q' = q' * q := by
      have hc := congrArg (fun w => w * q) hzq'
      rw [show q * q' * q⁻¹ * q = q * q' from by group] at hc
      exact hc
    exact NoKleinFourOfCardSix hcard hq2 hq'2 hcomm hq1 hq'1 hqq'

end Work.CORE3
