/-
Auxiliary lemmas for `Submission.Work.BG.l42Ngrid` (Bender--Glauberman 1981, Lemma 4.2, `n = 2`).

These are the two remaining structural ingredients of the `n = 2` case, proved here so that
`l42Ngrid.lean` is complete:

* `l42NgridAuxStruct`  -- when the dihedral Sylow `2`-subgroup has order `4`, it is the Klein
  four-group `{1, t, t₁, t₂}` with `t₂ = t t₁`;
* `l42NgridAuxParity`  -- `N_G(S)/C_G(S)` has odd order for an abelian Sylow `2`-subgroup `S`
  (`l42NgridAuxMaintained` is the auxiliary index-two computation it uses);
* `l42NgridAuxFixSq`   -- an element of `N_G(S)` fixing a non-identity element of `S` squares
  into `C_G(S)`.
-/
import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.S_le_H

open Subgroup

set_option linter.style.haveILetI false

namespace Work.BG

/-- The normalizer of `S` normalizes `C_G(S)`: for `z ∈ N_G(S)` with `z ^ 2 ∈ C_G(S)` every element
of `⟨C_G(S), z⟩` which is not in `C_G(S)` satisfies `b * z ∈ C_G(S)`. -/
theorem l42NgridAuxMaintained {G : Type} [Group G] (S : Sylow 2 G) {z : G}
    (hzN : z ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hz2 : z ^ 2 ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    ∀ b ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ⊔ Subgroup.zpowers z,
      b * z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∨
        b ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ((S : Subgroup G) : Set G) with hC
  have hzw : ∀ w ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∀ c ∈ C, w * c * w⁻¹ ∈ C := by
    intro w hw c hc
    rw [hC] at hc ⊢
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hw' : ∀ h : G, h ∈ (S : Subgroup G) ↔ w * h * w⁻¹ ∈ (S : Subgroup G) := by
      rw [Subgroup.mem_normalizer_iff] at hw
      exact hw
    have hwy : w⁻¹ * y * w ∈ (S : Subgroup G) :=
      (hw' (w⁻¹ * y * w)).mpr (by rw [show w * (w⁻¹ * y * w) * w⁻¹ = y from by group]; exact hy)
    calc y * (w * c * w⁻¹) = w * ((w⁻¹ * y * w) * c) * w⁻¹ := by group
      _ = w * (c * (w⁻¹ * y * w)) * w⁻¹ := by rw [hc (w⁻¹ * y * w) hwy]
      _ = (w * c * w⁻¹) * y := by group
  have hinv : ∀ w ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∀ c ∈ C, w⁻¹ * c * w ∈ C := by
    intro w hw c hc
    have h := hzw w⁻¹ (Subgroup.inv_mem _ hw) c hc
    rwa [inv_inv] at h
  have hz2C : z * z ∈ C := by rw [hC, ← pow_two]; exact hz2
  have hz2n : z⁻¹ * z⁻¹ ∈ C := by
    have h : z⁻¹ * z⁻¹ = (z * z)⁻¹ := by rw [mul_inv_rev]
    rw [h]; exact C.inv_mem hz2C
  let L : Subgroup G :=
    { carrier := {b : G | b ∈ C ∨ b * z ∈ C},
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (C.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact C.mul_mem ha hb)
        · refine Or.inr ?_
          have h1 : z⁻¹ * b * z ∈ C := hinv z hzN b hb
          rw [show a * b * z = (a * z) * (z⁻¹ * b * z) from by group]
          exact C.mul_mem ha h1
        · refine Or.inl ?_
          have h4 : z⁻¹ * (b * z) * z ∈ C := hinv z hzN (b * z) hb
          rw [show a * b = (a * z) * ((z⁻¹ * (b * z) * z) * (z⁻¹ * z⁻¹)) from by group]
          exact C.mul_mem ha (C.mul_mem h4 hz2n)
      one_mem' := Or.inl C.one_mem,
      inv_mem' := by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl (C.inv_mem ha)
        · refine Or.inr ?_
          have h3 : z * (a * z)⁻¹ * z⁻¹ ∈ C := hzw z hzN (a * z)⁻¹ (C.inv_mem ha)
          rw [show a⁻¹ * z = (z * (a * z)⁻¹ * z⁻¹) * (z * z) from by group]
          exact C.mul_mem h3 hz2C }
  have hCL : C ≤ L := fun b hb => Or.inl hb
  have hzL : z ∈ L := by
    refine Or.inr ?_
    rw [hC]
    show z * z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)
    exact hz2C
  have hML : C ⊔ Subgroup.zpowers z ≤ L := sup_le hCL (Subgroup.zpowers_le.mpr hzL)
  intro b hb
  rcases hML hb with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- `N_G(S)/C_G(S)` has odd order for an abelian Sylow `2`-subgroup `S`: an element of the
normalizer whose square centralizes `S` already centralizes `S`. -/
theorem l42NgridAuxParity {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (hab : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x)
    {z : G} (hzN : z ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hz2 : z ^ 2 ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ((S : Subgroup G) : Set G) with hC
  by_contra hzC
  have hSC : (S : Subgroup G) ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hab x hx y hy).symm
  set M : Subgroup G := C ⊔ Subgroup.zpowers z with hM
  have hCM : C ≤ M := by rw [hM]; exact le_sup_of_le_left le_rfl
  have hSM : (S : Subgroup G) ≤ M := le_trans hSC hCM
  have hzM : z ∈ M := by
    rw [hM]
    exact (le_sup_right : Subgroup.zpowers z ≤ C ⊔ Subgroup.zpowers z) (Subgroup.mem_zpowers z)
  have hri : C.relIndex M = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨z, hzM, hzC, ?_⟩
    intro b hb
    exact l42NgridAuxMaintained S hzN hz2 b (hM ▸ hb)
  have hcardM : Nat.card ↥M = 2 * Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card C M
    rw [hri] at h
    have hinf : C ⊓ M = C := inf_eq_left.mpr hCM
    rw [hinf] at h
    exact h.symm
  have hCardC : Nat.card ↥C = Nat.card (S : Subgroup G) * S.relIndex C := by
    have h := Subgroup.relIndex_mul_card (S : Subgroup G) C
    have hinf : (S : Subgroup G) ⊓ C = (S : Subgroup G) := inf_eq_left.mpr hSC
    rw [hinf, mul_comm] at h
    exact h.symm
  have hCardM : Nat.card ↥M = Nat.card (S : Subgroup G) * S.relIndex M := by
    have h := Subgroup.relIndex_mul_card (S : Subgroup G) M
    have hinf : (S : Subgroup G) ⊓ M = (S : Subgroup G) := inf_eq_left.mpr hSM
    rw [hinf, mul_comm] at h
    exact h.symm
  have hoddC : ¬ 2 ∣ S.relIndex C := by
    haveI : (S.subtype hSC).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
    have h : (S.subtype hSC : Subgroup ↥C).index = S.relIndex C := by
      rw [Sylow.coe_subtype]
      rfl
    rw [← h]
    exact (S.subtype hSC).not_dvd_index
  have hoddM : ¬ 2 ∣ S.relIndex M := by
    haveI : (S.subtype hSM).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
    have h : (S.subtype hSM : Subgroup ↥M).index = S.relIndex M := by
      rw [Sylow.coe_subtype]
      rfl
    rw [← h]
    exact (S.subtype hSM).not_dvd_index
  have hSpos : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
  have hji : S.relIndex M = 2 * S.relIndex C := by
    have h1 : Nat.card (S : Subgroup G) * S.relIndex M
        = Nat.card (S : Subgroup G) * (2 * S.relIndex C) := by
      calc Nat.card (S : Subgroup G) * S.relIndex M = Nat.card ↥M := hCardM.symm
        _ = 2 * Nat.card ↥C := hcardM
        _ = 2 * (Nat.card (S : Subgroup G) * S.relIndex C) := by rw [hCardC]
        _ = Nat.card (S : Subgroup G) * (2 * S.relIndex C) := by ring
    exact Nat.mul_left_cancel hSpos h1
  exact hoddM ⟨S.relIndex C, hji⟩

/-- When the dihedral Sylow `2`-subgroup of a `BGData` has order `4`, it is the Klein four-group
`{1, t, t₁, t₂}` with `t₂ = t * t₁`. -/
theorem l42NgridAuxStruct {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    Nat.card ↥(D.S : Subgroup G) = 4 ∧
    (∀ σ : ↥(D.S : Subgroup G), σ = 1 ∨ (σ : G) = D.t ∨ (σ : G) = D.t1 ∨ (σ : G) = D.t2) ∧
    (∀ σ : ↥(D.S : Subgroup G), σ ^ 2 = 1) ∧
    (∀ x ∈ (D.S : Subgroup G), ∀ y ∈ (D.S : Subgroup G), x * y = y * x) ∧
    D.t * D.t1 = D.t2 ∧ D.t * D.t2 = D.t1 ∧ D.t1 * D.t2 = D.t ∧ D.t1 ≠ D.t2 := by
  classical
  obtain ⟨e⟩ := D.dih
  have hcard : Nat.card ↥(D.S : Subgroup G) = 4 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn]
  have hexp : Monoid.exponent (DihedralGroup D.n) = 2 := by
    rw [DihedralGroup.exponent, hn]
    decide
  have hsq2 : ∀ d : DihedralGroup D.n, d ^ 2 = 1 := by
    intro d
    have h := Monoid.pow_exponent_eq_one d
    rwa [hexp] at h
  have hsq : ∀ σ : ↥(D.S : Subgroup G), σ ^ 2 = 1 := by
    intro σ
    refine e.injective ?_
    rw [map_pow, map_one, hsq2]
  have hcomm : ∀ a b : ↥(D.S : Subgroup G), a * b = b * a := by
    intro a b
    have ha : a * a = 1 := by rw [← pow_two]; exact hsq a
    have hb : b * b = 1 := by rw [← pow_two]; exact hsq b
    have hab : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact hsq (a * b)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right ha]
  have ht_ne_one : D.t ≠ 1 := by
    intro h
    have h2 := D.t_order
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have ht1_ne_one : D.t1 ≠ 1 := by
    intro h
    have h2 := D.t1_order
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have ht2_ne_one : D.t2 ≠ 1 := by
    intro h
    have h2 := D.t2_order
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hsqS : ∀ z ∈ (D.S : Subgroup G), z * z = 1 := by
    intro z hz
    have h := congrArg Subtype.val (hsq ⟨z, hz⟩)
    simpa [pow_two] using h
  -- `t1 ≠ t2`
  have hS0le : D.S0 ≤ (D.S : Subgroup G) := D.S0_le
  have ht1_ne_t2 : D.t1 ≠ D.t2 := by
    intro h
    have h2 : D.t1 * D.t2 = 1 := by
      rw [h]
      exact hsqS D.t2 D.t2_mem
    have h3 : (D.t : G) ∈ Subgroup.zpowers (D.t1 * D.t2) := by
      rw [← D.gen]; exact D.t_mem
    rw [h2] at h3
    have h4 : D.t = 1 := by simpa using h3
    exact ht_ne_one h4
  -- `S₀ = {1, t}`
  have hS0mem : ∀ x ∈ D.S0, x = 1 ∨ x = D.t := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      have hxS : x ∈ (D.S : Subgroup G) := hS0le hx
      have hx2 : orderOf x = 2 := by
        have hdvd : orderOf x ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsqS x hxS)
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1
        · exact h
      haveI : IsCyclic ↥D.S0 := D.S0_cyclic
      have heq := eq_of_orderOf_eq_two_of_isCyclic
        (a := (⟨x, hx⟩ : ↥D.S0)) (b := (⟨D.t, D.t_mem⟩ : ↥D.S0))
        (by rw [Subgroup.orderOf_mk]; exact hx2) (by rw [Subgroup.orderOf_mk]; exact D.t_order)
      exact congrArg Subtype.val heq
  have ht_ne_t1 : D.t ≠ D.t1 := fun h => D.t1_nmem (h ▸ D.t_mem)
  have ht_ne_t2 : D.t ≠ D.t2 := fun h => D.t2_nmem (h ▸ D.t_mem)
  -- the four elements exhaust `S`
  have htS : D.t ∈ (D.S : Subgroup G) := hS0le D.t_mem
  have ht1S : D.t1 ∈ (D.S : Subgroup G) := D.t1_mem
  have ht2S : D.t2 ∈ (D.S : Subgroup G) := D.t2_mem
  haveI : Fintype ↥(D.S : Subgroup G) := Fintype.ofFinite _
  have hdistinct : ({1, D.t, D.t1, D.t2} : Finset G).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨1, D.t, D.t1, D.t2, ht_ne_one.symm, ht1_ne_one.symm, ht2_ne_one.symm,
      ht_ne_t1, ht_ne_t2, ht1_ne_t2, rfl⟩
  have himg : ((Finset.univ : Finset ↥(D.S : Subgroup G)).image Subtype.val).card = 4 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    exact hcard
  have hsub : ({1, D.t, D.t1, D.t2} : Finset G)
      ⊆ (Finset.univ : Finset ↥(D.S : Subgroup G)).image Subtype.val := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [hz]⟩
    · exact Finset.mem_image.mpr ⟨⟨D.t, htS⟩, Finset.mem_univ _, by simp [hz]⟩
    · exact Finset.mem_image.mpr ⟨⟨D.t1, ht1S⟩, Finset.mem_univ _, by simp [hz]⟩
    · exact Finset.mem_image.mpr ⟨⟨D.t2, ht2S⟩, Finset.mem_univ _, by simp [hz]⟩
  have heq : ({1, D.t, D.t1, D.t2} : Finset G)
      = (Finset.univ : Finset ↥(D.S : Subgroup G)).image Subtype.val :=
    Finset.eq_of_subset_of_card_le hsub (by rw [himg, hdistinct])
  have hmem : ∀ σ : ↥(D.S : Subgroup G),
      σ = 1 ∨ (σ : G) = D.t ∨ (σ : G) = D.t1 ∨ (σ : G) = D.t2 := by
    intro σ
    have h : (σ : G) ∈ ({1, D.t, D.t1, D.t2} : Finset G) := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  -- products
  have hprod : ∀ {p q : G}, p ∈ (D.S : Subgroup G) → q ∈ (D.S : Subgroup G) →
      ¬ (p * q = 1) → ¬ (p * q = p) → ¬ (p * q = q) →
      p * q = D.t ∨ p * q = D.t1 ∨ p * q = D.t2 := by
    intro p q hp hq h1 hp' hq'
    have hmem' : p * q ∈ (D.S : Subgroup G) := mul_mem hp hq
    rcases hmem ⟨p * q, hmem'⟩ with h | h | h | h
    · exact absurd (Subtype.ext_iff.mp h) h1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have ht_t1 : D.t * D.t1 = D.t2 := by
    have h1 : ¬ (D.t * D.t1 = 1) := by
      intro h
      have h3 : D.t1 = D.t⁻¹ := by
        calc D.t1 = D.t⁻¹ * (D.t * D.t1) := by group
          _ = D.t⁻¹ * 1 := by rw [h]
          _ = D.t⁻¹ := by rw [mul_one]
      exact ht_ne_t1 ((h3.trans (inv_eq_of_mul_eq_one_right (hsqS D.t htS))).symm)
    have h2 : ¬ (D.t * D.t1 = D.t) := by
      intro h
      exact ht1_ne_one (mul_left_cancel (by rw [h, mul_one]))
    have h3 : ¬ (D.t * D.t1 = D.t1) := by
      intro h
      exact ht_ne_one (mul_right_cancel (by rw [h, one_mul]))
    rcases hprod htS ht1S h1 h2 h3 with h | h | h
    · exact absurd h h2
    · exact absurd h h3
    · exact h
  have ht_t2 : D.t * D.t2 = D.t1 := by
    have h1 : ¬ (D.t * D.t2 = 1) := by
      intro h
      have h3 : D.t2 = D.t⁻¹ := by
        calc D.t2 = D.t⁻¹ * (D.t * D.t2) := by group
          _ = D.t⁻¹ * 1 := by rw [h]
          _ = D.t⁻¹ := by rw [mul_one]
      exact ht_ne_t2 ((h3.trans (inv_eq_of_mul_eq_one_right (hsqS D.t htS))).symm)
    have h2 : ¬ (D.t * D.t2 = D.t) := by
      intro h
      exact ht2_ne_one (mul_left_cancel (by rw [h, mul_one]))
    have h3 : ¬ (D.t * D.t2 = D.t2) := by
      intro h
      exact ht_ne_one (mul_right_cancel (by rw [h, one_mul]))
    rcases hprod htS ht2S h1 h2 h3 with h | h | h
    · exact absurd h h2
    · exact h
    · exact absurd h h3
  have ht1_t2' : D.t1 * D.t2 = D.t := by
    have h1 : ¬ (D.t1 * D.t2 = 1) := by
      intro h
      have h3 : D.t2 = D.t1⁻¹ := by
        calc D.t2 = D.t1⁻¹ * (D.t1 * D.t2) := by group
          _ = D.t1⁻¹ * 1 := by rw [h]
          _ = D.t1⁻¹ := by rw [mul_one]
      exact ht1_ne_t2 ((h3.trans (inv_eq_of_mul_eq_one_right (hsqS D.t1 ht1S))).symm)
    have h2 : ¬ (D.t1 * D.t2 = D.t1) := by
      intro h
      exact ht2_ne_one (mul_left_cancel (by rw [h, mul_one]))
    have h3 : ¬ (D.t1 * D.t2 = D.t2) := by
      intro h
      exact ht1_ne_one (mul_right_cancel (by rw [h, one_mul]))
    rcases hprod ht1S ht2S h1 h2 h3 with h | h | h
    · exact h
    · exact absurd h h2
    · exact absurd h h3
  have hcomm' : ∀ x ∈ (D.S : Subgroup G), ∀ y ∈ (D.S : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  exact ⟨hcard, hmem, hsq, hcomm', ht_t1, ht_t2, ht1_t2', ht1_ne_t2⟩

/-- An element of `N_G(S)` fixing a non-identity element of the Klein four-group `S` squares into
`C_G(S)`. -/
theorem l42NgridAuxFixSq {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2)
    {y : G} (hy : y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    {x : G} (hx : x ∈ (D.S : Subgroup G)) (hx1 : x ≠ 1) (hyx : y * x * y⁻¹ = x) :
    y ^ 2 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
  classical
  obtain ⟨hcard, hmem, hsq, hcomm, ht_t1, ht_t2, ht1_t2, ht1ne_t2⟩ := l42NgridAuxStruct D hn
  set S : Subgroup G := (D.S : Subgroup G) with hSdef
  have htS : D.t ∈ S := by rw [hSdef]; exact D.S0_le D.t_mem
  have ht1S : D.t1 ∈ S := by rw [hSdef]; exact D.t1_mem
  have ht2S : D.t2 ∈ S := by rw [hSdef]; exact D.t2_mem
  have ht_ne_one : D.t ≠ 1 := by
    intro h; have h2 := D.t_order; rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have ht1_ne_one : D.t1 ≠ 1 := by
    intro h; have h2 := D.t1_order; rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have ht2_ne_one : D.t2 ≠ 1 := by
    intro h; have h2 := D.t2_order; rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have ht_ne_t1 : D.t ≠ D.t1 := fun h => D.t1_nmem (h ▸ D.t_mem)
  have ht_ne_t2 : D.t ≠ D.t2 := fun h => D.t2_nmem (h ▸ D.t_mem)
  have hSmem : ∀ z : G, z ∈ S ↔ z = 1 ∨ z = D.t ∨ z = D.t1 ∨ z = D.t2 := by
    intro z
    constructor
    · intro hz
      have hz' : z ∈ (D.S : Subgroup G) := hSdef ▸ hz
      rcases hmem ⟨z, hz'⟩ with h | h | h | h
      · exact Or.inl (by simpa using Subtype.ext_iff.mp h)
      · exact Or.inr (Or.inl (by simpa using h))
      · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
      · exact Or.inr (Or.inr (Or.inr (by simpa using h)))
    · rintro (h | h | h | h)
      · rw [h]; exact S.one_mem
      · rw [h]; exact htS
      · rw [h]; exact ht1S
      · rw [h]; exact ht2S
  have hy' := hy
  rw [Subgroup.mem_normalizer_iff] at hy'
  have hpres : ∀ z ∈ S, y * z * y⁻¹ ∈ S := by
    intro z hz
    have hz' : z ∈ (D.S : Subgroup G) := hSdef ▸ hz
    have hres : y * z * y⁻¹ ∈ (D.S : Subgroup G) := (hy' z).mp hz'
    exact hSdef.symm ▸ hres
  have hinj : ∀ a b : G, y * a * y⁻¹ = y * b * y⁻¹ → a = b :=
    fun a b h => mul_left_cancel (mul_right_cancel h)
  have hnotone : ∀ w ∈ S, w ≠ 1 → y * w * y⁻¹ ≠ 1 := by
    intro w hw hw1 h
    have h2 : w = 1 := by
      have h3 : y⁻¹ * (y * w * y⁻¹) * y = w := by group
      rw [h] at h3
      simpa using h3.symm
    exact hw1 h2
  have hxcase : x = D.t ∨ x = D.t1 ∨ x = D.t2 := by
    rcases (hSmem x).mp (hSdef.symm ▸ hx) with h | h | h | h
    · exact absurd h hx1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- a two-element set permuted by conjugation has square the identity on it
  have pair_lemma : ∀ {u v : G}, u ≠ v → (y * u * y⁻¹ = u ∨ y * u * y⁻¹ = v) →
      (y * v * y⁻¹ = u ∨ y * v * y⁻¹ = v) →
      y ^ 2 * u * (y ^ 2)⁻¹ = u ∧ y ^ 2 * v * (y ^ 2)⁻¹ = v := by
    intro u v huv hu hv
    have hsq' : ∀ w : G, y ^ 2 * w * (y ^ 2)⁻¹ = y * (y * w * y⁻¹) * y⁻¹ := by
      intro w
      rw [pow_two, mul_inv_rev]
      group
    constructor
    · rcases hu with h | h
      · rw [hsq', h, h]
      · rw [hsq', h]
        rcases hv with h2 | h2
        · exact h2
        · exact absurd (hinj u v (by rw [h, h2])) huv
    · rcases hv with h | h
      · rw [hsq', h]
        rcases hu with h2 | h2
        · exact absurd (hinj v u (by rw [h, h2])) (Ne.symm huv)
        · exact h2
      · rw [hsq', h, h]
  have hgoal : ∀ z ∈ S, y ^ 2 * z * (y ^ 2)⁻¹ = z := by
    intro z hz
    have hxfix : y ^ 2 * x * (y ^ 2)⁻¹ = x := by
      have hsqx : y ^ 2 * x * (y ^ 2)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by
        rw [pow_two, mul_inv_rev]
        group
      rw [hsqx, hyx, hyx]
    rcases hxcase with hx' | hx' | hx'
    · subst hx'
      have hu : y * D.t1 * y⁻¹ = D.t1 ∨ y * D.t1 * y⁻¹ = D.t2 := by
        have hm : y * D.t1 * y⁻¹ ∈ S := hpres D.t1 ht1S
        have h2 : y * D.t1 * y⁻¹ ≠ D.t := by
          intro h
          exact ht_ne_t1 (hinj D.t1 D.t (by rw [h, hyx])).symm
        rcases (hSmem _).mp hm with h | h | h | h
        · exact absurd h (hnotone D.t1 ht1S ht1_ne_one)
        · exact absurd h h2
        · exact Or.inl h
        · exact Or.inr h
      have hv : y * D.t2 * y⁻¹ = D.t1 ∨ y * D.t2 * y⁻¹ = D.t2 := by
        have hm : y * D.t2 * y⁻¹ ∈ S := hpres D.t2 ht2S
        have h2 : y * D.t2 * y⁻¹ ≠ D.t := by
          intro h
          exact ht_ne_t2 (hinj D.t2 D.t (by rw [h, hyx])).symm
        rcases (hSmem _).mp hm with h | h | h | h
        · exact absurd h (hnotone D.t2 ht2S ht2_ne_one)
        · exact absurd h h2
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨h1, h2⟩ := pair_lemma ht1ne_t2 hu hv
      rcases (hSmem z).mp hz with h | h | h | h
      · rw [h]; group
      · rw [h]; exact hxfix
      · rw [h]; exact h1
      · rw [h]; exact h2
    · subst hx'
      have hu : y * D.t * y⁻¹ = D.t ∨ y * D.t * y⁻¹ = D.t2 := by
        have hm : y * D.t * y⁻¹ ∈ S := hpres D.t htS
        have h2 : y * D.t * y⁻¹ ≠ D.t1 := by
          intro h
          exact ht_ne_t1 (hinj D.t D.t1 (by rw [h, hyx]))
        rcases (hSmem _).mp hm with h | h | h | h
        · exact absurd h (hnotone D.t htS ht_ne_one)
        · exact Or.inl h
        · exact absurd h h2
        · exact Or.inr h
      have hv : y * D.t2 * y⁻¹ = D.t ∨ y * D.t2 * y⁻¹ = D.t2 := by
        have hm : y * D.t2 * y⁻¹ ∈ S := hpres D.t2 ht2S
        have h2 : y * D.t2 * y⁻¹ ≠ D.t1 := by
          intro h
          exact ht1ne_t2 (hinj D.t2 D.t1 (by rw [h, hyx])).symm
        rcases (hSmem _).mp hm with h | h | h | h
        · exact absurd h (hnotone D.t2 ht2S ht2_ne_one)
        · exact Or.inl h
        · exact absurd h h2
        · exact Or.inr h
      obtain ⟨h1, h2⟩ := pair_lemma ht_ne_t2 hu hv
      rcases (hSmem z).mp hz with h | h | h | h
      · rw [h]; group
      · rw [h]; exact h1
      · rw [h]; exact hxfix
      · rw [h]; exact h2
    · subst hx'
      have hu : y * D.t * y⁻¹ = D.t ∨ y * D.t * y⁻¹ = D.t1 := by
        have hm : y * D.t * y⁻¹ ∈ S := hpres D.t htS
        have h2 : y * D.t * y⁻¹ ≠ D.t2 := by
          intro h
          exact ht_ne_t2 (hinj D.t D.t2 (by rw [h, hyx]))
        rcases (hSmem _).mp hm with h | h | h | h
        · exact absurd h (hnotone D.t htS ht_ne_one)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h2
      have hv : y * D.t1 * y⁻¹ = D.t ∨ y * D.t1 * y⁻¹ = D.t1 := by
        have hm : y * D.t1 * y⁻¹ ∈ S := hpres D.t1 ht1S
        have h2 : y * D.t1 * y⁻¹ ≠ D.t2 := by
          intro h
          exact ht1ne_t2 (hinj D.t1 D.t2 (by rw [h, hyx]))
        rcases (hSmem _).mp hm with h | h | h | h
        · exact absurd h (hnotone D.t1 ht1S ht1_ne_one)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h2
      obtain ⟨h1, h2⟩ := pair_lemma ht_ne_t1 hu hv
      rcases (hSmem z).mp hz with h | h | h | h
      · rw [h]; group
      · rw [h]; exact h1
      · rw [h]; exact h2
      · rw [h]; exact hxfix
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h := hgoal w (hSdef.symm ▸ hw)
  calc w * y ^ 2 = (y ^ 2 * w * (y ^ 2)⁻¹) * y ^ 2 := by rw [h]
    _ = y ^ 2 * w := by group

end Work.BG
