import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement

namespace Work.NormalComplement.NC4

/-! ## Auxiliary facts about finite groups -/

/-- If `t` maps the subgroup `X` into itself by conjugation (`NormalizedBy t X`), then `t` lies in
the normalizer of `X`.  For finite `X` the conjugation map `X → X` is a bijection, so a one-sided
containment upgrades to an equivalence. -/
lemma mem_normalizer_of_normalizedBy {G : Type*} [Group G] [Finite G] {t : G} {X : Subgroup G}
    (h : Work.NormalComplement.NormalizedBy t X) :
    t ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact h x hx
  · intro hx
    have hle : X.map (MulAut.conj t).toMonoidHom ≤ X := by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      change t * z * t⁻¹ ∈ X
      exact h z hz
    have hcard : Nat.card ↥(X.map (MulAut.conj t).toMonoidHom) = Nat.card ↥X :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have heq : X.map (MulAut.conj t).toMonoidHom = X :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
    have hmem : (MulAut.conj t) x ∈ X.map (MulAut.conj t).toMonoidHom := by
      rw [heq, MulAut.conj_apply]
      exact hx
    rw [Subgroup.mem_map] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : y = x := (MulAut.conj t).injective hyx
    rwa [hyx'] at hy

/-- Let `E` be a finite group whose order is `qa * m` with `qa` coprime to `m`.  If `N₂` is a
normal subgroup of order `m`, then every subgroup `N₁` of order `m` lies in `N₂`. -/
lemma le_of_normal_card_eq {E : Type*} [Group E] [Finite E] {qa m : ℕ}
    (hcard : Nat.card E = qa * m) (hcop : Nat.Coprime qa m)
    {N₁ N₂ : Subgroup E} (h₂ : N₂.Normal)
    (hc₁ : Nat.card ↥N₁ = m) (hc₂ : Nat.card ↥N₂ = m) : N₁ ≤ N₂ := by
  have hprod : Nat.card ↥(N₁ ⊔ N₂) * Nat.card ↥(N₁ ⊓ N₂) = m * m := by
    have hN : N₁ ≤ Subgroup.normalizer (N₂ : Set E) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr h₂]; exact le_top
    have h := Work.NormalComplement.card_sup_mul_card_inf (H := N₂) (K := N₁) hN
    rw [hc₂, hc₁] at h
    rwa [sup_comm N₂ N₁, inf_comm N₂ N₁] at h
  have hdvd_m2 : Nat.card ↥(N₁ ⊔ N₂) ∣ m * m := ⟨_, hprod.symm⟩
  have hdvd_E : Nat.card ↥(N₁ ⊔ N₂) ∣ qa * m := by
    have := Subgroup.card_subgroup_dvd_card (N₁ ⊔ N₂)
    rwa [hcard] at this
  have hcop_d : Nat.Coprime (Nat.card ↥(N₁ ⊔ N₂)) qa := by
    have hqq : Nat.Coprime (m * m) qa := by
      have h : Nat.Coprime (m ^ 2) (qa ^ 1) := (hcop.symm).pow 2 1
      simpa [pow_two, pow_one] using h
    exact Nat.Coprime.of_dvd_left hdvd_m2 hqq
  have hdvd_m : Nat.card ↥(N₁ ⊔ N₂) ∣ m :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop_d hdvd_E
  have hm_dvd : m ∣ Nat.card ↥(N₁ ⊔ N₂) := by
    rw [← hc₂]; exact Subgroup.card_dvd_of_le le_sup_right
  have heq : Nat.card ↥(N₁ ⊔ N₂) = m := Nat.dvd_antisymm hdvd_m hm_dvd
  have hEq : N₂ = N₁ ⊔ N₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [heq, hc₂])
  rw [hEq]; exact le_sup_left

/-- Let `E` be a finite group whose order is `qa * m` with `qa` coprime to `m`.  Two normal
subgroups of order `m` are equal. -/
lemma eq_of_normal_card_eq {E : Type*} [Group E] [Finite E] {qa m : ℕ}
    (hcard : Nat.card E = qa * m) (hcop : Nat.Coprime qa m)
    {N₁ N₂ : Subgroup E} (h₁ : N₁.Normal) (h₂ : N₂.Normal)
    (hc₁ : Nat.card ↥N₁ = m) (hc₂ : Nat.card ↥N₂ = m) : N₁ = N₂ :=
  le_antisymm (le_of_normal_card_eq hcard hcop h₂ hc₁ hc₂)
    (le_of_normal_card_eq hcard hcop h₁ hc₂ hc₁)

/-! ## The `q`-split of a finite nilpotent group -/

/-- A finite nilpotent group is the direct product of its `q`-primary part `S` and its `q'`-part
`T`; both are characteristic, hence invariant under every automorphism. -/
theorem exists_nilpotent_q_split {E : Type*} [Group E] [Finite E]
    (hnil : Group.IsNilpotent E) {q : ℕ} (hq : q.Prime) :
    ∃ S T : Subgroup E, S.Characteristic ∧ T.Characteristic ∧ S.Normal ∧ T.Normal ∧
      IsPGroup q S ∧ ¬ q ∣ Nat.card ↥T ∧ S ⊔ T = ⊤ ∧ S ⊓ T = ⊥ := by
  classical
  haveI : Group.IsNilpotent E := hnil
  haveI : Fact q.Prime := ⟨hq⟩
  set n := Nat.card E with hn_def
  have hn : n ≠ 0 := by rw [hn_def, Nat.card_ne_zero]; exact ⟨⟨1⟩, inferInstance⟩
  set qa := q ^ padicValNat q n with hqa_def
  set m := n.divMaxPow q with hm_def
  have hnm : qa * m = n := by rw [hqa_def, hm_def]; exact Nat.pow_padicValNat_mul_divMaxPow q n
  have hcop : Nat.Coprime qa m := by
    rw [hqa_def, hm_def]
    exact (Nat.Prime.coprime_pow_of_not_dvd hq (Nat.not_dvd_divMaxPow hq.one_lt hn)).symm
  have hqa_pos : 0 < qa := by rw [hqa_def]; exact Nat.pow_pos hq.pos
  obtain ⟨S, hScard, hSnorm⟩ :=
    Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (n := qa)
      (by rw [hqa_def, ← hn_def]; exact pow_padicValNat_dvd)
  obtain ⟨T, hTcard, hTnorm⟩ :=
    Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (n := m)
      (by rw [← hn_def, ← hnm]; exact ⟨qa, Nat.mul_comm qa m⟩)
  have hSP : IsPGroup q S := IsPGroup.of_card (hScard.trans hqa_def)
  have hqT : ¬ q ∣ Nat.card ↥T := by rw [hTcard, hm_def]; exact Nat.not_dvd_divMaxPow hq.one_lt hn
  have hSTinf : S ⊓ T = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hScard, hTcard]; exact hcop)).eq_bot
  have hSTsup : S ⊔ T = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hN : T ≤ Subgroup.normalizer (S : Set E) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hSnorm]; exact le_top
    have hprod := Work.NormalComplement.card_sup_mul_card_inf (H := S) (K := T) hN
    rw [hSTinf, Subgroup.card_bot, mul_one, hScard, hTcard, hnm] at hprod
    exact hprod
  have hSidx : ¬ q ∣ S.index := by
    have h := Subgroup.card_mul_index S
    rw [hScard, ← hn_def, ← hnm] at h
    have hidx : S.index = m := Nat.mul_left_cancel hqa_pos h
    rw [hidx, hm_def]; exact Nat.not_dvd_divMaxPow hq.one_lt hn
  have hSchar : S.Characteristic := by
    haveI : Finite (Sylow q E) := Sylow.finite_of_finiteIndex (default : Sylow q E)
    exact Sylow.characteristic_of_normal (hSP.toSylow hSidx) hSnorm
  have hTchar : T.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro ψ
    exact eq_of_normal_card_eq (hn_def.symm.trans hnm.symm) hcop
      (hTnorm.map ψ.toMonoidHom ψ.surjective) hTnorm
      (by rw [Subgroup.card_map_of_injective ψ.injective, hTcard]) hTcard
  exact ⟨S, T, hSchar, hTchar, hSnorm, hTnorm, hSP, hqT, hSTsup, hSTinf⟩

/-! ## The requested splitting lemma -/

theorem nilpotent_split {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hnil : Group.IsNilpotent ↥E) {t : G} (htE : Work.NormalComplement.NormalizedBy t E)
    {q : ℕ} (hq : q.Prime) :
    ∃ S T : Subgroup G, S ≤ E ∧ T ≤ E ∧ S ⊔ T = E ∧ S ⊓ T = ⊥ ∧
      (∀ s ∈ S, ∀ u ∈ T, s * u = u * s) ∧ E ≤ Subgroup.normalizer (S : Set G) ∧
      Work.NormalComplement.NormalizedBy t S ∧ Work.NormalComplement.NormalizedBy t T ∧
      IsPGroup q S ∧ ¬ q ∣ Nat.card ↥T := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨S₀, T₀, hS₀char, hT₀char, hS₀norm, hT₀norm, hS₀P, hqT₀, hS₀T₀sup, hS₀T₀inf⟩ :=
    exists_nilpotent_q_split hnil hq
  -- `t` acts on `E` by conjugation.
  have htmem : t ∈ Subgroup.normalizer (E : Set G) := mem_normalizer_of_normalizedBy htE
  refine ⟨S₀.map E.subtype, T₀.map E.subtype, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hS₀T₀sup, Subgroup.map_top, Subgroup.range_subtype]
  · obtain ⟨k, hk⟩ := hS₀P.exists_card_eq
    have hcop' : Nat.Coprime (Nat.card ↥S₀) (Nat.card ↥T₀) := by
      rw [hk]
      exact (Nat.Prime.coprime_pow_of_not_dvd hq hqT₀).symm
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [Subgroup.card_map_of_injective E.subtype_injective,
        Subgroup.card_map_of_injective E.subtype_injective]
      exact hcop')).eq_bot
  · intro s hs u hu
    rw [Subgroup.mem_map] at hs hu
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨u', hu', rfl⟩ := hu
    exact ((Subgroup.commute_of_normal_of_disjoint S₀ T₀ hS₀norm hT₀norm
      (disjoint_iff.mpr hS₀T₀inf) s' u' hs' hu').map E.subtype).eq
  · rw [Subgroup.le_normalizer_iff]
    intro e he k hk
    rw [Subgroup.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    refine Subgroup.mem_map.mpr ⟨⟨e, he⟩ * k' * ⟨e, he⟩⁻¹, hS₀norm.conj_mem k' hk' ⟨e, he⟩, ?_⟩
    rfl
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨s', hs', rfl⟩ := hx
    refine Subgroup.mem_map.mpr
      ⟨(Subgroup.normalizerMonoidHom E ⟨t, htmem⟩) s', ?_, ?_⟩
    · rw [← Subgroup.characteristic_iff_map_eq.mp hS₀char (Subgroup.normalizerMonoidHom E ⟨t, htmem⟩)]
      exact Subgroup.mem_map.mpr ⟨s', hs', rfl⟩
    · show (((Subgroup.normalizerMonoidHom E ⟨t, htmem⟩) s' : ↥E) : G) = t * ↑s' * t⁻¹
      simp only [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply,
        MulDistribMulAction.toMulEquiv_apply]
      rfl
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨u', hu', rfl⟩ := hx
    refine Subgroup.mem_map.mpr
      ⟨(Subgroup.normalizerMonoidHom E ⟨t, htmem⟩) u', ?_, ?_⟩
    · rw [← Subgroup.characteristic_iff_map_eq.mp hT₀char (Subgroup.normalizerMonoidHom E ⟨t, htmem⟩)]
      exact Subgroup.mem_map.mpr ⟨u', hu', rfl⟩
    · show (((Subgroup.normalizerMonoidHom E ⟨t, htmem⟩) u' : ↥E) : G) = t * ↑u' * t⁻¹
      simp only [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply,
        MulDistribMulAction.toMulEquiv_apply]
      rfl
  · exact hS₀P.map E.subtype
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hqT₀

end Work.NormalComplement.NC4
