import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.mem_AU_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open scoped Pointwise

noncomputable section

/-- An element `μ` of a subgroup `H` permutes `H` by conjugation. -/
private theorem mmc_map_conj_eq_self_of_mem {G : Type*} [Group G] {H : Subgroup G} {μ : G}
    (hμ : μ ∈ H) : H.map (MulAut.conj μ) = H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hμ hy) (H.inv_mem hμ)
  · intro hx
    refine ⟨μ⁻¹ * x * μ, H.mul_mem (H.mul_mem (H.inv_mem hμ) hx) hμ, ?_⟩
    change μ * (μ⁻¹ * x * μ) * μ⁻¹ = x
    group

/-- Conjugation takes the centralizer of `a` to the centralizer of `μ a μ⁻¹`. -/
private theorem mmc_centralizer_conj_singleton {G : Type*} [Group G] (μ a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj μ) =
      Subgroup.centralizer ({μ * a * μ⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have key : μ * z * μ⁻¹ * (μ * a * μ⁻¹) = μ * (z * a) * μ⁻¹ := by group
    have key2 : μ * a * μ⁻¹ * (μ * z * μ⁻¹) = μ * (a * z) * μ⁻¹ := by group
    change μ * z * μ⁻¹ * (μ * a * μ⁻¹) = μ * a * μ⁻¹ * (μ * z * μ⁻¹)
    rw [key, key2, hz]
  · intro hy
    refine ⟨μ⁻¹ * y * μ, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      have h := congrArg (fun t => μ⁻¹ * t * μ) hy
      simpa [mul_assoc] using h
    · change μ * (μ⁻¹ * y * μ) * μ⁻¹ = y
      group

/-- The cardinality of `H.subgroupOf K` is the cardinality of `H ⊓ K`. -/
private theorem mmc_card_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective K),
    Subgroup.subgroupOf_map_subtype]

/-- An element whose order is coprime to the index of a normal subgroup lies in it. -/
private theorem mmc_mem_of_coprime_index {G : Type*} [Group G]
    (D : Subgroup G) [D.Normal] {x : G} (h : (orderOf x).Coprime D.index) : x ∈ D := by
  have h1 : orderOf (QuotientGroup.mk' D x) ∣ 1 := by
    rw [← h.gcd_eq_one]
    refine Nat.dvd_gcd (orderOf_map_dvd _ x) ?_
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hker : QuotientGroup.mk' D x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hmem : x ∈ (QuotientGroup.mk' D).ker := MonoidHom.mem_ker.mpr hker
  rwa [QuotientGroup.ker_mk'] at hmem

/-- If `A` is a normal subgroup, `A ⊔ B = ⊤` and `A ⊓ B = ⊥`, then `|G| = |A|·|B|`. -/
private theorem mmc_card_eq_card_mul_card_of_sup_eq_top_of_disjoint {G : Type*} [Group G]
    [Finite G] {A B : Subgroup G} [A.Normal] (hsup : A ⊔ B = ⊤) (hdisj : Disjoint A B) :
    Nat.card G = Nat.card ↥A * Nat.card ↥B := by
  have hmul : (A : Set G) * (B : Set G) = Set.univ := by
    ext x
    rw [Set.mem_mul]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hx : x ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top x
    exact Subgroup.mem_sup_of_normal_left.mp hx
  exact (Subgroup.IsComplement.card_mul_card
    (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul)).symm

/-- Feit–Thompson Lemma 9.1 (p. 805), the local computation behind the vanishing statement.
Let `L̂` be tamely imbedded in `X` with `𝔇 ≠ ∅`, let `i` be a supporting index, let `H ∈ 𝔎_i^#` and
`L ∈ L̂^# ∩ (𝔏 ⊓ 𝔑_i)` (so `L` is a non-identity element of `L̂` normalizing `𝔎_i`).  If `H` and `L`
commute, then the product `HL` is conjugate in `X` to an element of `AU`.

This is the case analysis of pp. 805–806: if `L ∈ L0set Lhat` then `C(L) ≤ 𝔏` forces
`H ∈ 𝔏 ⊓ 𝔎_i = 1`, contrary to `H ≠ 1`; so `L ∈ Dset Lhat` and Definition 9.1(iii) gives a
conjugate `l` of `L` in `Lhat` with `C(l) = C_{𝔎_j}(l)·C_𝔏(l) ⊆ 𝔑_j` for some `j`, and
`l ∈ Lset Lhat (Hs j)`.  By Definition 9.1(i) `l = μ L μ⁻¹` with `μ ∈ 𝔏`, so
`H' := μ H μ⁻¹` centralizes `l`; writing `H' = h₁h₂` with `h₁ ∈ C_{𝔎_j}(l)`,
`h₂ ∈ C_𝔏(l)` (given by (iii)) one shows `H' ∈ 𝔎_j` because the order of the image of `H'` in
`C(l)/(C(l) ⊓ 𝔎_j) ≅ C_𝔏(l)` divides both `|H'| ∣ |𝔎_i|` and `|C_𝔏(l)|`, which are coprime by
(ii)(d).  Then `μ(HL)μ⁻¹ = l H' = H' l ∈ AL l (Hs j) ⊆ AU`. -/
theorem mul_mem_conjAU_of_commute {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    {i : Fin n} {H : X} (hH : H ∈ Hs i) (hH1 : H ≠ 1) {L : X} (hL : L ∈ Lhat) (hL1 : L ≠ 1)
    (hLK : L ∈ Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) (hcomm : H * L = L * H) :
    ∃ a ∈ AU Lhat n Hs, IsConj (H * L) a := by
  by_cases hL0 : L ∈ L0set Lhat
  · -- `L ∈ 𝔏_0`: then `H ∈ C(L) ≤ 𝔏` and `H ∈ 𝔎_i`, so `H ∈ 𝔎_i ⊓ 𝔏 = 1`.
    exfalso
    have hHL : H ∈ Subgroup.centralizer ({L} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hcomm
    have hHMemL : H ∈ Lgrp Lhat := (mem_L0set.mp hL0).2.2 hHL
    have hbot : Hs i ⊓ Lgrp Lhat = ⊥ := h.supp_inf hD i
    have hmem : H ∈ (Hs i ⊓ Lgrp Lhat : Subgroup X) := ⟨hH, hHMemL⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hH1 hmem
  · -- `L ∈ 𝔇`.
    have hLd : L ∈ Dset Lhat := ⟨hL, hL1, fun hc => hL0 ⟨hL, hL1, hc⟩⟩
    -- Definition 9.1(iii)
    obtain ⟨l, hl_mem, hconjLl, j, hCeq, hCle⟩ := h.cover L hLd
    -- Definition 9.1(i)
    obtain ⟨μ, hμ, hlμ⟩ := h.conj hL hl_mem hconjLl
    have hl_ne1 : l ≠ 1 := by
      intro h1
      exact hL1 (isConj_one_left.mp (h1 ▸ hconjLl))
    -- `l ∈ 𝔇`
    have hlD : l ∈ Dset Lhat := by
      refine ⟨hl_mem, hl_ne1, ?_⟩
      intro hcl
      have hCL : Subgroup.centralizer ({L} : Set X) ≤ Lgrp Lhat := by
        intro x hx
        have hxm : μ * x * μ⁻¹ ∈ (Subgroup.centralizer ({L} : Set X)).map (MulAut.conj μ) :=
          ⟨x, hx, MulAut.conj_apply μ x⟩
        rw [mmc_centralizer_conj_singleton μ L, ← hlμ] at hxm
        have hx' : μ * x * μ⁻¹ ∈ Lgrp Lhat := hcl hxm
        have hx'' : μ⁻¹ * (μ * x * μ⁻¹) * μ ∈ Lgrp Lhat :=
          (Lgrp Lhat).mul_mem ((Lgrp Lhat).mul_mem ((Lgrp Lhat).inv_mem hμ) hx') hμ
        simpa [mul_assoc] using hx''
      exact hLd.2.2 hCL
    have hlLset : l ∈ Lset Lhat (Hs j) := ⟨hlD, hCle⟩
    -- The conjugate `H' = μ H μ⁻¹` of `H` centralizes `l`.
    set H' := μ * H * μ⁻¹ with hH'def
    have hH'l : H' * l = l * H' := by
      rw [hH'def, hlμ]
      calc (μ * H * μ⁻¹) * (μ * L * μ⁻¹) = μ * (H * L) * μ⁻¹ := by group
        _ = μ * (L * H) * μ⁻¹ := by rw [hcomm]
        _ = (μ * L * μ⁻¹) * (μ * H * μ⁻¹) := by group
    have hH'C : H' ∈ Subgroup.centralizer ({l} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hH'l
    -- `H' ∈ 𝔎_j`.
    have hH'j : H' ∈ Hs j := by
      have hord_dvd : orderOf H' ∣ Nat.card ↥(Hs i) := by
        have hsemiconj : SemiconjBy μ H H' := by
          change μ * H = H' * μ
          rw [hH'def]; group
        have h1 : orderOf H' = orderOf H := (SemiconjBy.orderOf_eq μ hsemiconj).symm
        rw [h1, Subgroup.orderOf_coe (⟨H, hH⟩ : Hs i)]
        exact orderOf_dvd_natCard (⟨H, hH⟩ : Hs i)
      have hcard_eq : Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X))
          = Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X)) := by
        have hmap : (Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X)).map (MulAut.conj μ)
            = Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X) := by
          rw [Subgroup.map_inf _ _ _ (MulAut.conj μ).injective, mmc_map_conj_eq_self_of_mem hμ,
            mmc_centralizer_conj_singleton μ L, ← hlμ]
        rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj μ).injective]
      have hcop : (Nat.card ↥(Hs i)).Coprime
          (Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X))) := by
        rw [hcard_eq]
        exact h.supp_coprime_cent hD i L hL hL1
      -- Work in the group `C = C(l)`.
      let C : Subgroup X := Subgroup.centralizer ({l} : Set X)
      let Dc : Subgroup ↥C := (Hs j).subgroupOf C
      let Bc : Subgroup ↥C := (Lgrp Lhat).subgroupOf C
      haveI hDcNormal : Dc.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCle
      have hDcbot : Dc ⊓ Bc = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hx
        rw [Subgroup.mem_bot]
        have hxH : (x : X) ∈ Hs j := Subgroup.mem_subgroupOf.mp hx.1
        have hxL : (x : X) ∈ Lgrp Lhat := Subgroup.mem_subgroupOf.mp hx.2
        have h1 : (x : X) = 1 := by
          have hxbot : (x : X) ∈ (⊥ : Subgroup X) := by
            rw [← h.supp_inf hD j]; exact ⟨hxH, hxL⟩
          exact Subgroup.mem_bot.mp hxbot
        exact Subtype.ext h1
      have hsup : Dc ⊔ Bc = ⊤ := by
        have h1 : ((Hs j ⊓ C) ⊔ (Lgrp Lhat ⊓ C)).subgroupOf C = Dc ⊔ Bc := by
          rw [Subgroup.subgroupOf_sup inf_le_right inf_le_right, Subgroup.inf_subgroupOf_right,
            Subgroup.inf_subgroupOf_right]
        rw [← h1, ← hCeq, Subgroup.subgroupOf_self]
      have hcard : Nat.card ↥C = Nat.card ↥Dc * Nat.card ↥Bc :=
        mmc_card_eq_card_mul_card_of_sup_eq_top_of_disjoint hsup (disjoint_iff.mpr hDcbot)
      have hdDc : Nat.card ↥Dc = Nat.card ↥(Hs j ⊓ C) := mmc_card_subgroupOf (Hs j) C
      have hdBc : Nat.card ↥Bc = Nat.card ↥(Lgrp Lhat ⊓ C) := mmc_card_subgroupOf (Lgrp Lhat) C
      have hDcindex : Dc.index = Nat.card ↥(Lgrp Lhat ⊓ C) := by
        rw [Subgroup.index_eq_card_div, hcard, hdBc, Nat.mul_div_cancel_left _ Nat.card_pos]
      have hcop_index : (orderOf (⟨H', hH'C⟩ : ↥C)).Coprime Dc.index := by
        rw [← Subgroup.orderOf_coe (⟨H', hH'C⟩ : ↥C), hDcindex]
        exact hcop.coprime_dvd_left hord_dvd
      have hmem : (⟨H', hH'C⟩ : ↥C) ∈ Dc := mmc_mem_of_coprime_index Dc hcop_index
      exact Subgroup.mem_subgroupOf.mp hmem
    refine ⟨l * H', ?_, ?_⟩
    · rw [mem_AU_iff]
      exact Or.inr ⟨j, l, hlLset, H', hH'j, hH'l.symm, rfl⟩
    · rw [isConj_iff]
      refine ⟨μ, ?_⟩
      calc μ * (H * L) * μ⁻¹ = (μ * H * μ⁻¹) * (μ * L * μ⁻¹) := by group
        _ = H' * l := by rw [← hH'def, ← hlμ]
        _ = l * H' := hH'l

end

end Work.Tame
