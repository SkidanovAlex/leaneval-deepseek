/-
# `Work.NormalComplement.sec5_setup_invol`

Peterfalvi I Ch. III §5 (p. 184): in the §5 configuration, there is a unique involution `u ∈ H`
centralising `V = centD H t = C_D(t)`.  This is the first conjunct of
`Work.NormalComplement.sec5_setup`.

The two auxiliary lemmas `isSylowIn_of_le_of_le_mono` and `map_conj_map_conj` below are private
copies of lemmas proved in `Submission/Work/NormalComplement/sylow_normalizer_transfer.lean` (where
they are `private`, hence not importable).  The Sylow conjugacy itself is taken from
`Work.NormalComplement.exists_conj_sylow_of_normal_abelian`
(`Submission/Work/NormalComplement/conj_sylow_of_isCyclic.lean`) with `N = M = V`.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.sec1_lemma3_struct_regular
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.conj_sylow_of_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.NormalComplement

open Classical

/-! ## Auxiliary group theory -/

/-- A `p`-Sylow of `X` remains a `p`-Sylow of any intermediate subgroup `Y`. -/
private lemma isSylowIn_of_le_of_le_mono {G : Type*} [Group G] {p : ℕ} {S X Y : Subgroup G}
    (h : Work.NormalComplement.IsSylowIn p S X) (hSY : S ≤ Y) (hYX : Y ≤ X) :
    Work.NormalComplement.IsSylowIn p S Y := by
  refine ⟨h.1, hSY, ?_⟩
  intro hdiv
  apply h.2.2
  have h1 : p ∣ S.relIndex Y := hdiv
  have h2 : p ∣ S.relIndex Y * Y.relIndex X := dvd_mul_of_dvd_left h1 _
  rw [Subgroup.relIndex_mul_relIndex S Y X hSY hYX] at h2
  exact h2

/-- Conjugation is compatible with composition: `(A^a)^b = A^(b * a)`. -/
private lemma map_conj_map_conj {G : Type*} [Group G] (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- **Sylow conjugacy, `k`-form.**  If `P` is a Sylow `p`-subgroup of `V`, `V ≤ D`, `k ∈ D`,
`k⁻¹ · P · k ≤ V`, and `N_D(P) ≤ V`, then `k ∈ V`. -/
private lemma mem_of_isSylowIn_of_conj_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P V D : Subgroup G} {k : G}
    (hP : Work.NormalComplement.IsSylowIn p P V) (hVD : V ≤ D) (hkD : k ∈ D)
    (hkP : P.map (MulAut.conj k⁻¹).toMonoidHom ≤ V)
    (hND : D ⊓ Subgroup.normalizer (P : Set G) ≤ V) : k ∈ V := by
  set Q : Subgroup G := P.map (MulAut.conj k⁻¹).toMonoidHom with hQdef
  have hQle : Q ≤ V := hkP
  have hQ_syl : Work.NormalComplement.IsSylowIn p Q V := by
    refine ⟨?_, hQle, ?_⟩
    · exact hP.1.map _
    · have hc : Nat.card ↥Q = Nat.card ↥P :=
        Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
      have hidx : (Q.subgroupOf V).index = (P.subgroupOf V).index := by
        rw [Subgroup.index_eq_card_div (Q.subgroupOf V),
          Subgroup.index_eq_card_div (P.subgroupOf V),
          show Nat.card ↥(Q.subgroupOf V) = Nat.card ↥Q from
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv,
          show Nat.card ↥(P.subgroupOf V) = Nat.card ↥P from
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.2.1).toEquiv, hc]
      rw [hidx]
      exact hP.2.2
  obtain ⟨v, hvV, hvP⟩ :=
    exists_conj_sylow_of_normal_abelian (N := V) (M := V) (S := P) (T := Q) le_rfl
      (fun m hm n hn => V.mul_mem (V.mul_mem hm hn) (V.inv_mem hm))
      (fun a ha b hb => V.mul_mem (V.mul_mem (V.mul_mem ha hb) (V.inv_mem ha)) (V.inv_mem hb))
      hP hQ_syl
  have hnorm : k * v ∈ Subgroup.normalizer (P : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    change P.map (MulAut.conj (k * v)).toMonoidHom = P
    rw [← map_conj_map_conj P v k, hvP, hQdef,
      map_conj_map_conj P k⁻¹ k, mul_inv_cancel k]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one,
      mul_one]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hmem : k * v ∈ D ⊓ Subgroup.normalizer (P : Set G) :=
    ⟨D.mul_mem hkD (hVD hvV), hnorm⟩
  have hkvV : k * v ∈ V := hND hmem
  have hk : k = (k * v) * v⁻¹ := by group
  rw [hk]
  exact V.mul_mem hkvV (V.inv_mem hvV)

/-- **Peterfalvi I Ch. III §5, the involution `u` of `C_H(V)`** (p.184).  In the §5 configuration
(`h : Design.Setup5`), there is a **unique** involution of `H` centralising
`V = centD H t = C_D(t)`.  This is the first conjunct of `Work.NormalComplement.sec5_setup`.

Proof.  *Existence*: `hC4` P2(a) gives `u ∈ H` with `orderOf u = 2` and
`centD H t = twoPoint H t ⊓ C_G({u})`, hence `u` centralises `V`.
*Uniqueness*: an involution `x ∈ H` centralising `V ⊇ A` lies in `C_G(A)`, hence in
`H ⊓ N_G(A)`.  By `Work.NormalComplement.sec1_lemma3_struct_regular` (`X = A`, needs only `hC4`)
the group `K₁ = NK H t A = CK H t A` acts **sharply transitively** on the involutions of
`H ⊓ N_G(A)`; so `x = k u k⁻¹` for a unique `k ∈ K₁`.  Then `k ∈ CK H t A`, so `k ∈ D` with
`t k t⁻¹ = k⁻¹`, and `k` centralises `A`.  Since `x` and `u` both centralise `V` and
`V = D ⊓ C_G(u)`, one gets `k⁻¹Vk ⊆ V`, hence `k⁻¹Vk = V`; and `k⁻¹Pk ≤ V` with `P` a Sylow
`p`-subgroup of `V`, so `k ∈ V` (Sylow conjugacy in `V`, `N_D(P) ⊆ V` from `sec4_one_c`).
But then `t k t⁻¹ = k⁻¹` and `t k t⁻¹ = k`, so `k² = 1`, while `K₁` (`k ∈ K₁`) has odd order
`2^p - 1`: `k = 1`, and `x = u`. -/
theorem sec5_setup_invol (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    ∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) := by
  classical
  haveI hpF : Fact p.Prime := Fact.mk h.prime
  -- ## Existence: Ch. II §4 Prop. 2 (a).
  obtain ⟨u, huInv, huV⟩ := (hC4 G h.sit H h.se t h.invol h.notMem).2.1
  have huH : u ∈ H := huInv.1
  have hu2 : orderOf u = 2 := huInv.2
  have huC : u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ Subgroup.centralizer ({u} : Set G) := by
      have hv2 := hv
      rw [huV] at hv2
      exact (Subgroup.mem_inf.mp hv2).2
    exact (Subgroup.mem_centralizer_iff.mp hv' u (Set.mem_singleton u)).symm
  refine ⟨u, ⟨huH, hu2, huC⟩, ?_⟩
  rintro x ⟨hxH, hx2, hxC⟩
  -- ## Uniqueness.
  have hA_le_V : A ≤ Submission.Blueprint.centD H t := h.A_le
  have hP_le_V : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have huA : u ∈ Subgroup.centralizer (A : Set G) := Subgroup.centralizer_le hA_le_V huC
  have hxA : x ∈ Subgroup.centralizer (A : Set G) := Subgroup.centralizer_le hA_le_V hxC
  have huNA : u ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G) huA
  have hxNA : x ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G) hxA
  -- `N_K(A)` is nontrivial (`|C_K(A)| = 2^p - 1 ≥ 3`).
  have hNK_ne : ∃ k ∈ Work.NormalComplement.Design.NK H t A, k ≠ 1 := by
    have hsub : Work.NormalComplement.Design.CK H t A
        ⊆ Work.NormalComplement.Design.NK H t A := by
      intro y hy
      rw [Work.NormalComplement.Design.CK, Set.mem_inter_iff] at hy
      rw [Work.NormalComplement.Design.NK, Set.mem_inter_iff]
      exact ⟨hy.1, Subgroup.centralizer_le_normalizer (A : Set G) hy.2⟩
    have hlt : 1 < (Work.NormalComplement.Design.NK H t A).ncard := by
      have hle := Set.ncard_le_ncard hsub
      rw [h.A_CK] at hle
      have hp2 : 2 ≤ p := h.prime.two_le
      have h4 : 4 ≤ 2 ^ p := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
      omega
    obtain ⟨k, hk, hk1⟩ := Set.exists_ne_of_one_lt_ncard hlt (1 : G)
    exact ⟨k, hk, hk1⟩
  -- ## Sharp transitivity of `K₁ = C_K(A)` on `Inv(H ⊓ N_G(A))`.
  obtain ⟨K₁, hK₁car, hK₁NKeq, _hK₁cyc, hK₁reg⟩ :=
    sec1_lemma3_struct_regular hC4 h.sit h.se h.invol h.notMem h.A_ne h.A_le hNK_ne
  have hu_inv : u ∈ Submission.Blueprint.involutions
      ((H ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) : Set G) := ⟨⟨huH, huNA⟩, hu2⟩
  have hx_inv : x ∈ Submission.Blueprint.involutions
      ((H ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) : Set G) := ⟨⟨hxH, hxNA⟩, hx2⟩
  obtain ⟨k, ⟨hkK₁, hkux⟩, -⟩ := hK₁reg u hu_inv x hx_inv
  -- ## Properties of `k`.
  have hkCK : k ∈ Work.NormalComplement.Design.CK H t A := hK₁NKeq ▸ (hK₁car ▸ hkK₁)
  have hkKset : k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t := by
    rw [Work.NormalComplement.Design.CK, Set.mem_inter_iff] at hkCK
    exact hkCK.1
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := hkKset.1
  have hkinv : t * k * t⁻¹ = k⁻¹ := hkKset.2
  -- ## `k⁻¹ V k ⊆ V`.
  have hconjVV : ∀ v ∈ Submission.Blueprint.centD H t,
      k⁻¹ * v * k ∈ Submission.Blueprint.centD H t := by
    intro v hv
    have hcomm_x : v * (k * u * k⁻¹) = (k * u * k⁻¹) * v := by
      rw [hkux]
      exact (Subgroup.mem_centralizer_iff.mp hxC) v hv
    have hcomm_u : u * (k⁻¹ * v * k) = (k⁻¹ * v * k) * u := by
      have h2 := congrArg (fun z => k⁻¹ * z * k) hcomm_x
      calc u * (k⁻¹ * v * k) = k⁻¹ * ((k * u * k⁻¹) * v) * k := by group
        _ = k⁻¹ * (v * (k * u * k⁻¹)) * k := h2.symm
        _ = (k⁻¹ * v * k) * u := by group
    rw [huV]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Submission.Blueprint.twoPoint H t).mul_mem
        ((Submission.Blueprint.twoPoint H t).mul_mem
          ((Submission.Blueprint.twoPoint H t).inv_mem hkD)
          (Subgroup.mem_inf.mp hv).1) hkD
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hcomm_u
  have hVmap : (Submission.Blueprint.centD H t).map (MulAut.conj k⁻¹).toMonoidHom
      = Submission.Blueprint.centD H t := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro w ⟨v, hv, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hconjVV v hv
    · exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective).symm
  have hPmap_le : P.map (MulAut.conj k⁻¹).toMonoidHom ≤ Submission.Blueprint.centD H t := by
    rw [← hVmap]
    exact Subgroup.map_mono hP_le_V
  -- ## The Sylow step: `k ∈ V`.
  have hP_syl_V : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.centD H t) :=
    isSylowIn_of_le_of_le_mono h.P_syl hP_le_V inf_le_left
  have hND_le_V : Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G)
      ≤ Submission.Blueprint.centD H t := by
    rw [(sec4_one_c hFT h.toSetup45A).1]
    exact sup_le (inf_le_left.trans h.A_le) hP_le_V
  have hkV : k ∈ Submission.Blueprint.centD H t :=
    mem_of_isSylowIn_of_conj_le hP_syl_V inf_le_left hkD hPmap_le hND_le_V
  -- ## `k = 1` because `K₁` has odd order and `k² = 1`.
  have hk2 : k * k = 1 := by
    have htk0 : t * k = k * t :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hkV).2 t (Set.mem_singleton t))
    have htk : t * k * t⁻¹ = k := by rw [htk0]; group
    have hkk : k = k⁻¹ := htk.symm.trans hkinv
    exact mul_eq_one_iff_eq_inv.mpr hkk
  have hVodd : Odd (Nat.card ↥(Submission.Blueprint.centD H t)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_left)
  have hk1 : k = 1 := by
    have h1 : orderOf k ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hk2)
    have h2 : orderOf k ∣ Nat.card ↥(Submission.Blueprint.centD H t) :=
      Subgroup.orderOf_dvd_natCard _ hkV
    have hcop : Nat.Coprime 2 (Nat.card ↥(Submission.Blueprint.centD H t)) :=
      Nat.coprime_two_left.mpr hVodd
    have hone : orderOf k ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  rw [← hkux, hk1]
  simp

end Work.NormalComplement
