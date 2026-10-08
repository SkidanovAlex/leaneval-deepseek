import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.A7VnotCyclicAux
import Submission.Work.CORE4.A7Vsylow

/-!
# Area CORE4: `C_M(t) = H ∩ M` has a normal four-subgroup in the `A₇` case

`Work.CORE4.A7CMtFourGroupAlt` is the structural input of `Work.CORE4.A7VnotCyclic`
(`O₂(Ĥ) ⊄ S₀` in the `A₇` case of Bender 1981, §4): in the `A₇` configuration the centralizer
`C_M(t) = H ⊓ M` contains a Klein four-subgroup `V` normal in `C_M(t)`.

Route.  `E := layerIn C.D.M` has central quotient `A₇` and odd centre (`LayerCtx6`), `t ∈ E` is an
involution, and `Q := S ⊓ E` has order `8` (`A7Vsylow`) and lies in `C(t)` (`bSetup_S_le_H`: `t`
is central in `S`).  Writing `ψ : ↥E →* A₇` for the quotient map composed with a fixed isomorphism,
`V̄ := O₂(C_{A₇}(ψ t))` is a four-group (`A7ModelO2`).  The image `Q̄` of `Q` is a Sylow
`2`-subgroup of `C(ψ t)`, so `V̄ ≤ Q̄`, and the preimage `V` of `V̄` inside `Q` is a four-group.
Normality is the only serious point: for `k ∈ C_M(t) ⊆ M` the conjugation automorphism of `↥E`
induces an automorphism `α` of `A₇` fixing `ψ t`, so `α` preserves `C(ψ t)` and hence
`V̄ = O₂(C(ψ t))`; therefore `C_M(t)` normalises the preimage of `V̄`, and `V`, being the Sylow
`2`-subgroup of that (central-by-`V̄`) preimage, is normalised as well.
-/

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- Conjugation by `k ∈ M` as an automorphism of `↥E` (for `E ≤ M ⊆ N_G(E)`). -/
def conjAut {E M : Subgroup G} (hEnorm : M ≤ Subgroup.normalizer (E : Set G)) (k : G)
    (hk : k ∈ M) : ↥E ≃* ↥E where
  toFun x := ⟨k * (x : G) * k⁻¹, (Subgroup.le_normalizer_iff.mp hEnorm k hk) (x : G) x.2⟩
  invFun x := ⟨k⁻¹ * (x : G) * k,
    by simpa using (Subgroup.le_normalizer_iff.mp hEnorm k⁻¹ (M.inv_mem hk)) (x : G) x.2⟩
  left_inv x := Subtype.ext (by
    show k⁻¹ * (k * (x : G) * k⁻¹) * k = (x : G)
    group)
  right_inv x := Subtype.ext (by
    show k * (k⁻¹ * (x : G) * k) * k⁻¹ = (x : G)
    group)
  map_mul' x y := Subtype.ext (by
    show k * ((x : G) * (y : G)) * k⁻¹ = (k * (x : G) * k⁻¹) * (k * (y : G) * k⁻¹)
    group)

theorem conjAut_apply {E M : Subgroup G} (hEnorm : M ≤ Subgroup.normalizer (E : Set G))
    {k : G} (hk : k ∈ M) (x : ↥E) : ((conjAut hEnorm k hk x : ↥E) : G) = k * (x : G) * k⁻¹ := rfl

/-- The preimage of `O₂(C_{A₇}(x))` in `↥E` is invariant under `conjAut k` for `k ∈ M` fixing
`t`. -/
theorem map_conjAut_comap_le {E M : Subgroup G} (hEnorm : M ≤ Subgroup.normalizer (E : Set G))
    (Φ : (↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7)) {t : ↥E} {k : G}
    (hk : k ∈ M) (hkt : (conjAut hEnorm k hk) t = t) :
    ((Work.GW2.pCoreIn 2 (Subgroup.centralizer
        ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) t)} : Set (alternatingGroup (Fin 7))))).comap
        (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E)))).map
        (conjAut hEnorm k hk).toMonoidHom ≤
      (Work.GW2.pCoreIn 2 (Subgroup.centralizer
        ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) t)} : Set (alternatingGroup (Fin 7))))).comap
        (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))) := by
  set ψ : ↥E →* alternatingGroup (Fin 7) :=
    Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E)) with hψ
  set x : alternatingGroup (Fin 7) := Φ (QuotientGroup.mk' (Subgroup.center ↥E) t) with hx
  set Vbar : Subgroup (alternatingGroup (Fin 7)) :=
    Work.GW2.pCoreIn 2 (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7)))) with hVbar
  set σ : ↥E ≃* ↥E := conjAut hEnorm k hk with hσ
  have hσc : Subgroup.map (σ : ↥E →* ↥E) (Subgroup.center ↥E) = Subgroup.center ↥E :=
    map_center_mulEquiv σ
  set α : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) :=
    (Φ.symm.trans ((QuotientGroup.congr (Subgroup.center ↥E) (Subgroup.center ↥E) σ hσc).trans Φ))
    with hα
  have hψσ : ∀ y : ↥E, ψ (σ y) = α (ψ y) := by
    intro y
    show Φ (QuotientGroup.mk' (Subgroup.center ↥E) (σ y)) =
      α (Φ (QuotientGroup.mk' (Subgroup.center ↥E) y))
    rw [hα]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [QuotientGroup.congr_mk']
  have hxψ : ψ t = x := by rw [hψ, hx]; rfl
  have hxfix : α x = x := by
    rw [← hxψ, ← hψσ t, hkt, hxψ]
  have hαV : Vbar.map α.toMonoidHom = Vbar := by
    have h1 : Vbar.map α.toMonoidHom =
        Work.GW2.pCoreIn 2 ((Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7)))).map
          α.toMonoidHom) := by
      rw [hVbar]
      exact (PcoreInMapMulEquiv α 2
        (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))))).symm
    rw [h1, map_centralizer_eq_centralizer_image]
    have h2 : α '' ({x} : Set (alternatingGroup (Fin 7))) = {x} := by
      rw [Set.image_singleton, hxfix]
    rw [h2, hVbar]
  intro e he
  rw [Subgroup.mem_map] at he
  obtain ⟨y, hy, rfl⟩ := he
  rw [Subgroup.mem_comap] at hy ⊢
  rw [show σ.toMonoidHom y = σ y from rfl, hψσ y]
  have hmem : α (ψ y) ∈ Vbar.map α.toMonoidHom := Subgroup.mem_map_of_mem α.toMonoidHom hy
  rwa [hαV] at hmem


theorem A7CMtFourGroupAlt (I : Work.GW2.C4Inputs) (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (h : Work.GW2.Hyp9 G B C) (hA : Work.GW2.IsA7Case C.D) (hf : Work.GW2.A7Facts1 C.D) :
    ∃ V : Subgroup G, V ≤ B.H ⊓ C.D.M ∧ Work.GW2.IsFourGroup V ∧
      (V.subgroupOf (B.H ⊓ C.D.M)).Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := h
  have hH9 : Work.GW2.Hyp9 G B C := ⟨hbc, hcase2, hplus, hseven, height⟩
  set M : Subgroup G := C.D.M with hM
  set E : Subgroup G := Work.GW2.layerIn M with hE
  have hEM : E ≤ M := by rw [hE, hM]; exact layerIn_le C.D.M
  have hEnorm : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE, hM]; exact layerIn_le_normalizer C.D.M
  have hZodd : Odd (Nat.card ↥(Subgroup.center ↥E)) :=
    (LayerCtx6 I hbc C (DihOrCycSub hbc.sylow C.D.M)).2.1
  obtain ⟨Φ⟩ := hA
  have htE : B.t ∈ E := by rw [hE, hM]; exact C.D.t_mem
  let tE : ↥E := ⟨B.t, htE⟩
  have htE_ord : orderOf tE = 2 := by
    show orderOf (⟨B.t, htE⟩ : ↥E) = 2
    rw [Subgroup.orderOf_mk]
    exact B.t_order
  have hψker : ∀ z : ↥E,
      (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))) z = 1 ↔
        z ∈ Subgroup.center ↥E := by
    intro z
    constructor
    · intro hz
      have h1 : QuotientGroup.mk' (Subgroup.center ↥E) z = 1 :=
        Φ.injective (by simpa using hz)
      exact QuotientGroup.ker_mk' (Subgroup.center ↥E) ▸ MonoidHom.mem_ker.mpr h1
    · intro hz
      have h1 : QuotientGroup.mk' (Subgroup.center ↥E) z = 1 :=
        (QuotientGroup.eq_one_iff z).mpr hz
      rw [MonoidHom.comp_apply, h1, map_one]
  have htE_ne : tE ∉ Subgroup.center ↥E := by
    intro hc
    have hd : orderOf tE ∣ Nat.card ↥(Subgroup.center ↥E) :=
      Subgroup.orderOf_dvd_natCard _ hc
    rw [htE_ord] at hd
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr hd)
  have hxt : orderOf (Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h2 : tE ^ 2 = 1 := by rw [← htE_ord]; exact pow_orderOf_eq_one tE
      show Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE) ^ 2 = 1
      rw [← map_pow (f := Φ), ← map_pow (f := QuotientGroup.mk' (Subgroup.center ↥E)), h2]
      simp
    · intro h1
      exact htE_ne ((hψker tE).mp h1)
  -- the four-group of the central quotient
  have hVbar4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 (Subgroup.centralizer
      ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)} : Set (alternatingGroup (Fin 7))))) :=
    A7ModelO2 _ hxt
  -- `Q = S ⊓ E` has order `8`
  set Q : Subgroup G := (B.S : Subgroup G) ⊓ E with hQ
  have hQcard : Nat.card ↥Q = 8 := by
    rw [hQ, hE, hM]
    exact A7Vsylow G B C hH9 ⟨Φ⟩ hf
  have hQleE : Q ≤ E := by rw [hQ]; exact inf_le_right
  have hQleS : Q ≤ (B.S : Subgroup G) := by rw [hQ]; exact inf_le_left
  have hQleH : Q ≤ B.H := hQleS.trans (bSetup_S_le_H B)
  set Qv : Subgroup ↥E := Q.subgroupOf E with hQv
  have hQvcard : Nat.card ↥Qv = 8 := by
    rw [hQv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleE).toEquiv, hQcard]
  have hQvZ : Qv ⊓ Subgroup.center ↥E = ⊥ :=
    inf_eq_bot_of_two_group_of_odd
      (IsPGroup.of_card (n := 3) (by rw [hQvcard]; norm_num)) hZodd
  have hψker' : (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))).ker =
      Subgroup.center ↥E := by
    rw [MonoidHom.ker_comp_of_injective _ _ Φ.injective, QuotientGroup.ker_mk']
  have hQvker : Qv ⊓ (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))).ker = ⊥ := by
    rw [hψker', hQvZ]
  set ψ : ↥E →* alternatingGroup (Fin 7) :=
    Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E)) with hψ
  have hQbarcard : Nat.card ↥(Qv.map ψ) = 8 := by
    rw [card_map_eq_card_of_disjoint_ker ψ (by rw [hψ]; exact hQvker), hQvcard]
  set Qbar : Subgroup (alternatingGroup (Fin 7)) := Qv.map ψ with hQbar
  have hQbar_le_Cx : Qbar ≤ Subgroup.centralizer
      ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)} : Set (alternatingGroup (Fin 7))) := by
    rw [hQbar, hψ]
    rintro y ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have hqH : (q : G) ∈ B.H := hQleH hqQ
    have hcomm : (q : G) * B.t = B.t * (q : G) :=
      (Subgroup.mem_centralizer_iff.mp hqH B.t (by simp)).symm
    have hcommE : q * tE = tE * q := Subtype.ext (by simpa [tE] using hcomm)
    have h1 : ψ tE * ψ q = ψ q * ψ tE := by
      simp only [← map_mul, hcommE]
    rw [show ψ tE = Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE) from rfl] at h1
    exact h1
  -- Q̄ is a Sylow 2-subgroup of the centralizer
  set Cx : Subgroup (alternatingGroup (Fin 7)) := Subgroup.centralizer
      ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)} : Set (alternatingGroup (Fin 7))) with hCx
  have hCxcard : Nat.card ↥Cx = 24 := by
    rw [hCx]
    exact I.toolkit.a7.2.2.1 _ hxt
  have hQbar_le_Cx' : Qbar ≤ Cx := by rw [hCx]; exact hQbar_le_Cx
  have hQbarCx_card : Nat.card ↥(Qbar.comap Cx.subtype) = 8 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective (Qbar.comap Cx.subtype) Cx.subtype
        Cx.subtype_injective).toEquiv, Subgroup.map_comap_eq, Subgroup.range_subtype,
      inf_eq_right.mpr hQbar_le_Cx', hQbar, hQbarcard]
  have hndvd : ¬ 2 ∣ (Qbar.comap Cx.subtype).index := by
    intro hd
    have hmul := Subgroup.card_mul_index (Qbar.comap Cx.subtype)
    rw [hQbarCx_card, hCxcard] at hmul
    obtain ⟨m, hm⟩ := hd
    rw [hm] at hmul
    omega
  let P : Sylow 2 ↥Cx :=
    (IsPGroup.of_card (n := 3) (by rw [hQbarCx_card]; norm_num)).toSylow hndvd
  have hPcoe : (P : Subgroup ↥Cx) = Qbar.comap Cx.subtype := by
    simp only [P, IsPGroup.toSylow_coe]
  have hVbar_le_Cx : Work.GW2.pCoreIn 2 Cx ≤ Cx := pCoreIn_le_self 2 Cx
  have hVbar_le_Qbar : Work.GW2.pCoreIn 2 Cx ≤ Qbar := by
    intro v hv
    have h1 : (⟨v, hVbar_le_Cx hv⟩ : ↥Cx) ∈ (Work.GW2.pCoreIn 2 Cx).subgroupOf Cx := by
      rw [Subgroup.mem_subgroupOf]
      exact hv
    have h2 : (⟨v, hVbar_le_Cx hv⟩ : ↥Cx) ∈ (P : Subgroup ↥Cx) :=
      pCoreIn_le_sylow 2 Cx P h1
    rw [hPcoe] at h2
    exact Subgroup.mem_comap.mp h2
  -- the preimage `W` of `V̄` and the subgroup `Vv = Qv ⊓ W`
  set W : Subgroup ↥E := (Work.GW2.pCoreIn 2 (Subgroup.centralizer
      ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)} : Set (alternatingGroup (Fin 7))))).comap
      (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))) with hW
  set Vv : Subgroup ↥E := Qv ⊓ W with hVv
  have hVvmap : Vv.map ψ = Work.GW2.pCoreIn 2 (Subgroup.centralizer
      ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)} : Set (alternatingGroup (Fin 7)))) := by
    apply le_antisymm
    · refine (Subgroup.map_mono inf_le_right).trans ?_
      rw [hW, hψ, Subgroup.map_comap_eq]
      exact inf_le_right
    · intro y hy
      have hyQ : y ∈ Qbar := hVbar_le_Qbar hy
      rw [hQbar] at hyQ
      obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hyQ
      refine Subgroup.mem_map.mpr ⟨q, ?_, hqy⟩
      rw [hVv, Subgroup.mem_inf]
      refine ⟨hq, ?_⟩
      rw [hW, Subgroup.mem_comap]
      show (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))) q ∈ _
      rw [hqy]
      exact hy
  have hVvker : Vv ⊓ (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))).ker = ⊥ := by
    rw [hVv]
    exact le_bot_iff.mp (le_trans (inf_le_inf inf_le_left le_rfl) (le_of_eq hQvker))
  have hVvcard : Nat.card ↥Vv = 4 := by
    have h1 : Nat.card ↥(Vv.map ψ) = Nat.card ↥Vv := by
      rw [hψ]
      exact card_map_eq_card_of_disjoint_ker _ hVvker
    rw [← h1, hVvmap, hVbar4.1]
  have hVvexp : ∀ v ∈ Vv, v ^ 2 = 1 := by
    intro v hv
    have h1 : ψ v ∈ Work.GW2.pCoreIn 2 (Subgroup.centralizer
        ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)} : Set (alternatingGroup (Fin 7)))) := by
      have h2 : ψ v ∈ Vv.map ψ := Subgroup.mem_map_of_mem ψ hv
      rwa [hVvmap] at h2
    have h2 : ψ (v ^ 2) = 1 := by
      rw [map_pow, hVbar4.2 (ψ v) h1]
    have h3 : v ^ 2 ∈ (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))).ker :=
      MonoidHom.mem_ker.mpr h2
    have h4 : v ^ 2 ∈ Vv ⊓ (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))).ker :=
      ⟨Vv.pow_mem hv 2, h3⟩
    rw [hVvker] at h4
    exact Subgroup.mem_bot.mp h4
  -- the four-group in `G`
  refine ⟨Vv.map E.subtype, ?_, ?_, ?_⟩
  · -- `V ≤ H ⊓ M`
    have hVleQ : Vv.map E.subtype ≤ Q := by
      refine (Subgroup.map_mono inf_le_left).trans ?_
      rw [hQv, Subgroup.map_subgroupOf_eq_of_le hQleE]
    exact le_inf (hVleQ.trans hQleH) (hVleQ.trans (hQleE.trans hEM))
  · exact (isFourGroup_map_subtype_iff E Vv).mpr ⟨hVvcard, hVvexp⟩
  · -- normality in `H ⊓ M`
    have hle : Vv.map E.subtype ≤ B.H ⊓ C.D.M := by
      have hVleQ : Vv.map E.subtype ≤ Q := by
        refine (Subgroup.map_mono inf_le_left).trans ?_
        rw [hQv, Subgroup.map_subgroupOf_eq_of_le hQleE]
      exact le_inf (hVleQ.trans hQleH) (hVleQ.trans (hQleE.trans hEM))
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro xx k hx hk
    rw [Subgroup.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hkM : k ∈ M := (Subgroup.mem_inf.mp hk).2
    have hkH : k ∈ B.H := (Subgroup.mem_inf.mp hk).1
    have hkt : (conjAut hEnorm k hkM) tE = tE := by
      apply Subtype.ext
      show k * (tE : G) * k⁻¹ = (tE : G)
      have hc : B.t * k = k * B.t := Subgroup.mem_centralizer_iff.mp hkH B.t (by simp)
      have h1 : k * B.t * k⁻¹ = B.t := by rw [← hc]; group
      simpa [tE] using h1
    have hpW : (conjAut hEnorm k hkM) v ∈ W := by
      have hinv : W.map (conjAut hEnorm k hkM).toMonoidHom ≤ W := by
        rw [hW]
        exact map_conjAut_comap_le hEnorm Φ hkM hkt
      exact hinv (Subgroup.mem_map_of_mem (conjAut hEnorm k hkM).toMonoidHom
        (Subgroup.mem_inf.mp hv).2)
    have hpC : (conjAut hEnorm k hkM) v ∈
        Subgroup.centralizer ({tE} : Set ↥E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have hvC : tE * v = v * tE := by
        have hvQ : (v : G) ∈ Q := Subgroup.mem_subgroupOf.mp ((Subgroup.mem_inf.mp hv).1)
        have hvH : (v : G) ∈ B.H := hQleH hvQ
        have hcomm : B.t * (v : G) = (v : G) * B.t :=
          Subgroup.mem_centralizer_iff.mp hvH B.t (by simp)
        exact Subtype.ext (by simpa [tE] using hcomm)
      have hsymm : (conjAut hEnorm k hkM).symm tE = tE := by
        apply (conjAut hEnorm k hkM).injective
        rw [MulEquiv.apply_symm_apply, hkt]
      calc tE * (conjAut hEnorm k hkM) v
          = (conjAut hEnorm k hkM) ((conjAut hEnorm k hkM).symm tE * v) := by
            simp only [map_mul, MulEquiv.apply_symm_apply]
        _ = (conjAut hEnorm k hkM) (tE * v) := by rw [hsymm]
        _ = (conjAut hEnorm k hkM) (v * tE) := by rw [hvC]
        _ = (conjAut hEnorm k hkM) v * tE := by rw [map_mul, hkt]
    -- the cover: `p = z * q`
    have hpW₀ : (conjAut hEnorm k hkM) v ∈ W ⊓ Subgroup.centralizer ({tE} : Set ↥E) :=
      ⟨hpW, hpC⟩
    have hp2 : ((conjAut hEnorm k hkM) v) ^ 2 = 1 := by
      rw [← map_pow, show v ^ 2 = 1 from hVvexp v hv, map_one]
    -- decompose `p` using `V̄ ≤ Q̄`
    have hψp : ψ ((conjAut hEnorm k hkM) v) ∈ Work.GW2.pCoreIn 2 (Subgroup.centralizer
        ({Φ (QuotientGroup.mk' (Subgroup.center ↥E) tE)} : Set (alternatingGroup (Fin 7)))) := by
      rw [hW, Subgroup.mem_comap] at hpW
      exact hpW
    have hψpQ : ψ ((conjAut hEnorm k hkM) v) ∈ Qbar := hVbar_le_Qbar hψp
    rw [hQbar] at hψpQ
    obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hψpQ
    have hqW : q ∈ W := by
      rw [hW, Subgroup.mem_comap]
      show ψ q ∈ _
      rw [hqy]
      exact hψp
    have hqVv : q ∈ Vv := by rw [hVv, Subgroup.mem_inf]; exact ⟨hq, hqW⟩
    have hzZ : (conjAut hEnorm k hkM) v * q⁻¹ ∈ Subgroup.center ↥E := by
      have h1 : ψ ((conjAut hEnorm k hkM) v * q⁻¹) = 1 := by
        rw [map_mul, map_inv, hqy, mul_inv_cancel]
      exact (hψker _).mp (by rw [hψ]; exact h1)
    have hq2 : q ^ 2 = 1 := hVvexp q hqVv
    have h1z : q⁻¹ * ((conjAut hEnorm k hkM) v * q⁻¹) =
        ((conjAut hEnorm k hkM) v * q⁻¹) * q⁻¹ := Subgroup.mem_center_iff.mp hzZ q⁻¹
    have hcomm : q⁻¹ * (conjAut hEnorm k hkM) v = (conjAut hEnorm k hkM) v * q⁻¹ := by
      calc q⁻¹ * (conjAut hEnorm k hkM) v
          = (q⁻¹ * ((conjAut hEnorm k hkM) v * q⁻¹)) * q := by group
        _ = (((conjAut hEnorm k hkM) v * q⁻¹) * q⁻¹) * q := by rw [h1z]
        _ = (conjAut hEnorm k hkM) v * q⁻¹ := by group
    have hp2' : (conjAut hEnorm k hkM) v * (conjAut hEnorm k hkM) v = 1 := by
      rw [← pow_two]; exact hp2
    have hq2' : q * q = 1 := by rw [← pow_two]; exact hq2
    have hqinv2 : q⁻¹ * q⁻¹ = 1 := by rw [← mul_inv_rev, hq2', inv_one]
    have hz2 : ((conjAut hEnorm k hkM) v * q⁻¹) * ((conjAut hEnorm k hkM) v * q⁻¹) = 1 := by
      calc ((conjAut hEnorm k hkM) v * q⁻¹) * ((conjAut hEnorm k hkM) v * q⁻¹)
          = (conjAut hEnorm k hkM) v * (q⁻¹ * (conjAut hEnorm k hkM) v) * q⁻¹ := by group
        _ = (conjAut hEnorm k hkM) v * ((conjAut hEnorm k hkM) v * q⁻¹) * q⁻¹ := by rw [hcomm]
        _ = ((conjAut hEnorm k hkM) v * (conjAut hEnorm k hkM) v) * (q⁻¹ * q⁻¹) := by group
        _ = 1 := by rw [hp2', hqinv2, mul_one]
    have hz_eq_one : (conjAut hEnorm k hkM) v * q⁻¹ = 1 := by
      have hdvd : orderOf ((conjAut hEnorm k hkM) v * q⁻¹) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hz2)
      have hdvd2 : orderOf ((conjAut hEnorm k hkM) v * q⁻¹) ∣ Nat.card ↥(Subgroup.center ↥E) :=
        Subgroup.orderOf_dvd_natCard _ hzZ
      have h3 : orderOf ((conjAut hEnorm k hkM) v * q⁻¹) ∣
          (2 : ℕ).gcd (Nat.card ↥(Subgroup.center ↥E)) := Nat.dvd_gcd hdvd hdvd2
      have hcop : Nat.Coprime 2 (Nat.card ↥(Subgroup.center ↥E)) :=
        Nat.coprime_two_left.mpr hZodd
      rw [hcop] at h3
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    have hpVv : (conjAut hEnorm k hkM) v ∈ Vv := by
      have h1 : (conjAut hEnorm k hkM) v = ((conjAut hEnorm k hkM) v * q⁻¹) * q := by group
      rw [h1, hz_eq_one, one_mul]
      exact hqVv
    exact Subgroup.mem_map.mpr ⟨_, hpVv, rfl⟩

end Work.CORE4
