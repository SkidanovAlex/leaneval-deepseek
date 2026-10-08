import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2BGData
import Submission.Work.Dihedral.Defs
import Submission.Work.CORE4.CardCentralizerSr
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.Case2RelIndexMH
import Submission.Work.CORE4.dihedral_odd_cyclic_comm

namespace Work.CORE4

open scoped MatrixGroups

open Subgroup

/-!
# `Work.CORE4.Case2S0_comm_U`: Bender §4, p. 227, `[S₀, U] = 1`

Bender (1981, §4, p. 227): once `S ≤ E(M)` is known, `S₀ = O₂(H ∩ E) = O₂(H) = C_S(U)`, so
`[S₀, U] = 1`; this is used to exclude the exceptional clause `I_U(s) ⊲ Ĥ` of (8) via
Lemma 2.8 (`Work.GW2.Lemma28Prop`).

The proof here keeps the argument inside the §4 configuration:

* `S ≤ E := layerIn M` (§4 (9), `Case2Ctx.nine`), hence `S₀ ≤ H ⊓ M`;
* `U ⊓ M = K ⊔ B₀` (§4 (2), `Case2Pre`) and both parts lie in `N_G(S₀)`:
  `B₀ = C_{U⊓M}(S ⊓ E)` by `Case2PrePlus`, and `⁅K, S₀⁆ = ⊥` (Bender p. 224/227: `K` and `S₀`
  both lie in `E ⊓ H ≅ C_{L₂(q)}(t)`, which is dihedral, see `Case2S0_comm_K`);
* hence `H ⊓ M = (K ⊔ B₀) ⊔ S ≤ N_G(S₀)`, i.e. `S₀ ⊴ H ⊓ M`;
* since `S₀` is a `2`-group this gives `S₀ ≤ O₂(H ⊓ M) = O₂(H)` (the latter is §4 (7),
  `Case2SevenFacts`);
* finally `O₂(H) ⊓ U = 1` (coprime orders) and both are normal in `H`, so `O₂(H) ≤ C_G(U)`,
  and with `S₀ ≤ O₂(H)` the claim follows.
-/

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary lemmas -/

/-- Every normal `p`-subgroup of `X` lies in the `p`-core `O_p(X)`, in the `pCoreIn` form. -/
theorem le_pCoreIn_of_normal_isPGroup_s0 {p : ℕ} {X P : Subgroup G} (hPX : P ≤ X)
    (hN : (P.subgroupOf X).Normal) (hP : IsPGroup p (P.subgroupOf X)) :
    P ≤ Work.GW2.pCoreIn p X := by
  have h1 : P.subgroupOf X ≤ Work.GW2.pCore p ↥X :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hN, hP⟩)
  rintro x hx
  refine ⟨⟨x, hPX hx⟩, h1 ?_, rfl⟩
  rwa [Subgroup.mem_subgroupOf]

/-- `O_2(X)` is a `2`-group. -/
theorem isPGroup_pCoreIn_two (X : Subgroup G) : IsPGroup 2 (Work.GW2.pCoreIn 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥X | N.Normal ∧ IsPGroup 2 N}) :=
    Sylow.sSup_of_normal (G := ↥X) (p := 2) _ (fun N hN => hN.2) (fun N hN => hN.1)
  have hcore : IsPGroup 2 (Work.GW2.pCore 2 ↥X) := hsup.to_le (Subgroup.normalCore_le _)
  exact hcore.map X.subtype

/-! ## The main theorem -/

theorem Case2S0_comm_U (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B)
    (h : Work.GW2.Case2Ctx B) (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) :
    ⁅B.S0, B.U⁆ = ⊥ := by
  -- `S ≤ E = layerIn M` (§4 (9))
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := S_le_layerIn h
  have hSleHM : (B.S : Subgroup G) ≤ h.D.M ⊓ B.H := by
    intro x hx
    exact ⟨Work.GW2.Case2Ctx.S_le_M h hx, B.S_le_H hx⟩
  have hS0leS : B.S0 ≤ (B.S : Subgroup G) := B.S0_le
  have hS0leHM : B.S0 ≤ h.D.M ⊓ B.H := by
    intro x hx
    have h := hSleHM (hS0leS hx)
    exact ⟨h.1, h.2⟩
  -- 1. Bender p. 224/227: `⁅K, S₀⁆ = ⊥` (the `E`-part of the argument).
  -- `E ⊓ H = C_E(t) ≅ DihedralGroup n`; the image of `K` there has odd order, the image of `S₀`
  -- is cyclic and contains `t`, and `K ≤ C(t)`; the dihedral computation
  -- `Work.CORE4.dihedral_odd_cyclic_comm` then gives the claim.
  have hKS0 : ⁅h.D.K, B.S0⁆ = ⊥ := by
    obtain ⟨p, m, hp, hpodd, _h7le, ⟨φ⟩, hSE9⟩ := h.nine
    haveI := hp
    have htE : B.t ∈ Work.GW2.layerIn h.D.M := h.D.t_mem
    have htE2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn h.D.M)) = 2 := by
      rw [Subgroup.orderOf_mk, B.t_order]
    have ht' : orderOf (φ ⟨B.t, htE⟩) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact htE2
    obtain ⟨n, _hn, ⟨ψ⟩⟩ :=
      I.toolkit.l2cent p m hpodd (by omega : 5 ≤ p ^ m) (φ ⟨B.t, htE⟩) ht'
    let Ψ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H) ≃* DihedralGroup n :=
      (((Subgroup.subgroupOfEquivOfLe (inf_le_left : Work.GW2.layerIn h.D.M ⊓ B.H ≤
          Work.GW2.layerIn h.D.M)).symm.trans
        (MulEquiv.subgroupCongr (subgroupOf_inf_centralizer (Work.GW2.layerIn h.D.M) B.t htE))).trans
        (centralizerSingletonMulEquiv (φ : ↥(Work.GW2.layerIn h.D.M) ≃* PSL(2, GaloisField p m))
          ⟨B.t, htE⟩)).trans ψ
    have hKle : h.D.K ≤ Work.GW2.layerIn h.D.M ⊓ B.H := fun k hk =>
      ⟨K_le_layerIn B h hk, B.U_le_H (h.D.K_le_U B hk)⟩
    have hS0le : B.S0 ≤ Work.GW2.layerIn h.D.M ⊓ B.H := fun s hs =>
      ⟨hSE9 (hS0leS hs), B.S_le_H (hS0leS hs)⟩
    set A : Subgroup (DihedralGroup n) :=
      (h.D.K.subgroupOf (Work.GW2.layerIn h.D.M ⊓ B.H)).map
        (Ψ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H) →* DihedralGroup n) with hA
    set B' : Subgroup (DihedralGroup n) :=
      (B.S0.subgroupOf (Work.GW2.layerIn h.D.M ⊓ B.H)).map
        (Ψ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H) →* DihedralGroup n) with hB'
    have hAodd : Odd (Nat.card A) := by
      rw [hA, Subgroup.card_map_of_injective Ψ.injective]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]
      exact Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (h.D.K_le_U B))
    have hBcyc : IsCyclic B' := by
      rw [hB']
      exact (Subgroup.equivMapOfInjective (B.S0.subgroupOf (Work.GW2.layerIn h.D.M ⊓ B.H))
        Ψ.toMonoidHom Ψ.injective).isCyclic.mp
        ((Subgroup.subgroupOfEquivOfLe hS0le).isCyclic.mpr B.S0_cyclic)
    have htB : Ψ ⟨B.t, hS0le B.t_mem⟩ ∈ B' := by
      rw [hB']
      exact Subgroup.mem_map.mpr
        ⟨⟨B.t, hS0le B.t_mem⟩, by rw [Subgroup.mem_subgroupOf]; exact B.t_mem, rfl⟩
    have ht2 : orderOf (Ψ ⟨B.t, hS0le B.t_mem⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, B.t_order]
    have hcent : A ≤ Subgroup.centralizer ({Ψ ⟨B.t, hS0le B.t_mem⟩} :
        Set (DihedralGroup n)) := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      have hk : (x : G) ∈ h.D.K := Subgroup.mem_subgroupOf.mp hx
      have hct : B.t * (x : G) = (x : G) * B.t :=
        Subgroup.mem_centralizer_iff.mp (show (x : G) ∈ Subgroup.centralizer ({B.t} : Set G) from
          B.U_le_H (h.D.K_le_U B hk)) B.t (by simp)
      have h2 : (⟨B.t, hS0le B.t_mem⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) * x =
          x * ⟨B.t, hS0le B.t_mem⟩ := by
        apply Subtype.ext
        simpa using hct
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc Ψ ⟨B.t, hS0le B.t_mem⟩ * Ψ x
          = Ψ (⟨B.t, hS0le B.t_mem⟩ * x) := by rw [map_mul]
        _ = Ψ (x * ⟨B.t, hS0le B.t_mem⟩) := by rw [h2]
        _ = Ψ x * Ψ ⟨B.t, hS0le B.t_mem⟩ := by rw [map_mul]
    have hAB : ⁅A, B'⁆ = ⊥ := dihedral_odd_cyclic_comm A B' hAodd hBcyc htB ht2 hcent
    have hAcen : A ≤ Subgroup.centralizer (B' : Set (DihedralGroup n)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hAmem : Ψ ⟨k, hKle hk⟩ ∈ A := by
      rw [hA]
      exact Subgroup.mem_map.mpr
        ⟨⟨k, hKle hk⟩, by rw [Subgroup.mem_subgroupOf]; exact hk, rfl⟩
    have hBmem : Ψ ⟨s, hS0le hs⟩ ∈ B' := by
      rw [hB']
      exact Subgroup.mem_map.mpr
        ⟨⟨s, hS0le hs⟩, by rw [Subgroup.mem_subgroupOf]; exact hs, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hAcen hAmem) (Ψ ⟨s, hS0le hs⟩) hBmem
    have h2 : Ψ ((⟨s, hS0le hs⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) * ⟨k, hKle hk⟩) =
        Ψ (⟨k, hKle hk⟩ * ⟨s, hS0le hs⟩) := by
      rw [map_mul, map_mul]
      exact h1
    exact congrArg Subtype.val (Ψ.injective h2)
  have hKS0' : h.D.K ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKS0
  -- 2. `B₀ = (U ⊓ M) ⊓ C(S ⊓ E)`, hence `⁅B₀, S₀⁆ = ⊥`
  have hB0le : h.D.B0 ≤
      Subgroup.centralizer ((((B.S : Subgroup G)) ⊓ Work.GW2.layerIn h.D.M : Subgroup G) : Set G) :=
    hplus.2.2 ▸ inf_le_right
  have hS0infE : B.S0 ≤ ((B.S : Subgroup G)) ⊓ Work.GW2.layerIn h.D.M := by
    intro x hx
    exact ⟨hS0leS hx, hSE (hS0leS hx)⟩
  have hB0S0' : h.D.B0 ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) :=
    hB0le.trans (Subgroup.centralizer_le (fun x hx => hS0infE hx))
  -- 3. `U ⊓ M = K ⊔ B₀` lies in `C_G(S₀)`
  have hUMS0' : B.U ⊓ h.D.M ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) := by
    rw [Work.GW2.Case2Pre.U_eq B h.D h.pre]
    exact sup_le hKS0' hB0S0'
  have hUMS0 : (B.U ⊓ h.D.M) ≤ Subgroup.normalizer ((B.S0 : Subgroup G) : Set G) :=
    hUMS0'.trans (Subgroup.centralizer_le_normalizer _)
  -- 4. `S₀ ⊴ S` (index two) and `H ⊓ M = (U ⊓ M) ⊔ S`, so `S₀ ⊴ H ⊓ M`
  have hS0S_normal : (B.S0.subgroupOf (B.S : Subgroup G)).Normal := by
    refine Subgroup.normal_of_index_eq_two ?_
    simpa [Subgroup.relIndex] using B.S0_index
  have hS_le_N : (B.S : Subgroup G) ≤ Subgroup.normalizer ((B.S0 : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer B.S0_le).mp hS0S_normal
  have hHM_le_N : h.D.M ⊓ B.H ≤ Subgroup.normalizer ((B.S0 : Subgroup G) : Set G) := by
    rw [Work.GW2.Case2Ctx.inter_H_M I h]
    exact sup_le hUMS0 hS_le_N
  have hS0_normal : (B.S0.subgroupOf (h.D.M ⊓ B.H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS0leHM).mpr hHM_le_N
  -- 5. `S₀ ≤ O₂(H ⊓ M) = O₂(H)` (§4 (7))
  have hS0_pg : IsPGroup 2 (B.S0.subgroupOf (h.D.M ⊓ B.H)) := by
    have h1 : IsPGroup 2 ↥((B.S : Subgroup G).subgroupOf (h.D.M ⊓ B.H)) :=
      (B.S.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe hSleHM).symm
    exact h1.to_le (Subgroup.subgroupOf_mono (h.D.M ⊓ B.H) hS0leS)
  have hS0_pcore : B.S0 ≤ Work.GW2.pCoreIn 2 (h.D.M ⊓ B.H) :=
    le_pCoreIn_of_normal_isPGroup_s0 hS0leHM hS0_normal hS0_pg
  have hS0_pcoreH : B.S0 ≤ Work.GW2.pCoreIn 2 B.H := by
    rw [← h7.1, inf_comm]
    exact hS0_pcore
  -- 6. `O₂(H) ⊓ U = 1`
  have hXUbot : Work.GW2.pCoreIn 2 B.H ⊓ B.U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxX, hxU⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨m, hm⟩ := (isPGroup_pCoreIn_two (B.H)).exists_card_eq
    have h1 : orderOf x ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.orderOf_dvd_natCard _ hxX
    have h2 : orderOf x ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U hxU
    have hodd : Odd (orderOf x) := Odd.of_dvd_nat B.U_odd h2
    obtain ⟨k, _hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h' | h'
      · exact h'
      · exact absurd (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h')))
          (Nat.not_even_iff_odd.mpr (hk' ▸ hodd))
    exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])
  -- 7. `O₂(H)` normal in `H`, `U ◁ H` odd of coprime order, so `O₂(H) ≤ C_G(U)`
  have hXleH : Work.GW2.pCoreIn 2 B.H ≤ B.H := Subgroup.map_subtype_le _
  have hXsub : (Work.GW2.pCoreIn 2 B.H).subgroupOf B.H = Work.GW2.pCore 2 ↥B.H := by
    rw [Work.GW2.pCoreIn, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective B.H.subtype_injective _
  have hXn : ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H).Normal := by
    rw [hXsub]
    exact Work.GW2.pCore_normal 2 ↥B.H
  have hX_le_C : Work.GW2.pCoreIn 2 B.H ≤
      Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    haveI : ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H).Normal := hXn
    haveI : (B.U.subgroupOf B.H).Normal := B.U_normal
    have hinf : ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H) ⊓ (B.U.subgroupOf B.H) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have hyX : (y : G) ∈ Work.GW2.pCoreIn 2 B.H := by
        rwa [Subgroup.mem_subgroupOf] at hy1
      have hyU : (y : G) ∈ B.U := by rwa [Subgroup.mem_subgroupOf] at hy2
      refine Subtype.ext ?_
      have : (y : G) ∈ (⊥ : Subgroup G) := by
        rw [← hXUbot]
        exact ⟨hyX, hyU⟩
      simpa using this
    have hcomm : ⁅(Work.GW2.pCoreIn 2 B.H).subgroupOf B.H,
        (B.U.subgroupOf B.H)⁆ = ⊥ := by
      have h := Subgroup.commutator_le_inf ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H)
        (B.U.subgroupOf B.H)
      rw [hinf] at h
      exact le_bot_iff.mp h
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hx' : (⟨x, hXleH hx⟩ : ↥B.H) ∈ (Work.GW2.pCoreIn 2 B.H).subgroupOf B.H := by
      rwa [Subgroup.mem_subgroupOf]
    have hu' : (⟨u, B.U_le_H hu⟩ : ↥B.H) ∈ B.U.subgroupOf B.H := by
      rwa [Subgroup.mem_subgroupOf]
    have h1 : (⟨u, B.U_le_H hu⟩ : ↥B.H) * ⟨x, hXleH hx⟩ =
        ⟨x, hXleH hx⟩ * (⟨u, B.U_le_H hu⟩ : ↥B.H) :=
      Subgroup.mem_centralizer_iff.mp (hcen hx') _ hu'
    exact congrArg Subtype.val h1
  -- 8. Conclusion
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hS0_pcoreH.trans hX_le_C)

end Work.CORE4
