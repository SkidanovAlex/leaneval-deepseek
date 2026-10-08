import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn
import Submission.Work.CORE2A.bswHyps2_of_config2
import Submission.Work.CORE2A.coprime_invSet_index
import Submission.Work.BSW.Basic
import Submission.OddOrder.Isaacs.Ch05_Transfer.Basic
import Submission.OddOrder.Isaacs.Ch05_Transfer.SylowTwoDirectFactor

namespace Work.CORE2A

open Subgroup
open scoped commutatorElement

/-! ## Auxiliary facts about Bender's situation -/

theorem centralizer_zpowers_eq_singleton {G : Type} [Group G] (s : G) :
    Subgroup.centralizer (Subgroup.zpowers s : Set G) = Subgroup.centralizer ({s} : Set G) := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx s (Subgroup.mem_zpowers s)
  · rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute s x from hx s (by simp)) k).eq

/-- In Bender's minimal-counterexample context the Sylow 2-subgroup `S` is dihedral of order
`2n` with `n ≥ 2`. -/
theorem bender_sylow_dihedral {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have hnonab : ¬ IsMulCommutative G := by
    rintro h; obtain ⟨a, b, hab⟩ := hctx.nonab; exact hab (h.is_comm.comm a b)
  have hne : (B.S : Subgroup G) ≠ ⊥ := fun h => by
    have ht : B.t ∈ (⊥ : Subgroup G) := by rw [← h]; exact B.S0_le B.t_mem
    exact bSetup_t_ne_one B (by simpa using ht)
  rcases hctx.sylow B.S with hc | ⟨n, ⟨e⟩⟩
  · haveI : IsCyclic ↥(B.S : Subgroup G) := hc
    exact absurd
      ((OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two hnonab B.S hne)
        hctx.simple) id
  · refine ⟨n, ?_, ⟨e⟩⟩
    have h1 : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h2 : Nat.card ↥(B.S : Subgroup G) = 2 * Nat.card B.S0 := bSetup_card_S_eq B
    have hdvd : 2 ∣ Nat.card B.S0 := by
      rw [← B.t_order]; exact Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
    haveI : Nonempty ↥B.S0 := ⟨⟨1, B.S0.one_mem⟩⟩
    have h3 : 2 ≤ Nat.card B.S0 := Nat.le_of_dvd Nat.card_pos hdvd
    have h4 : 2 * n = 2 * Nat.card B.S0 := by rw [← h1, h2]
    omega

/-- In Bender's context there is no normal subgroup of index two. -/
theorem bender_no_index_two {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hNidx
  haveI := hN
  haveI := hctx.simple
  have hne_top : N ≠ ⊤ := by intro h; rw [h] at hNidx; simp at hNidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hNidx' : (⊥ : Subgroup G).index = 2 := hbot ▸ hNidx
    have h1 : (⊥ : Subgroup G).index = Nat.card G := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
    have hcard : Nat.card G = 2 := h1.symm.trans hNidx'
    have hcardT : Nat.card ↥(Subgroup.zpowers B.t) = 2 := by
      rw [Nat.card_zpowers]; exact B.t_order
    have hT : Subgroup.zpowers B.t = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardT, hcard])
    have hcomm : IsMulCommutative G := by
      refine IsMulCommutative.of_comm fun a b => ?_
      have ha : a ∈ Subgroup.zpowers B.t := by rw [hT]; exact Subgroup.mem_top a
      have hb : b ∈ Subgroup.zpowers B.t := by rw [hT]; exact Subgroup.mem_top b
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add, add_comm, zpow_add]
    obtain ⟨a, b, hab⟩ := hctx.nonab
    exact hab (hcomm.is_comm.comm a b)
  · exact hne_top htop

/-- `B.U = O(B.H)` is normal in `B.H`; consequently `B.H ≤ N_G(B.U)`. -/
theorem bender_H_le_normalizer_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.H ≤ Subgroup.normalizer (B.U : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ (Work.GW2.oddCore ↥B.H).map B.H.subtype := hx
    obtain ⟨n, hn, rfl⟩ := hx'
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹,
      (inferInstance : (Work.GW2.oddCore ↥B.H).Normal).conj_mem n hn ⟨h, hh⟩, by simp⟩
  · intro hx
    have hx' : h * x * h⁻¹ ∈ (Work.GW2.oddCore ↥B.H).map B.H.subtype := hx
    obtain ⟨n, hn, hneq⟩ := hx'
    refine ⟨⟨h, hh⟩⁻¹ * n * ⟨h, hh⟩, ?_, ?_⟩
    · simpa using (inferInstance : (Work.GW2.oddCore ↥B.H).Normal).conj_mem n hn ⟨h, hh⟩⁻¹
    · rw [show B.H.subtype (⟨h, hh⟩⁻¹ * n * ⟨h, hh⟩) = h⁻¹ * B.H.subtype n * h by
        simp only [map_mul, Subgroup.coe_subtype, Subgroup.coe_inv]]
      rw [hneq]; group

/-- `s ∈ S ≤ H` normalizes `U`. -/
theorem bender_s_mem_normalizer_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    {s : G} (hs : s ∈ (B.S : Subgroup G)) :
    s ∈ Subgroup.normalizer (B.U : Set G) :=
  bender_H_le_normalizer_U B (bSetup_S_le_H B hs)

/-- `s ∈ S` lies in `B.H = C(t)`. -/
theorem bender_s_mem_H {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    {s : G} (hs : s ∈ (B.S : Subgroup G)) : s ∈ B.H :=
  bSetup_S_le_H B hs

/-- Bender 1.1: `U = ⁅<\s>, U⁆ ⊔ C_U(s)`. -/
theorem bender_commutator_sup_fixed {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (B : Work.GW2.BenderSetup G) (s : G)
    (hsS : s ∈ (B.S : Subgroup G)) (hsord : orderOf s = 2) :
    (⁅Subgroup.zpowers s, B.U⁆ : Subgroup G) ⊔ (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) =
      B.U := by
  have hnorm : Subgroup.zpowers s ≤ Subgroup.normalizer (B.U : Set G) :=
    Subgroup.zpowers_le.mpr (bender_s_mem_normalizer_U B hsS)
  have hp : IsPGroup 2 (Subgroup.zpowers s : Subgroup G) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hsord]
    norm_num
  have hcp : Nat.Coprime 2 (Nat.card B.U) :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr fun h =>
      (Nat.not_even_iff_odd.mpr (bSetup_U_odd B)) (even_iff_two_dvd.mpr h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (T.c11i G 2 (Subgroup.zpowers s) B.U hp hcp hnorm).2

/-- Each commutator `⁅s, b⁆` with `b ∈ U` lies in `I_U(s)`, where `s` is an involution
normalizing `U`. -/
theorem bender_commutator_mem_invSet {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) {s b : G} (hsS : s ∈ (B.S : Subgroup G))
    (hb : b ∈ B.U) (hss : s * s = 1) :
    ⁅s, b⁆ ∈ Work.GW2.invSet B.U s := by
  have hssi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hsN : s ∈ Subgroup.normalizer (B.U : Set G) := bender_s_mem_normalizer_U B hsS
  have hsbU : s * b * s⁻¹ ∈ B.U := (Subgroup.mem_normalizer_iff.mp hsN b).mp hb
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact B.U.mul_mem hsbU (B.U.inv_mem hb)
  · rw [commutatorElement_def, hssi]
    rw [show (s * b * s * b⁻¹)⁻¹ = b * s * b⁻¹ * s by
      simp only [mul_inv_rev, inv_inv, hssi]
      group]
    calc s * (s * b * s * b⁻¹) * s = (s * s) * (b * (s * b⁻¹ * s)) := by group
      _ = b * (s * b⁻¹ * s) := by rw [hss, one_mul]
      _ = b * s * b⁻¹ * s := by group

/-- `⁅<\s>, U⁆ ≤ I_U(s)`. -/
theorem bender_commutator_le_invSet {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hss : s * s = 1)
    {I : Subgroup G} (hIiff : ∀ x : G, x ∈ I ↔ x ∈ Work.GW2.invSet B.U s) :
    (⁅Subgroup.zpowers s, B.U⁆ : Subgroup G) ≤ I := by
  have hs2 : s ^ 2 = 1 := by simpa [pow_two] using hss
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [hIiff]
  rcases OddOrder.Isaacs.Ch05.eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hs2 ha with rfl | rfl
  · refine ⟨?_, ?_⟩ <;> rw [commutatorElement_def] <;> simp
  · exact bender_commutator_mem_invSet B hsS hb hss

theorem lemma22 (T : Work.GW2.LocalToolkit) (hC : Work.GW2.BGThmCProp) (hBSW : Work.GW2.BSW2Prop) : Work.GW2.Lemma22Prop := by
  intro G _instG _instFin hFT hctx B hconfig
  obtain ⟨hS0C, s, hsS, hs0, I, hIset, hInorm, hNX⟩ := hconfig
  have hIiff : ∀ x : G, x ∈ I ↔ x ∈ Work.GW2.invSet B.U s := fun x => by
    show (x ∈ (I : Set G)) ↔ x ∈ Work.GW2.invSet B.U s
    rw [hIset]
  obtain ⟨n, hn, hD⟩ := bender_sylow_dihedral hctx B
  have hsord : orderOf s = 2 :=
    dihedral_index_two n hn (B.S : Subgroup G) B.S0 hD B.S0_le B.S0_cyclic B.S0_index s hsS hs0
  have hss : s * s = 1 := by
    have h : s ^ 2 = 1 := by rw [← hsord]; exact pow_orderOf_eq_one s
    simpa [pow_two] using h
  by_cases hUeq : (B.U : Set G) = Work.GW2.invSet B.U s
  · -- Case 1: `U = I_U(s)`
    have hIX : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ B.U → normalizer (X : Set G) ≤ B.H := by
      intro X hX hXU
      exact hNX X hX (by
        intro x hx
        rw [hIiff, ← hUeq]
        exact hXU hx)
    have hbs : Work.GW2.BSWHyps2 G B.t s (B.U ⊔ B.S0) :=
      bswHyps2_of_config2 T hctx B ⟨n, hn, hD⟩ s hsS hs0 hsord hUeq hS0C hIX
    obtain ⟨p, k, hp, hpodd, h5, hiso⟩ := hBSW G hctx.simple hctx.nonab B.t s _ hbs
    exact hiso.elim fun iso => (hctx.notPSL p k hp hpodd h5).false iso
  · -- Case 2: `U ≠ I_U(s)`; Bender–Glauberman Theorem C gives a contradiction
    have hPK : (⁅Subgroup.zpowers s, B.U⁆ : Subgroup G) ⊔
        (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) = B.U :=
      bender_commutator_sup_fixed T B s hsS hsord
    have hcomm_le : (⁅Subgroup.zpowers s, B.U⁆ : Subgroup G) ≤ I :=
      bender_commutator_le_invSet B hsS hss hIiff
    have hIU : I ≤ B.U := fun x hx => ((hIiff x).mp hx).1
    have hUdecomp : I ⊔ (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) = B.U := by
      refine le_antisymm (sup_le hIU inf_le_left) ?_
      calc B.U = (⁅Subgroup.zpowers s, B.U⁆ : Subgroup G) ⊔
            (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) := hPK.symm
        _ ≤ I ⊔ (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) :=
            sup_le_sup hcomm_le le_rfl
    have hCne : B.U ⊓ centralizer (Subgroup.zpowers s : Set G) ≠ ⊥ := by
      intro hbot
      apply hUeq
      have hIU : (B.U : Set G) = (I : Set G) := by rw [← hUdecomp, hbot, sup_bot_eq]
      rw [hIU, hIset]
    -- a generator of `S0`
    obtain ⟨z, hz⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top B.S0).mp B.S0_cyclic
    have hzS0 : z ∈ B.S0 := by rw [← hz]; exact Subgroup.mem_zpowers z
    have hzS : z ∈ (B.S : Subgroup G) := B.S0_le hzS0
    have hzx : ∀ x ∈ B.U, z * x = x * z := fun x hx =>
      ((Subgroup.mem_centralizer_iff.mp (hS0C hzS0)) x hx).symm
    -- the second reflection
    have ht2mem : s * z ∈ (B.S : Subgroup G) := (B.S : Subgroup G).mul_mem hsS hzS
    have ht2not : s * z ∉ B.S0 := by
      intro hmem
      apply hs0
      have : s = (s * z) * z⁻¹ := by group
      rw [this]
      exact B.S0.mul_mem hmem (B.S0.inv_mem hzS0)
    have ht2ord : orderOf (s * z) = 2 :=
      dihedral_index_two n hn (B.S : Subgroup G) B.S0 hD B.S0_le B.S0_cyclic B.S0_index
        (s * z) ht2mem ht2not
    have hgen : B.S0 = Subgroup.zpowers (s * (s * z)) := by
      rw [show s * (s * z) = z by rw [← mul_assoc, hss, one_mul], ← hz]
    -- the `BGData`
    let D : Work.GW2.BGData G :=
      { S := B.S
        n := n
        two_le := hn
        dih := hD
        oneClass := (T.fus G B.S n hn hD (bender_no_index_two hctx B)).1
        S0 := B.S0
        S0_le := B.S0_le
        S0_cyclic := B.S0_cyclic
        S0_index := B.S0_index
        t := B.t
        t_mem := B.t_mem
        t_order := B.t_order
        t1 := s
        t2 := s * z
        t1_mem := hsS
        t2_mem := ht2mem
        t1_nmem := hs0
        t2_nmem := ht2not
        t1_order := hsord
        t2_order := ht2ord
        gen := hgen }
    -- odd subgroups of `H` are contained in `U`
    have hodd_sub : ∀ X : Subgroup G, X ≤ B.H → Odd (Nat.card X) → X ≤ B.U :=
      odd_subgroup_le_oddCoreIn B.H B.U (B.S : Subgroup G) (bSetup_U_eq B)
        (T.split G B.S n hn hD B.t (B.S0_le B.t_mem) B.t_order
          (fun x hx => ((Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hx)) B.t (by simp)).symm))
        B.S.isPGroup'
    -- the index of `H` is coprime to `|I|`
    have hcop : Nat.Coprime (Nat.card I) (B.H).index :=
      coprime_invSet_index hFT hctx B s hsS hs0 hsord I hIset hInorm hNX hS0C
    have hoddI : Odd (Nat.card I) := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      rw [even_iff_two_dvd] at hev
      exact (Nat.not_even_iff_odd.mpr (bSetup_U_odd B))
        (even_iff_two_dvd.mpr (dvd_trans hev (card_dvd_of_le hIU)))
    -- `I` is the largest odd subgroup of `H = C(t)` inverted by `D.t1 = s`
    have hmax1 : Work.GW2.IsMaxInverted D.H D.t1 I := by
      refine ⟨le_trans hIU (bSetup_U_le_H B), hoddI, ?_, ?_⟩
      · intro x hx; exact ((hIiff x).mp hx).2
      · intro X hXH hXodd hinv x hx
        exact (hIiff x).mpr ⟨hodd_sub X hXH hXodd hx, hinv x hx⟩
    -- the same for `D.t2 = s * z`
    have hmax2 : Work.GW2.IsMaxInverted D.H D.t2 I := by
      have hinv : ∀ x ∈ I, (s * z) * x * (s * z)⁻¹ = x⁻¹ := by
        intro x hx
        have hxU : x ∈ B.U := ((hIiff x).mp hx).1
        rw [mul_inv_rev]
        calc (s * z) * x * (z⁻¹ * s⁻¹) = s * (z * x) * (z⁻¹ * s⁻¹) := by group
          _ = s * (x * z) * (z⁻¹ * s⁻¹) := by rw [hzx x hxU]
          _ = s * x * s⁻¹ := by group
          _ = x⁻¹ := ((hIiff x).mp hx).2
      refine ⟨le_trans hIU (bSetup_U_le_H B), hoddI, hinv, ?_⟩
      intro X hXH hXodd hXinv x hx
      have hXU : X ≤ B.U := hodd_sub X hXH hXodd
      refine (hIiff x).mpr ⟨hXU hx, ?_⟩
      have h1 : (s * z) * x * (s * z)⁻¹ = s * x * s⁻¹ := by
        rw [mul_inv_rev]
        calc (s * z) * x * (z⁻¹ * s⁻¹) = s * (z * x) * (z⁻¹ * s⁻¹) := by group
          _ = s * (x * z) * (z⁻¹ * s⁻¹) := by rw [hzx x (hXU hx)]
          _ = s * x * s⁻¹ := by group
      rw [← h1]; exact hXinv x hx
    -- identifications of the `BGData` projections
    have hDB1 : (D.B1 : Subgroup G) = B.U ⊓ centralizer (Subgroup.zpowers s : Set G) := by
      show B.U ⊓ Subgroup.centralizer ({s} : Set G) = _
      rw [centralizer_zpowers_eq_singleton]
    have hDB : (D.B : Subgroup G) = B.U ⊓ centralizer (Subgroup.zpowers s : Set G) := by
      show (B.U ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
        (B.U ⊓ Subgroup.centralizer ({s * z} : Set G)) =
          B.U ⊓ Subgroup.centralizer (Subgroup.zpowers s : Set G)
      rw [centralizer_zpowers_eq_singleton]
      refine le_antisymm inf_le_left (le_inf le_rfl ?_)
      intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxU, hxC⟩ := hx
      rw [Subgroup.mem_inf]
      refine ⟨hxU, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hxs : s * x = x * s := hxC s (by simp)
      have hxz : z * x = x * z := hzx x hxU
      calc (s * z) * x = s * (z * x) := by group
        _ = s * (x * z) := by rw [hxz]
        _ = (s * x) * z := by group
        _ = (x * s) * z := by rw [hxs]
        _ = x * (s * z) := by group
    have hIC : I ⊓ (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨hxI, hxU, hxC⟩
      have hxs : s * x * s⁻¹ = x⁻¹ := ((hIiff x).mp hxI).2
      have hxs' : s * x * s⁻¹ = x := by
        have h1 : s * x = x * s := (Subgroup.mem_centralizer_iff.mp hxC) s (Subgroup.mem_zpowers s)
        rw [h1]; group
      have hx2 : x * x = 1 := by
        have hxinv : x = x⁻¹ := by rw [hxs'] at hxs; exact hxs
        exact (mul_eq_one_iff_eq_inv).mpr hxinv
      have hdvd : orderOf x ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hx2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        have h2dvd : 2 ∣ Nat.card B.U := by
          rw [← h]; exact Subgroup.orderOf_dvd_natCard B.U hxU
        exact (Nat.not_even_iff_odd.mpr (bSetup_U_odd B)) (even_iff_two_dvd.mpr h2dvd)
    have hdir : Work.GW2.IsInternalDirect D.U (D.B1 ⊓ I) (D.B ⊔ (I ⊓ I)) := by
      have hA : (D.B1 ⊓ I : Subgroup G) = ⊥ := by
        calc (D.B1 ⊓ I : Subgroup G)
            = (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) ⊓ I := by rw [hDB1]
          _ = I ⊓ (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) := by rw [inf_comm]
          _ = ⊥ := hIC
      have hC' : (D.B ⊔ (I ⊓ I) : Subgroup G) = B.U := by
        calc (D.B ⊔ (I ⊓ I) : Subgroup G)
            = (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) ⊔ I := by rw [hDB, inf_idem]
          _ = B.U := by rw [sup_comm]; exact hUdecomp
      refine ⟨?_, ?_, ?_⟩
      · rw [hA, hC', bot_sup_eq]
      · rw [hA, bot_inf_eq]
      · intro a ha c hc
        have ha1 : a = 1 := by rw [hA] at ha; exact Subgroup.mem_bot.mp ha
        rw [ha1, one_mul, mul_one]
    have hBne : ⁅D.B, D.B⁆ ≠ D.B := by
      have hBU : (D.B : Subgroup G) ≤ B.U := by rw [hDB]; exact inf_le_left
      haveI : Group.IsSolvable ↥B.U := hFT ↥B.U (bSetup_U_odd B)
      set K : Subgroup ↥B.U := (D.B : Subgroup G).subgroupOf B.U with hK
      have hmapK : K.map B.U.subtype = (D.B : Subgroup G) := by
        rw [hK, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBU]
      have hKne : K ≠ ⊥ := by
        intro h
        have hbot : (D.B : Subgroup G) = ⊥ := by rw [← hmapK, h, Subgroup.map_bot]
        exact hCne (by rw [← hDB]; exact hbot)
      have hlt : ⁅K, K⁆ < K := Group.IsSolvable.commutator_lt_of_ne_bot hKne
      intro hcomm
      have hEq : ⁅K, K⁆ = K := by
        apply (Subgroup.map_injective (f := B.U.subtype) (Subtype.val_injective))
        rw [Subgroup.map_commutator, hmapK]
        exact hcomm
      exact absurd hEq (ne_of_lt hlt)
    have hfrob : (D.U ≠ D.B ⊔ (I ⊓ I) →
        Work.GW2.IsFrobeniusWith (D.B ⊔ (I ⊓ I)) (I ⊓ I) D.B) := by
      intro h
      refine absurd ?_ h
      calc D.U = B.U := rfl
        _ = I ⊔ (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) := hUdecomp.symm
        _ = (B.U ⊓ centralizer (Subgroup.zpowers s : Set G)) ⊔ I :=
              sup_comm I (B.U ⊓ centralizer (Subgroup.zpowers s : Set G))
        _ = D.B ⊔ (I ⊓ I) := by rw [hDB, inf_idem]
    exact (hC G D I I hmax1 hmax2 hdir (by rw [inf_idem]; exact hcop) hBne hfrob)
      hctx.simple

end Work.CORE2A
