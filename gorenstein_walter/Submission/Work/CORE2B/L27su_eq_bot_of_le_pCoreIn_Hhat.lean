import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.UNeBotProp_of_h22_proved
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

/-!
# `Work.CORE2B.L27su_eq_bot_of_le_pCoreIn_Hhat`

Bender 1981, proof of Lemma 2.7 (p. 221):

> "As `O₂(M)` centralizes `M ∩ F_{2'}(Ĥ) = M ∩ F(U)`, 1.1.iv implies `[O₂(M),U] = 1`, hence
> `O₂(M) ⊆ O₂(Ĥ)`, hence `O₂(M) = 1`."

This file proves the second half of that sentence, with the first half supplied as the
hypothesis `pCoreIn 2 M ≤ pCoreIn 2 B.Hhat`: if `M` satisfies the hypotheses of Lemma 2.7
(`L27Hyp B M`) and `O₂(M) ≤ O₂(Ĥ)`, then `O₂(M) = ⊥`.

## The argument

Write `P = O₂(M)`, `V = O₂(Ĥ)`, and suppose `P ≠ ⊥` (so `V ≠ ⊥`).

* `P ◁ M`, so `M ≤ N_G(P)`; `V ◁ Ĥ` and `V ≤ Ĥ`, so `Ĥ ≤ N_G(V)`.  Since `Ĥ` is a coatom of
  the simple group `G` and `V ≠ ⊥`, `N_G(V) = Ĥ` (`normalizer_eq_of_coatom_aux`).  Similarly,
  for any involution `z ∈ V#` that is normalized by `M`, `N_G(⟨z⟩) = C_G(z) = Ĥ`.
* Theorem 2.6 gives `V = S ⊓ C(U) ∋ t` together with the dichotomy "`V ≤ S₀`" or "`V` is a
  four-group".
  - If `V ≤ S₀`, then `V` is cyclic (it is a subgroup of the cyclic `S₀`), so it has a unique
    involution, which therefore is `t`.  A nontrivial `2`-group `P ≠ ⊥` contains an involution
    `z`, and `z ∈ V`, so `z = t ∈ P`.  Since `M` normalizes `P ≤ S₀`, any conjugate
    `m t m⁻¹` (`m ∈ M`) is an involution of the cyclic group `S₀`, hence equals `t`: thus
    `M ≤ C_G(t) = B.H ≤ Ĥ`, contradicting `¬ M ≤ Ĥ`.
  - If `V` is a four-group, then either `P = V`, in which case `M ≤ N_G(P) = N_G(V) = Ĥ`; or
    `|P| = 2`, so `P = ⟨z⟩` for an involution `z ∈ V`.  Then `M ≤ C_G(z)`, and the fusion
    property `T.fus` ("`N_G(W)` is transitive on `W#` for every four-group `W`") applied to
    `W = V` writes `z = h t h⁻¹` with `h ∈ N_G(V) = Ĥ`; conjugating the inclusion
    `C_G(t) = B.H ≤ Ĥ` by `h ∈ Ĥ` gives `C_G(z) ≤ Ĥ`, hence `M ≤ Ĥ`, again a contradiction.

All hypotheses of the statement are thus used except `h22` (which is retained for interface
compatibility; the coatom argument above only needs `BenderCtx.simple`).
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. Elementary helpers -/

/-- The image in `G` of a normal subgroup of `↥K` is normalized by `K`. -/
theorem le_normalizer_map_subtype_aux {G : Type} [Group G] (K : Subgroup G) (N : Subgroup ↥K)
    [N.Normal] : K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk y hy
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨(⟨k, hk⟩ : ↥K) * z * (⟨k, hk⟩ : ↥K)⁻¹, ?_, ?_⟩
  · exact (inferInstance : N.Normal).conj_mem z hz (⟨k, hk⟩ : ↥K)
  · have hcoe : K.subtype ((⟨k, hk⟩ : ↥K) * z * (⟨k, hk⟩ : ↥K)⁻¹) = k * K.subtype z * k⁻¹ := by
      simp
    rw [hcoe, hzy]

/-- A finite cyclic group has at most one element of order two. -/
theorem eq_of_orderOf_eq_two_of_isCyclic_aux {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {a b : H} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have hfin : Fintype H := Fintype.ofFinite H
  have hd : 2 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← ha]
    exact orderOf_dvd_natCard a
  have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
  exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)

/-- For a coatomic `K` of a finite simple group, a nontrivial `Z ≤ K` normalized by `K`
satisfies `N_G(Z) = K`. -/
theorem normalizer_eq_of_coatom_aux {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K Z : Subgroup G} (hK : IsCoatom K) (hZK : Z ≤ K) (hZ : Z ≠ ⊥)
    (hKnorm : K ≤ Subgroup.normalizer (Z : Set G)) :
    Subgroup.normalizer (Z : Set G) = K := by
  rcases lt_or_eq_of_le hKnorm with hlt | heq
  · have htop : Subgroup.normalizer (Z : Set G) = ⊤ := hK.lt_iff.mp hlt
    haveI hZn : Z.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases Subgroup.Normal.eq_bot_or_eq_top Z with hbot | htopZ
    · exact absurd hbot hZ
    · exact absurd (top_le_iff.mp (htopZ ▸ hZK)) hK.ne_top
  · exact heq.symm

/-- A nontrivial finite `2`-group contains an element of order `2`. -/
theorem exists_orderOf_eq_two_of_isPGroup_two_aux {G : Type} [Group G] [Finite G]
    (P : Subgroup G) (hpg : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ z ∈ P, orderOf z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard1 : Nat.card ↥P ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  rcases hpg.card_eq_or_dvd with h | h
  · exact absurd h hcard1
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
    exact ⟨(x : G), x.2, by rw [← Subgroup.orderOf_mk]; exact hx⟩

/-! ## 2. The main theorem -/

theorem L27su_eq_bot_of_le_pCoreIn_Hhat :
    ∀ (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop) (h26 : Work.GW2.Thm26Prop)
      (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        Work.GW2.pCoreIn 2 M ≤ Work.GW2.pCoreIn 2 B.Hhat →
        Work.GW2.pCoreIn 2 M = ⊥ := by
  intro T h22 h26 G _ _ hFT hCtx B M hD hle
  by_contra hPne0
  haveI hSimple : IsSimpleGroup G := hCtx.simple
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hVdef
  set P : Subgroup G := Work.GW2.pCoreIn 2 M with hPdef
  have hPleV : P ≤ V := by rw [hPdef, hVdef]; exact hle
  have hPne : P ≠ ⊥ := by rw [hPdef]; exact hPne0
  have hVne : V ≠ ⊥ := fun h => hPne (le_bot_iff.mp (hPleV.trans (le_of_eq h)))
  -- Theorem 2.6
  obtain ⟨h26a, h26b, h26c⟩ := h26 G hFT hCtx B
  -- `t ∈ O₂(Ĥ)`
  have htV : B.t ∈ V := by
    rw [hVdef, ← h26b]
    refine ⟨B.S0_le B.t_mem, ?_⟩
    show B.t ∈ Subgroup.centralizer (B.U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huH : u ∈ B.H := Subgroup.map_subtype_le _ hu
    exact (Subgroup.mem_centralizer_iff.mp huH B.t rfl).symm
  -- `Ĥ ≤ N_G(V)`
  have hHhat_le_NV : B.Hhat ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef]
    exact le_normalizer_map_subtype_aux B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  have hVleHhat : V ≤ B.Hhat := by rw [hVdef]; exact Subgroup.map_subtype_le _
  -- `N_G(V) = Ĥ`
  have hNV : Subgroup.normalizer (V : Set G) = B.Hhat :=
    normalizer_eq_of_coatom_aux B.Hhat_coatom hVleHhat hVne hHhat_le_NV
  -- `M ≤ N_G(P)`
  have hM_le_NP : M ≤ Subgroup.normalizer (P : Set G) := by
    rw [hPdef]
    exact le_normalizer_map_subtype_aux M (Work.GW2.pCore 2 ↥M)
  -- Sylow `2`-subgroups of `G` are dihedral of order at least `4`, so Bender's fusion lemma
  -- (`T.fus`) is available, in particular its second half on four-groups.
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hn2, ⟨e⟩⟩ :
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | ⟨m, ⟨e⟩⟩
    · exact absurd h hncS
    · obtain ⟨hEv, hNe⟩ :=
        Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e B.S.isPGroup' hncS
      refine ⟨m, ?_, ⟨e⟩⟩
      have hm0 : m ≠ 0 := hNe.out
      obtain ⟨k, hk⟩ := hEv
      omega
  have hcardG : Nat.card G ≠ 2 := by
    have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hle2 : Nat.card (B.S : Subgroup G) ≤ Nat.card G := Subgroup.card_le_card_group _
    rw [hcardS] at hle2
    omega
  have hNoIndex2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN hIdx
    haveI : N.Normal := hN
    rcases Subgroup.Normal.eq_bot_or_eq_top N with hbot | htop
    · rw [hbot, Subgroup.index_bot] at hIdx
      exact hcardG hIdx
    · rw [htop, Subgroup.index_top] at hIdx
      omega
  have hTrans : ∀ (W : Subgroup G), Work.GW2.IsFourGroup W → ∀ x ∈ W, ∀ y ∈ W,
      x ≠ 1 → y ≠ 1 → ∃ g ∈ Subgroup.normalizer (W : Set G), g * x * g⁻¹ = y :=
    (T.fus G B.S n hn2 ⟨e⟩ hNoIndex2).2
  -- uniqueness of the involution inside the cyclic `S₀`
  have huniqS0 : ∀ {a b : G}, a ∈ B.S0 → b ∈ B.S0 → orderOf a = 2 → orderOf b = 2 →
      a = b := by
    intro a b ha hb ha2 hb2
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    refine congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic_aux
      (H := ↥B.S0) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) ?_ ?_)
    · rw [Subgroup.orderOf_mk]; exact ha2
    · rw [Subgroup.orderOf_mk]; exact hb2
  -- an involution of `P`
  have hinvP : ∃ z ∈ P, orderOf z = 2 :=
    exists_orderOf_eq_two_of_isPGroup_two_aux P
      (by rw [hPdef]; exact isPGroup_pCoreIn_two M) hPne
  -- conjugates of an involution have order `2`
  have hconj_order : ∀ (a m : G), orderOf a = 2 → orderOf (m * a * m⁻¹) = 2 := by
    intro a m ha
    have hsemi : SemiconjBy m a (m * a * m⁻¹) := by
      show m * a = (m * a * m⁻¹) * m
      group
    exact (SemiconjBy.orderOf_eq m hsemi).symm.trans ha
  -- the conjugate `m * a * m⁻¹` lies in `P`
  have hconj_mem_P : ∀ (a : G) (ha : a ∈ P) (m : G) (hm : m ∈ M), m * a * m⁻¹ ∈ P := by
    intro a ha m hm
    exact (Subgroup.mem_normalizer_iff.mp (hM_le_NP hm) a).mp ha
  -- `t ≠ 1`
  have ht_ne_one : B.t ≠ 1 := by
    intro h
    have h2 := B.t_order
    rw [h] at h2
    simp at h2
  rcases h26c with ⟨hVleS0, -⟩ | ⟨hfour, -, -⟩
  · -- ## `V ≤ S₀`, so `V` is cyclic and its unique involution is `t`
    obtain ⟨z, hzP, hz2⟩ := hinvP
    have hzV : z ∈ V := hPleV hzP
    have hzt : z = B.t := huniqS0 (hVleS0 hzV) B.t_mem hz2 B.t_order
    have htP : B.t ∈ P := hzt ▸ hzP
    refine hD.not_le ?_
    intro m hm
    -- `m` commutes with `t`
    have hcomm : B.t * m = m * B.t := by
      have hconj : m * B.t * m⁻¹ ∈ P := hconj_mem_P B.t htP m hm
      have hconjS0 : m * B.t * m⁻¹ ∈ B.S0 := hVleS0 (hPleV hconj)
      have heq : m * B.t * m⁻¹ = B.t :=
        huniqS0 hconjS0 B.t_mem (hconj_order B.t m B.t_order) B.t_order
      calc B.t * m = m * B.t * m⁻¹ * m := by rw [heq]
        _ = m * B.t := by group
    exact B.H_le_Hhat (by
      show m ∈ Subgroup.centralizer ({B.t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm)
  · -- ## `V` is a four-group
    rw [← hVdef] at hfour
    by_cases hPV : P = V
    · -- `P = V`: `M ≤ N_G(P) = N_G(V) = Ĥ`
      have hM_le_NV : M ≤ Subgroup.normalizer (V : Set G) := by
        rw [← hPV]
        exact hM_le_NP
      exact hD.not_le (hM_le_NV.trans (le_of_eq hNV))
    · -- `|P| = 2`, so `P = ⟨z⟩` with `z` an involution of `V`
      obtain ⟨z, hzP, hz2⟩ := hinvP
      have hzV : z ∈ V := hPleV hzP
      have hcardP : Nat.card ↥P = 2 := by
        have hVc : Nat.card ↥V = 4 := hfour.1
        have hdvd : Nat.card ↥P ∣ Nat.card ↥V := Subgroup.card_dvd_of_le hPleV
        have hdvd2 : Nat.card ↥P ∣ 2 ^ 2 := by simpa [hVc] using hdvd
        have hne1 : Nat.card ↥P ≠ 1 := fun h => hPne (Subgroup.card_eq_one.mp h)
        have hne4 : Nat.card ↥P ≠ 4 := fun h =>
          hPV (Subgroup.eq_of_le_of_card_ge hPleV (le_of_eq (by rw [hVc, h])))
        rcases (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp hdvd2 with
          ⟨k, hk, hkx⟩
        have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hk3 with rfl | rfl | rfl
        · rw [pow_zero] at hkx
          exact absurd hkx hne1
        · simpa using hkx
        · norm_num at hkx
          exact absurd hkx hne4
      have hz1 : z ≠ 1 := by intro h; rw [h] at hz2; simp at hz2
      -- `M ≤ C_G(z)`
      have hMcent : M ≤ Subgroup.centralizer ({z} : Set G) := by
        haveI hPcyc : IsCyclic ↥P := isCyclic_of_prime_card (p := 2) hcardP
        intro m hm
        have hconj : m * z * m⁻¹ ∈ P := hconj_mem_P z hzP m hm
        have heq : (⟨m * z * m⁻¹, hconj⟩ : ↥P) = ⟨z, hzP⟩ :=
          eq_of_orderOf_eq_two_of_isCyclic_aux (H := ↥P)
            (by rw [Subgroup.orderOf_mk]; exact hconj_order z m hz2)
            (by rw [Subgroup.orderOf_mk]; exact hz2)
        have hval : m * z * m⁻¹ = z := congrArg Subtype.val heq
        have hzm : z * m = m * z := by
          calc z * m = (m * z * m⁻¹) * m := by rw [hval]
            _ = m * z := by group
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hzm
      -- `C_G(z) ≤ Ĥ`, by transporting `H ≤ Ĥ` along the fusion element
      have hcent_le : Subgroup.centralizer ({z} : Set G) ≤ B.Hhat := by
        obtain ⟨h, hhN, hhz⟩ := hTrans V hfour B.t htV z hzV ht_ne_one hz1
        have hhH : h ∈ B.Hhat := by rw [← hNV]; exact hhN
        intro m hm
        have hmz : z * m = m * z := Subgroup.mem_centralizer_iff.mp hm z (Set.mem_singleton z)
        have htm : B.t = h⁻¹ * z * h := by rw [← hhz]; group
        have hcomm : B.t * (h⁻¹ * m * h) = (h⁻¹ * m * h) * B.t := by
          calc B.t * (h⁻¹ * m * h) = h⁻¹ * z * h * (h⁻¹ * m * h) := by rw [htm]
            _ = h⁻¹ * (z * m) * h := by group
            _ = h⁻¹ * (m * z) * h := by rw [hmz]
            _ = (h⁻¹ * m * h) * (h⁻¹ * z * h) := by group
            _ = (h⁻¹ * m * h) * B.t := by rw [htm]
        have hm'H : h⁻¹ * m * h ∈ B.H := by
          show h⁻¹ * m * h ∈ Subgroup.centralizer ({B.t} : Set G)
          exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
        have hm_eq : m = h * (h⁻¹ * m * h) * h⁻¹ := by group
        rw [hm_eq]
        exact B.Hhat.mul_mem (B.Hhat.mul_mem hhH (B.H_le_Hhat hm'H))
          (B.Hhat.inv_mem hhH)
      exact hD.not_le (hMcent.trans hcent_le)

end Work.CORE2B
