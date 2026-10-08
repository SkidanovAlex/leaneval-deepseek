import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.sylow_two_not_isCyclic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE2A.d16_case_a_false
import Submission.Work.CORE2A.d16_case_d_false
import Submission.Work.CORE2A.relIndex_S_V_eq_two
import Submission.Work.CORE2A.relIndex_sup_U_eq_six_and_commutator
import Submission.Work.CORE2A.thm26a_CS_eq_O2

/-!
# CORE2A: the dichotomy of Bender's Theorem 2.6 (first paragraph)

`Work.CORE2A.thm26a_dichotomy` is the last conjunct of Bender's Theorem 2.6 (first paragraph):
if `O₂(Ĥ) ≠ 1` then either `O₂(Ĥ) ≤ S₀` and `Ĥ = H = C(t)`, or `O₂(Ĥ)` is a four-group,
`(O₂(Ĥ) ⊔ O(H))` has index `6` in `Ĥ`, and `Ĥ/(O₂(Ĥ)·O(H))` is not abelian.

The proof is the paper's opening paragraph decomposed into its cases:

* `O₂(Ĥ) ≤ S₀` ⟹ `Ĥ = H` (`Work.CORE2A.Hhat_eq_H_of_pCoreIn_le_S0`): the first case;
* otherwise Bender `1.6` (`Work.GW2.D16Prop`, the toolkit input `T.d16`), applied to the proper
  subgroup `Ĥ` (a `D`-group by `BenderCtx.ih` and Sylow-`2` heredity), gives four cases; case
  (a) is impossible (`Work.CORE2A.d16_case_a_false`), case (b) forces `Ĥ = H`
  (`Work.CORE2A.Hhat_eq_H_of_central_involution`), which contradicts
  `Work.CORE2A.pCoreIn_le_S0_of_Hhat_eq_H`, case (d) is impossible
  (`Work.CORE2A.d16_case_d_false`), and in case (c) `O₂(Ĥ)` is a four-group and the quotient is
  `C₃` or `D₃`, which is exactly the second case of the dichotomy
  (`Work.CORE2A.relIndex_sup_U_eq_six_and_commutator`).
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

section Helpers

/-- `Ĥ` is a proper subgroup of `G`, hence smaller. -/
theorem card_lt_card_Hhat (B : Work.GW2.BenderSetup G) : Nat.card ↥B.Hhat < Nat.card G := by
  have hne : B.Hhat ≠ ⊤ := B.Hhat_coatom.ne_top
  have hidx : 1 < B.Hhat.index := Subgroup.one_lt_index_of_ne_top hne
  have hpos : 0 < Nat.card ↥B.Hhat := Nat.card_pos
  have h1 : Nat.card ↥B.Hhat < B.Hhat.index * Nat.card ↥B.Hhat := by
    calc Nat.card ↥B.Hhat = 1 * Nat.card ↥B.Hhat := (one_mul _).symm
      _ < B.Hhat.index * Nat.card ↥B.Hhat := Nat.mul_lt_mul_of_pos_right hidx hpos
  rwa [Subgroup.index_mul_card] at h1

/-- `|S| = 2|S₀| ≥ 4`. -/
theorem card_S_ge_four_d (B : Work.GW2.BenderSetup G) : 4 ≤ Nat.card ↥(B.S : Subgroup G) := by
  have hS0 : 1 < Nat.card ↥B.S0 := by
    rw [Nat.one_lt_iff_ne_zero_and_ne_one]
    refine ⟨Nat.card_pos.ne', ?_⟩
    intro h1
    have hbot : B.S0 = ⊥ := Subgroup.card_eq_one.mp h1
    have ht : B.t = 1 := by
      have hmem : B.t ∈ (⊥ : Subgroup G) := hbot ▸ B.t_mem
      simpa using hmem
    exact bSetup_t_ne_one B ht
  calc 4 = 2 * 2 := by norm_num
    _ ≤ 2 * Nat.card ↥B.S0 := by omega
    _ = Nat.card ↥(B.S : Subgroup G) := (bSetup_card_S_eq B).symm

/-- `G` has no normal subgroup of index `2` (`G` is simple and non-abelian). -/
theorem no_normal_index_two (hctx : Work.GW2.BenderCtx G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN h2
  haveI : N.Normal := hN
  haveI : IsSimpleGroup G := hctx.simple
  have hNt : N ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at h2
    exact absurd h2 (by norm_num)
  have hNb : N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exact absurd h hNt
  -- `G/⊥ ≅ G` is a group of order `2`, hence commutative.
  have hcard : Nat.card G = 2 := by
    have h := Subgroup.index_mul_card N
    rw [h2, hNb, Subgroup.card_bot] at h
    exact h.symm
  obtain ⟨a, b, hab⟩ := hctx.nonab
  have hsq : ∀ x : G, x * x = 1 := by
    intro x
    rcases eq_or_ne x 1 with h | h
    · simp [h]
    · have hdvd : orderOf x ∣ 2 := hcard ▸ orderOf_dvd_natCard x
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) h
      · have h2x : orderOf x = 2 := h1
        have := pow_orderOf_eq_one x
        rw [h2x, pow_two] at this
        exact this
  have hcomm : ∀ x y : G, x * y = y * x := by
    intro x y
    have h1 : x * y = (x * y)⁻¹ := ((inv_eq_iff_mul_eq_one (a := x * y) (b := x * y)).mpr (hsq (x * y))).symm
    have hx : x⁻¹ = x := (inv_eq_iff_mul_eq_one (a := x) (b := x)).mpr (hsq x)
    have hy : y⁻¹ = y := (inv_eq_iff_mul_eq_one (a := y) (b := y)).mpr (hsq y)
    calc x * y = (x * y)⁻¹ := h1
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hx, hy]
  exact hab (hcomm a b)

/-- `S` is dihedral: `G` has dihedral or cyclic Sylow `2`-subgroups and `S` is not cyclic. -/
theorem dich_exists_dihedral_S (B : Work.GW2.BenderSetup G) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥(B.S : Subgroup G) ≃* DihedralGroup n) := by
  rcases hctx.sylow B.S with hcyc | ⟨n, hD⟩
  · refine absurd hcyc (sylow_two_not_isCyclic hctx.simple hctx.nonab B.S ?_)
    exact le_trans (by norm_num) (card_S_ge_four_d B)
  · refine ⟨n, ?_, hD⟩
    have hcard : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr (Classical.choice hD).toEquiv, DihedralGroup.nat_card]
    have := card_S_ge_four_d B
    omega

/-- **Centralizer of a conjugate.** -/
theorem centralizer_conj_sub (g x : G) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set G) =
      Work.GW2.conjSub g (Subgroup.centralizer ({x} : Set G)) := by
  ext y
  rw [Work.CORE2A.mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h := hy (g * x * g⁻¹) (Set.mem_singleton _)
    have h1 : (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
    have h2 : x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
    rw [h1, h2, h]
  · intro hy w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h := hy x (Set.mem_singleton x)
    have h1 : (g * x * g⁻¹) * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
    have h2 : y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    rw [h1, h2, h]

/-- `IsFourGroup` is compatible with pushing a subgroup forward along `K.subtype`. -/
theorem isFourGroup_map_subtype_iff (K : Subgroup G) (L : Subgroup ↥K) :
    Work.GW2.IsFourGroup (L.map K.subtype) ↔ Work.GW2.IsFourGroup L := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective K.subtype_injective]; exact h.1
    · intro v hv
      have hm : K.subtype v ∈ L.map K.subtype := Subgroup.mem_map_of_mem K.subtype hv
      have := h.2 (K.subtype v) hm
      exact Subtype.ext (by simpa using this)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.card_map_of_injective K.subtype_injective]; exact h1
    · rintro _ ⟨v, hv, rfl⟩
      simpa using congrArg Subtype.val (h2 v hv)

/-- The relative index of the image of a subgroup of `Ĥ` is its index in `Ĥ`. -/
theorem relIndex_map_subtype_eq_index (B : Work.GW2.BenderSetup G)
    (K : Subgroup ↥B.Hhat) : (K.map B.Hhat.subtype).relIndex B.Hhat = K.index := by
  have h1 : (K.map B.Hhat.subtype).relIndex B.Hhat *
      Nat.card ↥(K.map B.Hhat.subtype ⊓ B.Hhat) = Nat.card ↥B.Hhat :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr (Subgroup.map_subtype_le K),
    Subgroup.card_map_of_injective B.Hhat.subtype_injective] at h1
  have h2 := Subgroup.index_mul_card K
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥K)) (h1.trans h2.symm)

end Helpers

section Assembly

variable (T : Work.GW2.LocalToolkit)

/-- `Ĥ` is a `D`-group. -/
theorem isDGroup_Hhat (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) :
    Work.GW2.IsDGroup ↥B.Hhat :=
  hctx.ih ↥B.Hhat (card_lt_card_Hhat B) (dihOrCycSylow_subgroup hctx.sylow B.Hhat)

/-- A central involution of `Ĥ` forces `Ĥ = H = C(t)`: Bender `1.6(b)` is compatible only with
the first case of the dichotomy. -/
theorem Hhat_eq_H_of_central_involution (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) {z : ↥B.Hhat}
    (hz : z ∈ Subgroup.center ↥B.Hhat) (hz2 : orderOf z = 2) : B.Hhat = B.H := by
  haveI : IsSimpleGroup G := hctx.simple
  set zG : G := ((z : ↥B.Hhat) : G) with hzG
  have hz2G : orderOf zG = 2 := by
    rw [hzG, Subgroup.orderOf_coe]; exact hz2
  have hcent : B.Hhat ≤ Subgroup.centralizer ({zG} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨h, hh⟩)).symm
  have hC : Subgroup.centralizer ({zG} : Set G) = B.Hhat := by
    refine le_antisymm ?_ hcent
    by_contra hle
    have hlt : B.Hhat < Subgroup.centralizer ({zG} : Set G) :=
      lt_of_le_of_ne hcent (fun h => hle (le_of_eq h.symm))
    have htop : Subgroup.centralizer ({zG} : Set G) = ⊤ := (B.Hhat_coatom.lt_iff).mp hlt
    have hzg : zG ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg' : g ∈ Subgroup.centralizer ({zG} : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg' zG (Set.mem_singleton zG)).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · have h1 : zG = 1 := by
        have : zG ∈ (⊥ : Subgroup G) := h ▸ hzg
        simpa using this
      rw [h1, orderOf_one] at hz2G
      exact absurd hz2G (by norm_num)
    · obtain ⟨a, b, hab⟩ := hctx.nonab
      haveI : IsMulCommutative G := by
        rw [isMulCommutative_iff]
        intro p q
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top p) q).symm
      exact hab (mul_comm a b)
  have hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := no_normal_index_two hctx
  obtain ⟨n, hn2, ⟨e⟩⟩ := dich_exists_dihedral_S B hFT hctx
  obtain ⟨c, hc⟩ : ∃ c : G, c * zG * c⁻¹ = B.t :=
    isConj_iff.mp ((T.fus G B.S n hn2 ⟨e⟩ hno).1 zG B.t hz2G B.t_order)
  have hH : B.H = Work.GW2.conjSub c B.Hhat := by
    rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, ← hc,
      centralizer_conj_sub c zG, hC]
  have hcard : Nat.card ↥B.H = Nat.card ↥B.Hhat := by
    have h := Work.CORE2A.card_conjSub c B.Hhat
    rwa [← hH] at h
  exact (Subgroup.eq_of_le_of_card_ge B.H_le_Hhat (le_of_eq hcard.symm)).symm


/-- **Bender 1981, Theorem 2.6, first paragraph: the dichotomy.** -/
theorem thm26a_dichotomy (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h22 : Work.GW2.Lemma22Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥ →
        ((Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0 ∧ B.Hhat = B.H) ∨
          (Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) ∧
            (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 ∧
            ∃ a ∈ B.Hhat, ∃ b ∈ B.Hhat,
              a * b * a⁻¹ * b⁻¹ ∉ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)) := by
  intro G _ _ hFT hctx B hV
  -- Case 1: `O₂(Ĥ) ≤ S₀`, and then `Ĥ = H`.
  by_cases hle : Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0
  · exact Or.inl ⟨hle, Hhat_eq_H_of_pCoreIn_le_S0 B hV hle⟩
  -- Case 2: `O₂(Ĥ) ⊄ S₀`.  Bender 1.6 (`T.d16`) applied to the `D`-group `Ĥ`.
  · refine Or.inr ?_
    have hd16 := T.d16 ↥B.Hhat hFT (dihOrCycSylow_subgroup hctx.sylow B.Hhat)
      (isDGroup_Hhat hctx B)
    rcases hd16 with hA | hB | hC | hD
    · -- 1.6(a) is impossible when `O₂(Ĥ) ≠ 1`.
      exact absurd hA (d16_case_a_false T G hFT hctx B hV)
    · -- 1.6(b): a central involution forces `Ĥ = H`; together with `O₂(Ĥ) ≠ 1` and Bender's
      -- Lemma 2.2 (`h22`, i.e. `U = O(C(t)) ≠ 1`) this contradicts `O₂(Ĥ) ≰ S₀`: an involution
      -- `x ∈ O₂(Ĥ) − S₀` lies in `C_S(U)`, hence is conjugate to `t` in `N_G(U) = Ĥ = C(t)`
      -- (`fusion`), so `x = t` as `t` is central in `C(t)`.
      obtain ⟨z, hz, hz2⟩ := hB
      have hEq : B.Hhat = B.H := Hhat_eq_H_of_central_involution T hFT hctx B hz hz2
      obtain ⟨n, hn2, hD⟩ := dich_exists_dihedral_S (B := B) hFT hctx
      obtain ⟨x, hxV, hx0⟩ : ∃ x ∈ Work.GW2.pCoreIn 2 B.Hhat, x ∉ B.S0 := by
        by_contra hcon
        exact hle fun x hx => by
          by_contra hx0
          exact hcon ⟨x, hx, hx0⟩
      have hxQ : x ∈ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) :=
        V_le_Q (B := B) hxV
      have hx2 : orderOf x = 2 :=
        dihedral_index_two n hn2 _ _ hD B.S0_le B.S0_cyclic B.S0_index x hxQ.1 hx0
      obtain ⟨h, hh, hhx⟩ := fusion (B := B) T h21 h22 hFT hctx hV x hxQ hx2
      have htcent : h * B.t * h⁻¹ = B.t := by
        have h1 : B.t * h = h * B.t :=
          Subgroup.mem_centralizer_iff.mp (hEq ▸ hh) B.t (by simp)
        calc h * B.t * h⁻¹ = (B.t * h) * h⁻¹ := by rw [← h1]
          _ = B.t := by group
      have hxt : x = B.t := by
        calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
          _ = h⁻¹ * B.t * h := by rw [hhx]
          _ = h⁻¹ * (h * B.t * h⁻¹) * h := by rw [htcent]
          _ = B.t := by group
      exact absurd (by rw [hxt]; exact B.t_mem) hx0
    · -- 1.6(c): `O₂(Ĥ)` is a four-group and `Ĥ/O₂(Ĥ)O(Ĥ)` is `C₃` or `D₃`.
      obtain ⟨h4, hquot⟩ := hC
      have h4' : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) :=
        (isFourGroup_map_subtype_iff B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)).mpr h4
      have hq : ((Work.GW2.pCoreIn 2 B.Hhat ⊔ Work.GW2.oddCoreIn B.Hhat).relIndex B.Hhat = 3 ∨
          (Work.GW2.pCoreIn 2 B.Hhat ⊔ Work.GW2.oddCoreIn B.Hhat).relIndex B.Hhat = 6) := by
        have hmap : ((Work.GW2.pCore 2 ↥B.Hhat ⊔ Work.GW2.oddCore ↥B.Hhat).map
              B.Hhat.subtype).relIndex B.Hhat
            = (Work.GW2.pCore 2 ↥B.Hhat ⊔ Work.GW2.oddCore ↥B.Hhat).index :=
          relIndex_map_subtype_eq_index B _
        have hsup : (Work.GW2.pCoreIn 2 B.Hhat ⊔ Work.GW2.oddCoreIn B.Hhat)
            = (Work.GW2.pCore 2 ↥B.Hhat ⊔ Work.GW2.oddCore ↥B.Hhat).map B.Hhat.subtype := by
          rw [Work.GW2.pCoreIn, Work.GW2.oddCoreIn, Subgroup.map_sup]
        have hidx : (Work.GW2.pCore 2 ↥B.Hhat ⊔ Work.GW2.oddCore ↥B.Hhat).index
            = Nat.card (↥B.Hhat ⧸ (Work.GW2.pCore 2 ↥B.Hhat ⊔ Work.GW2.oddCore ↥B.Hhat)) := rfl
        rcases hquot with ⟨_, h3⟩ | ⟨e3⟩
        · exact Or.inl (by rw [hsup, hmap, hidx, h3])
        · refine Or.inr ?_
          rw [hsup, hmap, hidx]
          rw [Nat.card_congr (Classical.choice e3).toEquiv, DihedralGroup.nat_card]
      obtain ⟨hidx, hcom⟩ :=
        relIndex_sup_U_eq_six_and_commutator T h21 G hFT hctx B h4' hle hq
      exact ⟨h4', hidx, hcom⟩
    · -- 1.6(d) is impossible.
      exact absurd hD (d16_case_d_false T h21 G hFT hctx B hle)

end Assembly

end Work.CORE2A
