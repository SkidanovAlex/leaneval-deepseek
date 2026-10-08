import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE2A.thm26a_U_eq_Ohat
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.le_oddCoreIn_of_normal_of_odd
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.CORE2A.exists_mul_of_mem_involutionSet_H
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.sylow_two_not_isCyclic
import Submission.Work.CORE2A.CS_eq_O2_plan
import Submission.Work.CORE2A.bswHyps2_of_config
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Basic

/-!
# CORE2A: Bender 1981, Theorem 2.6, middle conjunct `C_S(U) = O₂(Ĥ)`

The proof follows Bender 1981, p. 220 (see `Submission/Work/CORE2A/CS_eq_O2_plan.lean`):

* `V = O₂(Ĥ) ≤ S ⊓ C_G(U)` — `pCoreIn_le_S` and `V_le_centralizer_U`;
* `S ⊓ C_G(U) ≠ S` (Bender's Lemma 2.2 configuration, `CS_ne_S`);
* `N_G(U) = Ĥ` (`normalizer_U_eq_Hhat`, from `U = O(Ĥ)` = `thm26a_U_eq_Ohat`);
* all involutions of `S ⊓ C_G(U)` are `Ĥ`-conjugate to `t` (`fusion`): Bender's assertion
  "all involutions in `C_S(U)` are conjugate in `N_G(U) = Ĥ`".  Proof: `T.fus` puts an
  involution `x ∈ C_S(U)` into the `G`-class of `t`; since `H = U ⋔ S` is solvable with `U` a
  Hall `2'`-subgroup, Hall conjugacy (`OddOrder.Isaacs.Ch03.hall_C`) moves the conjugating
  element into `N_G(U) = Ĥ`.
* consequently every involution of `S ⊓ C_G(U)` lies in `V` (`inv_mem_V`);
* if `V ⊄ S₀` then `V` together with any reflection of `S` inside it has index `≤ 2` in `S`,
  so `S ⊓ C_G(U) = V` (`Q_le_V_of_not_le_S0`);
* if `V ≤ S₀` then `Ĥ = H` (`PcoreInBasic`), every element of `S ⊓ C_G(U)` lies in the cyclic
  group `S₀` and hence centralizes `O₂(H) = V`, and `H`'s Fitting subgroup self-centralizes
  (`OddOrder.GroupTheory.centralizer_fitting_le_fitting`), giving
  `S ⊓ C_G(U) ≤ O₂(H) = V` (`Q_le_V_of_le_S0`).
-/

open scoped MatrixGroups
open scoped Pointwise

namespace Work.CORE2A

open Subgroup

variable {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)

section Setup

/-- `V = O₂(Ĥ) ≤ H`, hence a normal `2`-subgroup of `H`. -/
theorem pCoreIn_subgroupOf_H_normal :
    ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (pCoreIn_le_S B |>.trans (bSetup_S_le_H B))]
  intro a b ha hb
  exact conj_mem_pCoreIn B (B.H_le_Hhat hb) ha

/-- `U = O(Ĥ)`, hence `U ⊴ Ĥ`. -/
theorem U_subgroupOf_Hhat_normal (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (h22 : Work.GW2.Lemma22Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥) :
    (B.U.subgroupOf B.Hhat).Normal := by
  rw [← thm26a_U_eq_Ohat T h21 h22 G hFT hctx B hV]
  exact oddCoreIn_normal_inSelf B.Hhat

/-- **Bender p. 220**: `N_G(U) = Ĥ`. -/
theorem normalizer_U_eq_Hhat (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (h22 : Work.GW2.Lemma22Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥) :
    Subgroup.normalizer (B.U : Set G) = B.Hhat := by
  haveI : IsSimpleGroup G := hctx.simple
  refine normalizer_eq_of_coatom B.Hhat_coatom (bSetup_U_le_Hhat B)
    (lemma22Prop_U_ne_bot h22 hFT hctx B) ?_
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (bSetup_U_le_Hhat B)).mp
    (U_subgroupOf_Hhat_normal B T h21 h22 hFT hctx hV)

end Setup

theorem card_S0_ge_two : 2 ≤ Nat.card B.S0 := by
  have hle : Subgroup.zpowers B.t ≤ B.S0 := Subgroup.zpowers_le.mpr B.t_mem
  have hcard : Nat.card ↥(Subgroup.zpowers B.t) ≤ Nat.card ↥B.S0 :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have h2 : Nat.card ↥(Subgroup.zpowers B.t) = 2 := by rw [Nat.card_zpowers, B.t_order]
  omega

theorem card_S_ge_four : 4 ≤ Nat.card (B.S : Subgroup G) := by
  have h := bSetup_card_S_eq B
  have h0 := card_S0_ge_two (B := B)
  omega

theorem exists_dihedral_S (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have h2 : 2 ≤ Nat.card (B.S : Subgroup G) := by have := card_S_ge_four (B := B); omega
  have h4 : 4 ≤ Nat.card (B.S : Subgroup G) := card_S_ge_four (B := B)
  rcases hctx.sylow B.S with hcyc | ⟨n, hn⟩
  · exact absurd hcyc (sylow_two_not_isCyclic hctx.simple hctx.nonab B.S h2)
  · obtain ⟨e⟩ := hn
    have hcard : Nat.card (B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    exact ⟨n, by omega, ⟨e⟩⟩

theorem no_index_two (hctx : Work.GW2.BenderCtx G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  haveI : IsSimpleGroup G := hctx.simple
  intro N hN h2
  haveI : N.Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [hbot, Subgroup.index_bot] at h2
    obtain ⟨a, b, hab⟩ := hctx.nonab
    refine hab ?_
    have hall : ∀ x : G, x * x = 1 := fun x => by
      have h : orderOf x ∣ 2 := h2 ▸ orderOf_dvd_natCard x
      have h1 := orderOf_dvd_iff_pow_eq_one.mp h
      simpa [pow_two] using h1
    have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_iff_mul_eq_one.mpr (hall x)
    calc a * b = (a * b)⁻¹⁻¹ := by simp
      _ = (b⁻¹ * a⁻¹)⁻¹ := by rw [mul_inv_rev]
      _ = (b * a)⁻¹ := by rw [hinv a, hinv b]
      _ = b * a := hinv (b * a)
  · rw [htop, Subgroup.index_top] at h2
    exact absurd h2 (by norm_num)

section Fusion

/-- `|H| = |U| · |S|` (from `H = U ⋔ S`). -/
theorem card_H_eq (hsplit : B.U ⊔ (B.S : Subgroup G) = B.H) :
    Nat.card ↥B.H = Nat.card ↥B.U * Nat.card ↥(B.S : Subgroup G) := by
  have hset : ((B.U : Set G) * ((B.S : Subgroup G) : Set G)) = (B.H : Set G) := by
    ext y
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact B.H.mul_mem (bSetup_U_le_H B ha) (bSetup_S_le_H B hb)
    · intro hy
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_decomposition (bSetup_U_le_H B) (bSetup_S_le_H B)
        (subgroupOf_oddCoreIn_normal B.H) hsplit y hy
      exact ⟨a, ha, b, hb, hab⟩
  have hHK := Subgroup.card_HK_mul_card_inf_eq_card_mul_card B.U (B.S : Subgroup G)
  rw [inf_U_S_eq_bot B, Subgroup.card_bot, mul_one] at hHK
  have h1 : Nat.card ↥B.H = (B.H : Set G).ncard := Nat.card_coe_set_eq _
  have h2 : ((B.U : Set G) * ((B.S : Subgroup G) : Set G)).ncard
      = Nat.card ↥((B.U : Set G) * ((B.S : Subgroup G) : Set G)) := (Nat.card_coe_set_eq _).symm
  rw [h1, ← hset, h2]
  exact hHK

/-- `U` is a Hall `2'`-subgroup of `H`. -/
theorem U_isHall_in_H (hsplit : B.U ⊔ (B.S : Subgroup G) = B.H) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup {p : ℕ | p ≠ 2} (B.U.subgroupOf B.H) := by
  have hcardU : Nat.card ↥(B.U.subgroupOf B.H) = Nat.card ↥B.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (bSetup_U_le_H B)).toEquiv
  have hindex : (B.U.subgroupOf B.H).index = Nat.card ↥(B.S : Subgroup G) := by
    have h := Subgroup.card_mul_index (H := B.U.subgroupOf B.H)
    rw [hcardU, card_H_eq B hsplit] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  constructor
  · intro p hp hp2
    obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    rw [hcardU] at hpdvd
    subst hp2
    exact (Nat.not_even_iff_odd.mpr (bSetup_U_odd B)) (even_iff_two_dvd.mpr hpdvd)
  · intro p hp
    obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    rw [hindex] at hpdvd
    obtain ⟨k, hk⟩ := (B.S).isPGroup'.exists_card_eq
    rw [hk] at hpdvd
    obtain ⟨c, hc⟩ := hpp.dvd_of_dvd_pow hpdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp ⟨c, hc⟩ with h | h
    · exact absurd h hpp.ne_one
    · simpa only [Set.mem_setOf_eq, not_not] using h

/-- `↥H` is solvable: `H = U ⋔ S` with `U` odd (hence solvable by Feit–Thompson) and `S` a
`2`-group. -/
theorem H_solvable (hFT : Work.GW2.FeitThompsonProp) (hsplit : B.U ⊔ (B.S : Subgroup G) = B.H) :
    Group.IsSolvable ↥B.H := by
  haveI hN : (B.U.subgroupOf B.H).Normal := subgroupOf_oddCoreIn_normal B.H
  haveI : Group.IsSolvable ↥(B.U.subgroupOf B.H) := by
    haveI : Group.IsSolvable ↥B.U := hFT ↥B.U (bSetup_U_odd B)
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (bSetup_U_le_H B)).symm.toMonoidHom)
      ((Subgroup.subgroupOfEquivOfLe (bSetup_U_le_H B)).symm.surjective)
  haveI : Group.IsSolvable (↥B.H ⧸ (B.U.subgroupOf B.H)) := by
    haveI : Group.IsSolvable ↥(B.S : Subgroup G) := by
      haveI : Group.IsNilpotent ↥(B.S : Subgroup G) := (B.S).isPGroup'.isNilpotent
      infer_instance
    set φ : ↥(B.S : Subgroup G) →* (↥B.H ⧸ (B.U.subgroupOf B.H)) :=
      (QuotientGroup.mk' (B.U.subgroupOf B.H)).comp (Subgroup.inclusion (bSetup_S_le_H B)) with hφ
    have hsurj : Function.Surjective φ := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (B.U.subgroupOf B.H) q
      obtain ⟨u, hu, s, hs, hus⟩ := mem_sup_decomposition (bSetup_U_le_H B) (bSetup_S_le_H B)
        hN hsplit y y.2
      refine ⟨⟨s, hs⟩, ?_⟩
      have hy : y = ⟨u, bSetup_U_le_H B hu⟩ * ⟨s, bSetup_S_le_H B hs⟩ :=
        Subtype.ext (by simpa using hus.symm)
      have h1 : (QuotientGroup.mk' (B.U.subgroupOf B.H)) ⟨u, bSetup_U_le_H B hu⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hu
      rw [hy, map_mul, h1, one_mul]
      rfl
    exact Group.isSolvable_of_surjective (f := φ) hsurj
  exact Group.isSolvable_of_subgroup_quotient (B.U.subgroupOf B.H)
/-- **Bender 1981, p. 220**: all involutions of `C_S(U) = S ⊓ C_G(U)` are conjugate to `t` in
`N_G(U) = Ĥ`. -/
theorem fusion (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (h22 : Work.GW2.Lemma22Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥) :
    ∀ x ∈ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G), orderOf x = 2 →
      ∃ h ∈ B.Hhat, h * x * h⁻¹ = B.t := by
  intro x hx hx2
  by_cases hxt : x = B.t
  · exact ⟨1, B.Hhat.one_mem, by rw [hxt]; group⟩
  obtain ⟨n, hn2, ⟨e⟩⟩ := exists_dihedral_S (B := B) T hFT hctx
  -- `H = U ⋔ S`
  have hsplit : B.U ⊔ (B.S : Subgroup G) = B.H := by
    have hcentral : ∀ y ∈ (B.S : Subgroup G), y * B.t = B.t * y := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hy) B.t (by simp)).symm
    have h := T.split G B.S n hn2 ⟨e⟩ B.t (bSetup_t_mem_S B) B.t_order hcentral
    rw [show Subgroup.centralizer ({B.t} : Set G) = B.H from rfl, ← bSetup_U_eq B] at h
    exact h
  haveI := H_solvable (B := B) hFT hsplit
  have hHallU := U_isHall_in_H (B := B) hsplit
  -- `x ~_G t`
  obtain ⟨g, hg⟩ := (T.fus G B.S n hn2 ⟨e⟩ (no_index_two hctx)).1 x B.t hx2 B.t_order
  have hgt : (g : G) * x * (g : G)⁻¹ = B.t := by
    rw [show (g : G) * x = B.t * (g : G) from hg]
    group
  obtain ⟨hxS, hxU⟩ := Subgroup.mem_inf.mp hx
  -- `X = gUg⁻¹ ≤ H`
  set X : Subgroup G := B.U.map (MulAut.conj (g : G)).toMonoidHom with hXdef
  have hXleH : X ≤ B.H := by
    intro y hy
    rw [hXdef] at hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hux : u * x = x * u := (Subgroup.mem_centralizer_iff.mp hxU u hu)
    calc B.t * (MulAut.conj (g : G)) u
        = ((g : G) * x * (g : G)⁻¹) * ((g : G) * u * (g : G)⁻¹) := by
          rw [hgt, MulAut.conj_apply]
      _ = (g : G) * (x * u) * (g : G)⁻¹ := by group
      _ = (g : G) * (u * x) * (g : G)⁻¹ := by rw [← hux]
      _ = (MulAut.conj (g : G)) u * B.t := by
        rw [← hgt, MulAut.conj_apply]; group
  -- `X` is Hall in `H` too
  have hcardX : Nat.card ↥X = Nat.card ↥B.U := by
    rw [hXdef]
    exact Nat.card_congr (Subgroup.equivMapOfInjective B.U (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective).toEquiv.symm
  have hHallX : OddOrder.Isaacs.Ch03.IsHallSubgroup {p : ℕ | p ≠ 2} (X.subgroupOf B.H) :=
    OddOrder.Isaacs.Ch03.isHallSubgroup_of_card_eq hHallU (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleH).toEquiv, hcardX,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (bSetup_U_le_H B)).toEquiv])
  obtain ⟨c, hc⟩ := OddOrder.Isaacs.Ch03.hall_C (π := {p : ℕ | p ≠ 2}) hHallU hHallX
  -- `hc : (U.subgroupOf H).map (conj c) = X.subgroupOf H`
  have hcF : ∀ w ∈ B.U, (c : G) * w * (c : G)⁻¹ ∈ X := by
    intro w hw
    have hwH : (c : G) * w * (c : G)⁻¹ ∈ B.H :=
      B.H.mul_mem (B.H.mul_mem c.2 (bSetup_U_le_H B hw)) (B.H.inv_mem c.2)
    have hmem : (⟨(c : G) * w * (c : G)⁻¹, hwH⟩ : ↥B.H)
        ∈ (B.U.subgroupOf B.H).map (MulAut.conj c).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨⟨w, bSetup_U_le_H B hw⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hw
      · ext
        simp [MulAut.conj_apply]
    rw [hc] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hkey : ∀ y ∈ X, (c : G)⁻¹ * y * c ∈ B.U := by
    intro y hy
    have hyH : y ∈ B.H := hXleH hy
    have hymem : (⟨y, hyH⟩ : ↥B.H) ∈ (X.subgroupOf B.H) := Subgroup.mem_subgroupOf.mpr hy
    rw [← hc] at hymem
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hymem
    have hwU : (w : G) ∈ B.U := Subgroup.mem_subgroupOf.mp hw
    have h3 : (c : G) * (w : G) * (c : G)⁻¹ = y := by
      have h2 := congrArg (fun z : ↥B.H => (z : G)) hwv
      simpa using h2
    have : (w : G) = (c : G)⁻¹ * y * c := by
      calc (w : G) = (c : G)⁻¹ * ((c : G) * (w : G) * (c : G)⁻¹) * c := by group
        _ = (c : G)⁻¹ * y * c := by rw [h3]
    rwa [← this]
  have hkey' : ∀ y ∈ B.H, (c : G)⁻¹ * y * c ∈ B.U → y ∈ X := by
    intro y hy hyU
    have h1 : (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ ∈ X := hcF _ hyU
    have h2 : (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ = y := by group
    rwa [h2] at h1
  -- `h := c⁻¹ g`
  refine ⟨(c : G)⁻¹ * (g : G), ?_, ?_⟩
  · have hle : B.U.map (MulAut.conj ((c : G)⁻¹ * (g : G))).toMonoidHom ≤ B.U := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
      have hgu : (g : G) * u * (g : G)⁻¹ ∈ X := by
        rw [hXdef]
        exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      have h1 := hkey _ hgu
      have e1 : (MulAut.conj ((c : G)⁻¹ * (g : G))) u
          = (c : G)⁻¹ * ((g : G) * u * (g : G)⁻¹) * c := by
        rw [MulAut.conj_apply]; group
      change (MulAut.conj ((c : G)⁻¹ * (g : G))) u ∈ B.U
      rw [e1]
      exact h1
    have heq : B.U.map (MulAut.conj ((c : G)⁻¹ * (g : G))).toMonoidHom = B.U := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_congr (Subgroup.equivMapOfInjective B.U
        (MulAut.conj ((c : G)⁻¹ * (g : G))).toMonoidHom
        (MulAut.conj ((c : G)⁻¹ * (g : G))).injective).toEquiv]
    rw [← normalizer_U_eq_Hhat (B := B) T h21 h22 hFT hctx hV]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := B.U)
      (g := (c : G)⁻¹ * (g : G))).mpr heq
  · have hct : (c : G) * B.t * (c : G)⁻¹ = B.t := by
      have h := Subgroup.mem_centralizer_iff.mp c.2 B.t (by simp)
      rw [← h]; group
    have hct' : (c : G)⁻¹ * B.t * c = B.t := by
      have := congrArg (fun z => (c : G)⁻¹ * z * c) hct
      simpa [mul_assoc] using this.symm
    calc (c : G)⁻¹ * (g : G) * x * ((c : G)⁻¹ * (g : G))⁻¹
        = (c : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * c := by group
      _ = (c : G)⁻¹ * B.t * c := by rw [hgt]
      _ = B.t := hct'

end Fusion

section Inverse

/-- **Dihedral inversion.**  If `S ≅ DihedralGroup n` (`n ≥ 2`) and `S₀ ≤ S` is cyclic of
index two, then every `s ∈ S − S₀` inverts `S₀`. -/
theorem inverts_of_dihedral_cyclic_index_two' (n : ℕ) (hn : 2 ≤ n) (S S0 : Subgroup G)
    (hD : Nonempty (S ≃* DihedralGroup n)) (hS0 : S0 ≤ S) (hcyc : IsCyclic S0)
    (hidx : S0.relIndex S = 2) : ∀ s ∈ S, s ∉ S0 → Work.GW2.Inverts s S0 := by
  classical
  obtain ⟨e⟩ := hD
  intro s hsS hs0
  have hcardS : Nat.card S = 2 * n := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS0 : Nat.card S0 = n := by
    have h := Subgroup.relIndex_mul_card S0 S
    rw [hidx, inf_eq_left.mpr hS0] at h
    rw [hcardS] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  set T : Subgroup (DihedralGroup n) := (S0.subgroupOf S).map e.toMonoidHom with hT
  have hcycT : IsCyclic T := by
    rw [hT]
    exact (Subgroup.equivMapOfInjective (S0.subgroupOf S) e.toMonoidHom e.injective).isCyclic.mp
      ((Subgroup.subgroupOfEquivOfLe hS0).isCyclic.mpr hcyc)
  have hidxT : T.relIndex ⊤ = 2 := by
    rw [hT]
    have hcardMap : Nat.card ((S0.subgroupOf S).map e.toMonoidHom) = n := by
      rw [← Nat.card_congr
            (Subgroup.equivMapOfInjective (S0.subgroupOf S) e.toMonoidHom e.injective).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0).toEquiv]
      exact hcardS0
    have h := Subgroup.relIndex_mul_card ((S0.subgroupOf S).map e.toMonoidHom) ⊤
    rw [inf_top_eq, Subgroup.card_top, DihedralGroup.nat_card, hcardMap] at h
    exact Nat.mul_right_cancel (by omega : 0 < n) h
  have hy : e ⟨s, hsS⟩ ∉ T := by
    rw [hT, Subgroup.mem_map]
    rintro ⟨y, hy, hye⟩
    rw [Subgroup.mem_subgroupOf] at hy
    rw [e.injective hye] at hy
    exact hs0 hy
  intro x hx
  have hxS : x ∈ S := hS0 hx
  have hzT : e ⟨x, hxS⟩ ∈ T := by
    rw [hT, Subgroup.mem_map]
    exact ⟨⟨x, hxS⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩
  have key := bsw_dihedral_cyclic_index_two_inverts n hn T hcycT hidxT (e ⟨s, hsS⟩) hy
    (e ⟨x, hxS⟩) hzT
  have hmem : s * x * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hsS hxS) (S.inv_mem hsS)
  have hxinv : x⁻¹ ∈ S := S.inv_mem hxS
  have heq : (⟨s * x * s⁻¹, hmem⟩ : ↥S) = ⟨s, hsS⟩ * ⟨x, hxS⟩ * (⟨s, hsS⟩ : ↥S)⁻¹ := by
    ext; simp [mul_assoc]
  have hgoal : (⟨s * x * s⁻¹, hmem⟩ : ↥S) = ⟨x⁻¹, hxinv⟩ := by
    apply e.injective
    have hxinv' : (⟨x⁻¹, hxinv⟩ : ↥S) = (⟨x, hxS⟩ : ↥S)⁻¹ := by ext; simp
    rw [hxinv', map_inv, heq, map_mul, map_mul, map_inv]
    exact key
  exact congrArg Subtype.val hgoal

end Inverse



section Cases

/-- `V = O₂(Ĥ) ≤ S ⊓ C_G(U)`. -/
theorem V_le_Q :
    Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) :=
  le_inf (pCoreIn_le_S B) (V_le_centralizer_U B)

/-- Every involution of `S ⊓ C_G(U)` lies in `O₂(Ĥ)`. -/
theorem inv_mem_V (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (h22 : Work.GW2.Lemma22Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥) :
    ∀ x ∈ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G), orderOf x = 2 →
      x ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  intro x hx hx2
  -- an involution of `V`
  have h2dvd : 2 ∣ Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) := by
    rcases (pCoreIn_isPGroup B).card_eq_or_dvd (p := 2) with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) hV
    · exact h2
  obtain ⟨z, hz2⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Work.GW2.pCoreIn 2 B.Hhat)) 2 h2dvd
  have hzV : ((z : ↥(Work.GW2.pCoreIn 2 B.Hhat)) : G) ∈ Work.GW2.pCoreIn 2 B.Hhat := z.2
  have hzord : orderOf (((z : ↥(Work.GW2.pCoreIn 2 B.Hhat)) : G)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hz2
  have hzQ : ((z : ↥(Work.GW2.pCoreIn 2 B.Hhat)) : G)
      ∈ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) :=
    V_le_Q (B := B) hzV
  -- `t ∈ V`
  obtain ⟨h, hh, hh2⟩ := fusion (B := B) T h21 h22 hFT hctx hV _ hzQ hzord
  have htV : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    have := conj_mem_pCoreIn B hh hzV
    rwa [hh2] at this
  -- `x ∈ V`
  obtain ⟨h', hh', hh'2⟩ := fusion (B := B) T h21 h22 hFT hctx hV x hx hx2
  have hxeq : x = (h')⁻¹ * B.t * ((h')⁻¹)⁻¹ := by
    rw [← hh'2]; group
  rw [hxeq]
  exact conj_mem_pCoreIn B (B.Hhat.inv_mem hh') htV

/-- If `V ⊄ S₀`, then `S ⊓ C_G(U) = V`. -/
theorem Q_le_V_of_not_le_S0 (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (h22 : Work.GW2.Lemma22Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥)
    (hnot : ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0) :
    (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) ≤ Work.GW2.pCoreIn 2 B.Hhat := by
  obtain ⟨n, hn2, hD⟩ := exists_dihedral_S (B := B) T hFT hctx
  have hinv : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → Work.GW2.Inverts s B.S0 :=
    fun s hs h0 => inverts_of_dihedral_cyclic_index_two' n hn2 _ _ hD
      B.S0_le B.S0_cyclic B.S0_index s hs h0
  -- a reflection in `V`
  obtain ⟨v, hvV, hv0⟩ : ∃ v ∈ Work.GW2.pCoreIn 2 B.Hhat, v ∉ B.S0 := by
    by_contra hcon
    exact hnot fun x hx => by
      by_contra hx0
      exact hcon ⟨x, hx, hx0⟩
  have hvS : v ∈ (B.S : Subgroup G) := pCoreIn_le_S B hvV
  have hvC : v ∈ Subgroup.centralizer (B.U : Set G) := V_le_centralizer_U B hvV
  have hvQ : v ∈ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) := ⟨hvS, hvC⟩
  have hvv : v * v = 1 := by
    have h2 : orderOf v = 2 :=
      dihedral_index_two n hn2 _ _ hD B.S0_le B.S0_cyclic B.S0_index v hvS hv0
    have h1 : v ^ orderOf v = 1 := pow_orderOf_eq_one v
    rw [h2] at h1
    simpa [pow_two] using h1
  intro x hx
  obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
  by_cases hx0 : x ∈ B.S0
  · -- `v * x` is a reflection, hence an involution of `Q`, hence lies in `V`
    have hvxS : v * x ∈ (B.S : Subgroup G) := (B.S).mul_mem hvS hxS
    have hvx0 : v * x ∉ B.S0 := by
      intro hmem
      exact hv0 (by
        have : v = (v * x) * x⁻¹ := by group
        rw [this]
        exact B.S0.mul_mem hmem (B.S0.inv_mem hx0))
    have hvx2 : orderOf (v * x) = 2 :=
      dihedral_index_two n hn2 _ _ hD B.S0_le B.S0_cyclic B.S0_index (v * x) hvxS hvx0
    have hvxQ : v * x ∈ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) :=
      ⟨hvxS, Subgroup.mul_mem _ hvC hxC⟩
    have hvxV : v * x ∈ Work.GW2.pCoreIn 2 B.Hhat :=
      inv_mem_V (B := B) T h21 h22 hFT hctx hV (v * x) hvxQ hvx2
    have hxeq : x = v * (v * x) := by
      rw [← mul_assoc, hvv, one_mul]
    rw [hxeq]
    exact (Work.GW2.pCoreIn 2 B.Hhat).mul_mem hvV hvxV
  · -- `x` is itself a reflection, hence an involution of `Q`
    have hx2 : orderOf x = 2 :=
      dihedral_index_two n hn2 _ _ hD B.S0_le B.S0_cyclic B.S0_index x hxS hx0
    exact inv_mem_V (B := B) T h21 h22 hFT hctx hV x hx hx2


/-- Elements of a cyclic subgroup commute. -/
theorem comm_of_mem_zpowers {G : Type*} [Group G] {g a b : G}
    (ha : a ∈ Subgroup.zpowers g) (hb : b ∈ Subgroup.zpowers g) : a * b = b * a := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, add_comm, zpow_add]

/-- If `V ≤ S₀`, then `S ⊓ C_G(U) = V` (using `Ĥ = H`, the solvability of `H = U ⋔ S` and
P. Hall's theorem `C_H(F(H)) ≤ F(H)`). -/
theorem Q_le_V_of_le_S0 (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (h22 : Work.GW2.Lemma22Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥)
    (hS0 : Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0) :
    (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) ≤ Work.GW2.pCoreIn 2 B.Hhat := by
  have hHhat : B.Hhat = B.H := Hhat_eq_H_of_pCoreIn_le_S0 B hV hS0
  obtain ⟨n, hn2, hD⟩ := exists_dihedral_S (B := B) T hFT hctx
  -- `Q ≤ S₀`
  have hQleS0 : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) ≤ B.S0 := by
    intro x hx
    by_contra hx0
    have hx2 : orderOf x = 2 :=
      dihedral_index_two n hn2 _ _ hD B.S0_le B.S0_cyclic B.S0_index x
        (Subgroup.mem_inf.mp hx).1 hx0
    exact hx0 (hS0 (inv_mem_V (B := B) T h21 h22 hFT hctx hV x hx hx2))
  have hsplit : B.U ⊔ (B.S : Subgroup G) = B.H := by
    have hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := hD
    have hcentral : ∀ y ∈ (B.S : Subgroup G), y * B.t = B.t * y := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hy) B.t (by simp)).symm
    have h := T.split G B.S n hn2 hdih B.t (bSetup_t_mem_S B) B.t_order hcentral
    rw [show Subgroup.centralizer ({B.t} : Set G) = B.H from rfl, ← bSetup_U_eq B] at h
    exact h
  haveI hHsolv := H_solvable (B := B) hFT hsplit
  haveI hS0cyc : IsCyclic ↥B.S0 := B.S0_cyclic
  haveI hS0comm : CommGroup ↥B.S0 := IsCyclic.commGroup
  -- `O₂(H)` is `V`
  have hO2map : (OddOrder.Isaacs.Ch01.opCore 2 ↥B.H).map B.H.subtype
      = Work.GW2.pCoreIn 2 B.Hhat := by
    rw [hHhat, ← pCore_eq_opCore]
    rfl
  -- odd `p`-cores sit inside `U`
  have hOpU : ∀ p : (Nat.card ↥B.H).primeFactors, (p : ℕ) ≠ 2 →
      (OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥B.H).map B.H.subtype ≤ B.U := by
    intro p hp2
    have hpp : Nat.Prime (p : ℕ) := (Nat.mem_primeFactors.mp p.2).1
    refine le_oddCoreIn_of_normal_of_odd (Subgroup.map_subtype_le _) ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le _)]
      intro b a hb ha
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hb
      exact Subgroup.mem_map.mpr ⟨⟨a, ha⟩ * z * (⟨a, ha⟩ : ↥B.H)⁻¹,
        (OddOrder.Isaacs.Ch01.opCore.normal (p : ℕ) ↥B.H).conj_mem z hz ⟨a, ha⟩,
        by simp [mul_assoc]⟩
    · haveI : Fact (Nat.Prime (p : ℕ)) := ⟨hpp⟩
      have hcard := Nat.card_congr (Subgroup.equivMapOfInjective
          (OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥B.H)
          B.H.subtype B.H.subtype_injective).toEquiv
      rw [← hcard]
      obtain ⟨k, hk⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup (p : ℕ) ↥B.H).exists_card_eq
      rw [hk]
      exact (hpp.odd_of_ne_two hp2).pow
  intro x hx
  have hxS0 : x ∈ B.S0 := hQleS0 hx
  have hxH : x ∈ B.H := le_trans B.S0_le (bSetup_S_le_H B) hxS0
  have hxC : x ∈ Subgroup.centralizer (B.U : Set G) := (Subgroup.mem_inf.mp hx).2
  set x' : ↥B.H := ⟨x, hxH⟩ with hx'def
  -- `x'` centralizes every `O_p(H)`
  have hFle : (⨆ p : (Nat.card ↥B.H).primeFactors,
        OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥B.H) ≤
      Subgroup.centralizer ({x'} : Set ↥B.H) := by
    refine iSup_le fun p y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hcomm : y * x' = x' * y := by
      by_cases hp2 : (p : ℕ) = 2
      · have hyV : (y : G) ∈ Work.GW2.pCoreIn 2 B.Hhat := by
          have hymem : y ∈ OddOrder.Isaacs.Ch01.opCore 2 ↥B.H := by
            rwa [hp2] at hy
          have hmm : (y : G) ∈ (OddOrder.Isaacs.Ch01.opCore 2 ↥B.H).map B.H.subtype :=
            Subgroup.mem_map.mpr ⟨y, hymem, rfl⟩
          rwa [hO2map] at hmm
        have hyS0 : (y : G) ∈ B.S0 := hS0 hyV
        have hgen : ∃ g : G, Subgroup.zpowers g = B.S0 :=
          (Subgroup.isCyclic_iff_exists_zpowers_eq_top (H := B.S0)).mp
            (show IsCyclic ↥B.S0 from B.S0_cyclic)
        obtain ⟨g0, hg0⟩ := hgen
        refine Subtype.ext ?_
        show (y : G) * x = x * (y : G)
        exact comm_of_mem_zpowers (by rw [hg0]; exact hyS0) (by rw [hg0]; exact hxS0)
      · have hyU : (y : G) ∈ B.U := Subgroup.mem_subgroupOf.mp
          (hOpU p hp2 (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))
        refine Subtype.ext ?_
        show (y : G) * x = x * (y : G)
        exact Subgroup.mem_centralizer_iff.mp hxC (y : G) hyU
    exact hcomm.symm
  -- so `x' ∈ C_H(F(H))` and hence `x' ∈ F(H)`
  have hcent : x' ∈ Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting ↥B.H :
      Subgroup ↥B.H) : Set ↥B.H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ ⨆ p : (Nat.card ↥B.H).primeFactors,
        OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥B.H := by
      rwa [OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors] at hy
    have := hFle hy'
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this x' (by simp)).symm
  have hxF : x' ∈ OddOrder.Isaacs.Ch01.fitting ↥B.H :=
    OddOrder.GroupTheory.centralizer_fitting_le_fitting hcent
  -- `x'` is a `2`-element, hence lies in `O₂(H) = V`
  have hxp : ∃ k : ℕ, x' ^ 2 ^ k = 1 := by
    obtain ⟨a, ha⟩ := (B.S).isPGroup'.exists_card_eq
    refine ⟨a, ?_⟩
    have hdvd : orderOf x' ∣ 2 ^ a := by
      rw [show orderOf x' = orderOf x from (Subgroup.orderOf_coe x').symm]
      rw [← ha]
      exact Subgroup.orderOf_dvd_natCard (s := (B.S : Subgroup G)) (Subgroup.mem_inf.mp hx).1
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  -- the 2-part of `F(H)`
  have hxO2F : (⟨x', hxF⟩ : ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H))
      ∈ OddOrder.Isaacs.Ch01.opCore 2 ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H) := by
    obtain ⟨k, hk⟩ := hxp
    have hpg : IsPGroup 2 (Subgroup.zpowers (⟨x', hxF⟩ :
        ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H))) := by
      have hord : orderOf (⟨x', hxF⟩ : ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H)) ∣ 2 ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact Subtype.ext (by simpa using hk)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
      refine IsPGroup.of_card (n := j) ?_
      rw [Nat.card_zpowers, hj]
    obtain ⟨P, hP⟩ := hpg.exists_le_sylow
    haveI : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H) :=
      OddOrder.Isaacs.Ch01.fitting.isNilpotent
    have hPnorm : (P : Subgroup ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H)).Normal :=
      OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
    rw [← OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPnorm]
    exact hP (Subgroup.mem_zpowers _)
  -- transfer to `O₂(H) = V`
  have hle : (OddOrder.Isaacs.Ch01.opCore 2 ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H)).map
      (OddOrder.Isaacs.Ch01.fitting ↥B.H).subtype ≤
      OddOrder.Isaacs.Ch01.opCore 2 ↥B.H := by
    refine OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore ((OddOrder.Isaacs.Ch01.opCore_isPGroup 2
      ↥(OddOrder.Isaacs.Ch01.fitting ↥B.H)).map (OddOrder.Isaacs.Ch01.fitting ↥B.H).subtype)
  have hxO2 : x' ∈ OddOrder.Isaacs.Ch01.opCore 2 ↥B.H :=
    hle (Subgroup.mem_map.mpr ⟨_, hxO2F, rfl⟩)
  have : (x' : G) ∈ (OddOrder.Isaacs.Ch01.opCore 2 ↥B.H).map B.H.subtype :=
    Subgroup.mem_map.mpr ⟨x', hxO2, rfl⟩
  rwa [hO2map] at this

end Cases

/-- **Bender 1981, Theorem 2.6 (middle conjunct)**: `C_S(U) = O₂(Ĥ)`, i.e.
`S ⊓ C_G(U) = O₂(Ĥ)`. -/
theorem thm26a_CS_eq_O2 (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h22 : Work.GW2.Lemma22Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥ →
        (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) = Work.GW2.pCoreIn 2 B.Hhat := by
  intro G _ _ hFT hctx B hV
  refine le_antisymm ?_ ?_
  · by_cases h : Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0
    · exact Q_le_V_of_le_S0 (B := B) T h21 h22 hFT hctx hV h
    · exact Q_le_V_of_not_le_S0 (B := B) T h21 h22 hFT hctx hV h
  · exact V_le_Q (B := B)

end Work.CORE2A
