import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.Extra
import Submission.Work.CORE2A.isFourGroup_closure_pair
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.fourGroup_normalizer_not_le
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.Thm26bTmemLayer
import Submission.Work.CORE2A.oneInvClassIn_of_sylow_le_of_involutions_conj
import Submission.Work.DSTR.dihedralAbelianRank
import Submission.Work.DSTR.dihOrCycHered
import Submission.Work.DSTR.dihedralSubgroup
import Submission.Work.DSTR.dihedralQuotient
import Submission.Work.DSTR.quasisimpleSylow
import Submission.Work.DSTR.layerOneInvClass
import Submission.Work.FUS.Fusion

/-!
# CORE2A: `Thm26bOneClass` assembled from `K1`, `K3` and the torus crux

This file proves the assembly leaf `Work.CORE2A.c13_thm26bOneClass` of the
Gorenstein–Walter development (design pass 13, `_design_gw/Core13.lean` §2):

```
theorem c13_thm26bOneClass (T : LocalToolkit) (hTor : Thm26bTorusProp) : Thm26bOneClassProp
```

that is, in a minimal counterexample `BenderCtx G` with `B : BenderSetup G` and `E(Ĥ) ≠ 1`,
the subgroup `Ĥ` has a single class of involutions.

The mathematical argument: let `E = E(Ĥ) = layerIn B.Hhat` and `V = ⟨t, s⟩`.

* `c13_sylow_le_layerIn_of_card_eq_four` handles the case `|S| = 4`: `S` is then contained
  in any normal quasisimple subgroup `E₀ ≤ Ĥ`, hence in the layer.  Consequently
  `¬ (S ≤ E)` forces `|S| ≥ 8` (`t ∈ E` is `Work.CORE2A.Thm26bTmemLayer`).
* Choose an involution `s ∈ S ∖ E` (a "reflection": `S` is dihedral with rotation subgroup
  `S₀`, and `t ∈ S₀ ∩ E`).
* The torus crux `hTor` produces `y ∈ N_G(V)` with `t^y = s` and `4 ∣ |E ∩ Ĥ^y|`.
* `c13_exists_twoSubgroup_lt` (below) turns `4 ∣ |E ∩ Ĥ^y|`, together with `E ∩ Ĥ^y ⊴ Ĥ ∩ Ĥ^y`
  and `V ∩ (E ∩ Ĥ^y) = ⟨t⟩`, into a `2`-subgroup `W₀ ≤ Ĥ ∩ Ĥ^y` strictly containing `V`.
* `c13_K3_aux` (below) says that no such `W₀` exists: any `2`-subgroup of `Ĥ ∩ Ĥ^y` containing
  `V` equals `V` (the normalizer condition in the `2`-group `W₀` produces `w ∈ N_{W₀}(V) ∖ V`
  which the normality of `E` and of `E^y` forces to centralize `V`; then `V ⊔ ⟨w⟩` is an abelian
  `2`-subgroup of `G`, hence — by the abelian rank of the dihedral group `S` — of order `≤ 4`).

The contradiction rules out `S ≰ E(Ĥ)`, and `c13_oneInvClassIn_of_sylow_le_layer` then gives
the conclusion.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

section Aux

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Elementary four-group bookkeeping -/

/-- `⟨a⟩ ⊔ ⟨b⟩ = ⟨{a, b}⟩`. -/
theorem c13_zpowers_sup_eq_closure {a b : G} :
    (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = Subgroup.closure ({a, b} : Set G) := by
  have h : ({a} : Set G) ∪ {b} = {a, b} := by ext x; simp [or_comm]
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, h]

/-- Two distinct commuting involutions generate a Klein four-group. -/
theorem c13_isFourGroup_zpowers_sup {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hc : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    Work.GW2.IsFourGroup (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) := by
  rw [c13_zpowers_sup_eq_closure]
  exact isFourGroup_closure_pair ha hb hc ha1 hb1 hab

/-- `⟨a, b⟩ ≤ K^g` iff both generators lie in `K^g`. -/
theorem c13_zpowers_sup_le_conjSub_iff {g : G} {K : Subgroup G} {a b : G} :
    (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) ≤ Work.GW2.conjSub g K ↔
      a ∈ Work.GW2.conjSub g K ∧ b ∈ Work.GW2.conjSub g K := by
  constructor
  · intro h
    exact ⟨h (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)),
           h (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))⟩
  · rintro ⟨ha, hb⟩
    exact sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)

/-- For a four-group `V = ⟨t, s⟩` meeting a subgroup `E` in `t` (with `s ∉ E`), one has
`V ⊓ E = ⟨t⟩`. -/
theorem c13_inf_zpowers_sup_eq_zpowers_of_isFourGroup {E : Subgroup G} {t s : G}
    (hV4 : Work.GW2.IsFourGroup (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G))
    (htE : t ∈ E) (hsE : s ∉ E) (ht2 : orderOf t = 2) :
    (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) ⊓ E = Subgroup.zpowers t := by
  set V : Subgroup G := (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G)
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have htle : Subgroup.zpowers t ≤ V ⊓ E :=
    le_inf (Subgroup.zpowers_le.mpr htV) (Subgroup.zpowers_le.mpr htE)
  have hne : V ⊓ E ≠ V := by
    intro h
    exact hsE (h ▸ hsV).2
  have hcardV : Nat.card V = 4 := hV4.1
  have hcardt : Nat.card ↥(Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, ht2]
  have heq : Nat.card ↥((V ⊓ E).subgroupOf V) = Nat.card ↥(V ⊓ E) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hdiv : Nat.card ↥(V ⊓ E) ∣ 4 := by
    rw [← heq, ← hcardV]
    exact Subgroup.card_subgroup_dvd_card ((V ⊓ E).subgroupOf V)
  have hlt : Nat.card ↥(V ⊓ E) < 4 := by
    rw [← hcardV]
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left hne)
  have hge : 2 ≤ Nat.card ↥(V ⊓ E) := by
    calc 2 = Nat.card ↥(Subgroup.zpowers t) := hcardt.symm
      _ ≤ Nat.card ↥(V ⊓ E) := Subgroup.card_le_of_le htle
  have h2 : Nat.card ↥(V ⊓ E) = 2 := by
    have hdiv' : Nat.card ↥(V ⊓ E) ∣ 2 ^ 2 := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rwa [this] at hdiv
    obtain ⟨k, _, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv'
    have hk1 : k = 1 := by
      interval_cases k
      · rw [hk_eq] at hge; norm_num at hge
      · rfl
      · rw [hk_eq] at hlt; norm_num at hlt
    rw [hk_eq, hk1]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge htle (by rw [h2, hcardt])).symm

/-! ## 2. Abelian subgroups of a dihedral group, transported -/

/-- An abelian subgroup of a subgroup isomorphic to a dihedral group is cyclic or of order at most
`4`.  (Transport of `Work.DSTR.dihedralAbelianRank` along the isomorphism.) -/
theorem c13_isCyclic_or_card_le_four_of_le_dihedral {A Q : Subgroup G} {n : ℕ}
    (e : ↥Q ≃* DihedralGroup n) (hle : A ≤ Q) (hcomm : IsMulCommutative ↥A) :
    IsCyclic ↥A ∨ Nat.card ↥A ≤ 4 := by
  let f : ↥A →* DihedralGroup n := e.toMonoidHom.comp (Subgroup.inclusion hle)
  have hf_inj : Function.Injective f := e.injective.comp (Subgroup.inclusion_injective hle)
  have hcommA : IsMulCommutative ↥f.range := by
    rw [isMulCommutative_iff]
    intro x y
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    show (x : DihedralGroup n) * (y : DihedralGroup n) =
      (y : DihedralGroup n) * (x : DihedralGroup n)
    rw [← ha, ← hb, ← map_mul, ← map_mul, hcomm.is_comm.comm a b]
  let g : ↥A ≃* ↥f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨by
      intro a b hab
      apply hf_inj
      have h := congrArg Subtype.val hab
      rwa [MonoidHom.coe_rangeRestrict f a, MonoidHom.coe_rangeRestrict f b] at h,
     f.rangeRestrict_surjective⟩
  have hcard : Nat.card ↥A = Nat.card ↥f.range := Nat.card_congr g.toEquiv
  rcases Work.DSTR.dihedralAbelianRank n f.range hcommA with hcyc | hle4
  · exact Or.inl (g.isCyclic.mpr hcyc)
  · exact Or.inr (by rw [hcard]; exact hle4)

/-- An abelian `2`-subgroup of a group with cyclic or dihedral Sylow `2`-subgroups is cyclic or of
order at most `4`. -/
theorem c13_isCyclic_or_card_le_four_of_isPGroup (hsyl : Work.GW2.DihOrCycSylow G)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hcomm : IsMulCommutative ↥P) :
    IsCyclic ↥P ∨ Nat.card ↥P ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  rcases hsyl Q with hcyc | ⟨n, ⟨e⟩⟩
  · refine Or.inl ?_
    haveI : IsCyclic ↥(Q : Subgroup G) := hcyc
    exact Subgroup.isCyclic_of_le hPQ
  · exact c13_isCyclic_or_card_le_four_of_le_dihedral e hPQ hcomm

/-! ## 3. The layer `E(Ĥ)` and the reduction to `S ≤ E(Ĥ)` -/

theorem c13_layer_normal (X : Type) [Group X] : (Work.GW2.layer X).Normal := by
  rw [Work.GW2.layer]
  exact Subgroup.sSup_normal _ (fun E hE => hE.1)

/-- `E(K) = (layer K).map K.subtype` is normalized by `K`. -/
theorem c13_layerIn_normal (K : Subgroup G) :
    ∀ h ∈ K, ∀ x ∈ layerIn K, h * x * h⁻¹ ∈ layerIn K := by
  have hl : (layer K).Normal := c13_layer_normal ↥K
  intro h hh x hx
  rw [Work.GW2.layerIn] at hx ⊢
  obtain ⟨e, he, hxe⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * e * ⟨h, hh⟩⁻¹, hl.conj_mem e he ⟨h, hh⟩, ?_⟩
  rw [← hxe, map_mul, map_mul, map_inv]
  rfl

theorem c13_layerOneInvClass_inst : Work.GW2.LayerOneInvClassProp :=
  Work.DSTR.layerOneInvClass
    (Work.DSTR.dihOrCycHered Work.DSTR.dihedralSubgroup Work.DSTR.dihedralQuotient)
    Work.DSTR.quasisimpleSylow Work.FUS.involutionFusionProp

/-- A subgroup `(E.map K.subtype).subgroupOf K` is `E`. -/
theorem c13_subgroupOf_map_subtype (K : Subgroup G) (E : Subgroup ↥K) :
    ((E.map K.subtype).subgroupOf K) = E := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp hx
    have h1 : e = x := Subtype.ext hex
    rwa [h1] at he
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem c13_orderOf_coe_subtype (K : Subgroup G) (x : ↥K) :
    orderOf x = orderOf ((x : G)) :=
  (Subgroup.orderOf_coe x).symm

/-- A nontrivial layer contains a normal quasisimple subgroup. -/
theorem c13_exists_normal_quasisimple (K : Subgroup G) (h : layerIn K ≠ ⊥) :
    ∃ E : Subgroup ↥K, E.Normal ∧ IsQuasisimple E := by
  by_contra hcon
  have hempty : {E : Subgroup ↥K | E.Normal ∧ IsQuasisimple E} = ∅ := by
    ext E
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    exact hcon ⟨E, h1, h2⟩
  refine h ?_
  show (layer ↥K).map K.subtype = ⊥
  rw [Work.GW2.layer, hempty, sSup_empty, Subgroup.map_bot]

/-- **The reduction of Bender 2.6, step 2.**  If the Sylow `2`-subgroup `S` of `G` is contained
in the layer `E(Ĥ)`, then `Ĥ` has a single class of involutions. -/
theorem c13_oneInvClassIn_of_sylow_le_layer (T : LocalToolkit) (hFT : FeitThompsonProp)
    (hbc : BenderCtx G) (B : BenderSetup G) (hE : layerIn B.Hhat ≠ ⊥)
    (hS : (B.S : Subgroup G) ≤ layerIn B.Hhat) : OneInvClassIn B.Hhat := by
  classical
  obtain ⟨E, hEnorm, hEquasi⟩ := c13_exists_normal_quasisimple (K := B.Hhat) hE
  have hSle : (B.S : Subgroup G) ≤ B.Hhat := bSetup_S_le_Hhat B
  have hhat_lt : Nat.card ↥B.Hhat < Nat.card G := by
    have hdvd : Nat.card ↥B.Hhat ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have hle : Nat.card ↥B.Hhat ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdvd
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Subgroup.eq_top_of_card_eq B.Hhat h) B.Hhat_coatom.ne_top
  have hsyHhat : DihOrCycSylow ↥B.Hhat := dihOrCycSylow_subgroup hbc.sylow B.Hhat
  have hDGHat : IsDGroup ↥B.Hhat := hbc.ih ↥B.Hhat hhat_lt hsyHhat
  have hlayer_eq : layer ↥B.Hhat = E :=
    (T.lay ↥B.Hhat hFT hsyHhat hDGHat E hEnorm hEquasi).1
  have hC3 : C3OneInvClassIn E :=
    c13_layerOneInvClass_inst ↥B.Hhat hFT hsyHhat E hEnorm hEquasi
  have hconj : ∀ x ∈ layerIn B.Hhat, orderOf x = 2 →
      ∀ y ∈ layerIn B.Hhat, orderOf y = 2 →
      ∃ g ∈ layerIn B.Hhat, g * x * g⁻¹ = y := by
    intro x hx hx2 y hy hy2
    simp only [Work.GW2.layerIn] at hx hy
    rw [hlayer_eq] at hx hy
    obtain ⟨x', hx'E, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy'E, rfl⟩ := Subgroup.mem_map.mp hy
    have hx'2 : orderOf x' = 2 := by rw [c13_orderOf_coe_subtype B.Hhat x']; exact hx2
    have hy'2 : orderOf y' = 2 := by rw [c13_orderOf_coe_subtype B.Hhat y']; exact hy2
    obtain ⟨g, hgE, hg⟩ := hC3 x' hx'E y' hy'E hx'2 hy'2
    have hglayer : g ∈ layer ↥B.Hhat := by rw [hlayer_eq]; exact hgE
    refine ⟨(g : ↥B.Hhat), ?_, ?_⟩
    · simp only [Work.GW2.layerIn]
      exact Subgroup.mem_map.mpr ⟨g, hglayer, rfl⟩
    · simpa using congrArg (fun z : ↥B.Hhat => (z : G)) hg
  have hEK : layerIn B.Hhat ≤ B.Hhat := by
    simp only [Work.GW2.layerIn]
    rw [hlayer_eq]
    exact Subgroup.map_subtype_le _
  have hsub : ((layerIn B.Hhat).subgroupOf B.Hhat) = E := by
    simp only [Work.GW2.layerIn]
    rw [hlayer_eq]
    exact c13_subgroupOf_map_subtype B.Hhat E
  have hEn : ((layerIn B.Hhat).subgroupOf B.Hhat).Normal := hsub ▸ hEnorm
  exact oneInvClassIn_of_sylow_le_of_involutions_conj (K := B.Hhat) (E := layerIn B.Hhat)
    B.S hSle hEK hEn hS hconj

/-! ## 4. `|S| = 4` forces `S ≤ E(Ĥ)` -/

/-- A Sylow `2`-subgroup of order `< 8` of a finite group lies in every normal quasisimple
subgroup. -/
theorem c13_sylow_le_of_card_lt_eight {Y : Type} [Group Y] [Finite Y]
    (hFT : FeitThompsonProp) (S : Sylow 2 Y) (E : Subgroup Y) (hEn : E.Normal)
    (hEq : IsQuasisimple E) (hcard : Nat.card (S : Subgroup Y) < 8) :
    (S : Subgroup Y) ≤ E := by
  classical
  haveI hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup Y := (S : Subgroup Y) ⊓ E with hPdef
  have hPsub : IsPGroup 2 (P.subgroupOf E) := (odd_index_inf_sylow_subgroupOf_aux S E hEn).1
  have hPodd : Odd (P.subgroupOf E).index := (odd_index_inf_sylow_subgroupOf_aux S E hEn).2
  have hPidx : ¬ 2 ∣ (P.subgroupOf E).index :=
    fun h => (Nat.not_even_iff_odd.mpr hPodd) (even_iff_two_dvd.mpr h)
  have hnc : ¬ IsCyclic ↥(P.subgroupOf E) :=
    Work.DSTR.quasisimpleSylow Y hFT E hEq (hPsub.toSylow hPidx)
  obtain ⟨k, hk⟩ := hPsub.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hcon
    have hk1 : k ≤ 1 := by omega
    have hdvd : Nat.card ↥(P.subgroupOf E) ∣ 2 := by
      rw [hk, show (2 : ℕ) = 2 ^ 1 from (pow_one 2).symm]
      exact Nat.pow_dvd_pow 2 hk1
    exact hnc (isCyclic_of_card_dvd_prime hdvd)
  have hcardP : 4 ≤ Nat.card ↥P := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ≤ E)).toEquiv]
    rw [hk, show (4 : ℕ) = 2 ^ 2 from by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have hPleS : P ≤ (S : Subgroup Y) := inf_le_left
  obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
  have h4le : 4 ≤ Nat.card (S : Subgroup Y) :=
    le_trans hcardP (Nat.card_le_card_of_injective (Subgroup.inclusion hPleS)
      (Subgroup.inclusion_injective hPleS))
  have hm2 : 2 ≤ m := by
    have h2m : 2 ^ 2 ≤ 2 ^ m := by rw [← hm]; simpa using h4le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h2m
  have hm3 : m < 3 := by
    by_contra hcon
    have hcon' : 3 ≤ m := by omega
    have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hcon'
    rw [← hm] at h8
    omega
  have hcardS : Nat.card (S : Subgroup Y) = 4 := by
    rw [hm, show m = 2 by omega]
    norm_num
  have hPS : P = (S : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hPleS (by rw [hcardS]; exact hcardP)
  rw [← hPS]
  exact inf_le_right

/-- If `|B.S| = 4` then `B.S ≤ E(Ĥ)`. -/
theorem c13_sylow_le_layerIn_of_card_eq_four (T : LocalToolkit) (hFT : FeitThompsonProp)
    (hbc : BenderCtx G) (B : BenderSetup G) (hE : layerIn B.Hhat ≠ ⊥)
    (hcard4 : Nat.card (B.S : Subgroup G) = 4) : (B.S : Subgroup G) ≤ layerIn B.Hhat := by
  classical
  obtain ⟨E0, hE0n, hE0q⟩ := c13_exists_normal_quasisimple (K := B.Hhat) hE
  have hSle : (B.S : Subgroup G) ≤ B.Hhat := bSetup_S_le_Hhat B
  let S' : Sylow 2 ↥B.Hhat := (B.S).subtype hSle
  have hS'coe : (S' : Subgroup ↥B.Hhat) = (B.S : Subgroup G).subgroupOf B.Hhat :=
    Sylow.coe_subtype (B.S) hSle
  have hcardS' : Nat.card (S' : Subgroup ↥B.Hhat) = Nat.card (B.S : Subgroup G) := by
    rw [hS'coe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv
  have hle : (S' : Subgroup ↥B.Hhat) ≤ E0 :=
    c13_sylow_le_of_card_lt_eight hFT S' E0 hE0n hE0q (by rw [hcardS', hcard4]; norm_num)
  intro x hx
  rw [Work.GW2.layerIn]
  exact Subgroup.mem_map.mpr
    ⟨⟨x, hSle hx⟩, le_sSup (show E0 ∈ {E : Subgroup ↥B.Hhat | E.Normal ∧ IsQuasisimple E}
        from ⟨hE0n, hE0q⟩) (hle (by rw [hS'coe]; exact Subgroup.mem_subgroupOf.mpr hx)), rfl⟩

/-! ## 5. An involution of `S` outside `E(Ĥ)` -/

/-- If `S ⊄ E(Ĥ)` then some involution of `S` lies outside `E(Ĥ)`. -/
theorem c13_exists_involution_notMem (hbc : BenderCtx G) (B : BenderSetup G)
    (hnot : ¬ (B.S : Subgroup G) ≤ layerIn B.Hhat) :
    ∃ s ∈ (B.S : Subgroup G), orderOf s = 2 ∧ s ∉ layerIn B.Hhat := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hbS, hbS0⟩ := bSetup_exists_mem_S_not_mem_S0 B
  obtain ⟨n, hn2, hn⟩ := fnbt_exists_dihedral hbc B
  obtain ⟨e⟩ := hn
  have hord2 : ∀ t ∈ (B.S : Subgroup G), t ∉ B.S0 → orderOf t = 2 :=
    dihedral_index_two n hn2 (B.S : Subgroup G) B.S0 ⟨e⟩ B.S0_le B.S0_cyclic B.S0_index
  have hb2 : orderOf b = 2 := hord2 b hbS hbS0
  have hbE : b ∈ layerIn B.Hhat := hcon b hbS hb2
  apply hnot
  intro y hy
  by_cases hy0 : y ∈ B.S0
  · obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top B.S0).mp B.S0_cyclic
    have hgS0 : g ∈ B.S0 := hg ▸ Subgroup.mem_zpowers g
    have hgS : g ∈ (B.S : Subgroup G) := B.S0_le hgS0
    have hgE : g ∈ layerIn B.Hhat := by
      by_contra hgnE
      have hgbS : g * b ∈ (B.S : Subgroup G) := (B.S).mul_mem hgS hbS
      have hgbS0 : g * b ∉ B.S0 := fun hmem =>
        hbS0 (by
          have h1 : b = g⁻¹ * (g * b) := by group
          rw [h1]
          exact B.S0.mul_mem (B.S0.inv_mem hgS0) hmem)
      have hgb2 : orderOf (g * b) = 2 := hord2 (g * b) hgbS hgbS0
      have hgbE : g * b ∈ layerIn B.Hhat := hcon (g * b) hgbS hgb2
      have hgeq : g = (g * b) * b⁻¹ := by group
      exact hgnE (by
        rw [hgeq]
        exact (layerIn B.Hhat).mul_mem hgbE ((layerIn B.Hhat).inv_mem hbE))
    have hyz : y ∈ Subgroup.zpowers g := by rw [hg]; exact hy0
    exact Subgroup.zpowers_le.mpr hgE hyz
  · exact hcon y hy (hord2 y hy hy0)

/-! ## 6. The normalizer condition inside a `2`-group -/

/-- In a finite `2`-group every proper subgroup is strictly contained in its normalizer. -/
theorem c13_normalizerCondition_witness {X : Type} [Group X] [Finite X] (hX : IsPGroup 2 X)
    {V : Subgroup X} (hlt : V < ⊤) :
    ∃ w ∈ Subgroup.normalizer (V : Set X), w ∉ V := by
  haveI : Group.IsNilpotent X := hX.isNilpotent
  exact SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := X) V hlt)

/-- In a `2`-subgroup `W0 ≤ G` properly containing `V`, there is an element of `N_G(V) ∩ W0`
outside `V`. -/
theorem c13_exists_normalizer_witness {W0 V : Subgroup G} (hW0 : IsPGroup 2 W0) (hVW0 : V ≤ W0)
    (hne : V ≠ W0) :
    ∃ w ∈ W0, w ∈ Subgroup.normalizer (V : Set G) ∧ w ∉ V := by
  set V' : Subgroup ↥W0 := V.subgroupOf W0 with hV'def
  have hV'lt : V' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hne (le_antisymm hVW0 (by
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥W0) ∈ V' := htop.symm ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1))
  obtain ⟨w, hwN, hwV⟩ := c13_normalizerCondition_witness (X := ↥W0) hW0 hV'lt
  refine ⟨(w : G), w.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : (⟨x, hVW0 hx⟩ : ↥W0) ∈ V' := Subgroup.mem_subgroupOf.mpr hx
      have h := (Subgroup.mem_normalizer_iff.mp hwN ⟨x, hVW0 hx⟩).mp hx'
      exact Subgroup.mem_subgroupOf.mp (by simpa using h)
    · intro hx
      have hxW0 : x ∈ W0 := by
        have hmem : (w : G) * x * (w : G)⁻¹ ∈ V := hx
        have key : x = (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * (w : G) := by group
        rw [key]
        exact W0.mul_mem (W0.mul_mem (W0.inv_mem w.2) (hVW0 hmem)) w.2
      have hx'' : (⟨x, hxW0⟩ : ↥W0) ∈ V' := by
        have h := (Subgroup.mem_normalizer_iff.mp hwN ⟨x, hxW0⟩).mpr
          (Subgroup.mem_subgroupOf.mpr (by simpa using hx))
        simpa using h
      exact Subgroup.mem_subgroupOf.mp hx''
  · intro hcon
    exact hwV (Subgroup.mem_subgroupOf.mpr hcon)

/-! ## 7. `K3`: `2`-subgroups of `Ĥ ∩ Ĥ^y` containing `V = ⟨t, s⟩` are `V` -/

theorem c13_K3_aux (T : LocalToolkit) (hFT : FeitThompsonProp) (hbc : BenderCtx G)
    (B : BenderSetup G) (ht : B.t ∈ layerIn B.Hhat) (hS8 : 8 ≤ Nat.card (B.S : Subgroup G))
    (s : G) (hsS : s ∈ (B.S : Subgroup G)) (hs2 : orderOf s = 2) (hsE : s ∉ layerIn B.Hhat)
    (y : G)
    (hyV : y ∈ Subgroup.normalizer
      ((Subgroup.zpowers B.t ⊔ Subgroup.zpowers s : Subgroup G) : Set G))
    (hy : y * B.t * y⁻¹ = s) (W0 : Subgroup G) (hW0 : IsPGroup 2 W0)
    (hW0le : W0 ≤ B.Hhat ⊓ conjSub y B.Hhat)
    (hVW0 : Subgroup.zpowers B.t ⊔ Subgroup.zpowers s ≤ W0) :
    W0 = Subgroup.zpowers B.t ⊔ Subgroup.zpowers s := by
  classical
  set V : Subgroup G := Subgroup.zpowers B.t ⊔ Subgroup.zpowers s with hVdef
  set E : Subgroup G := layerIn B.Hhat with hEdef
  have ht1 : B.t ≠ 1 := bSetup_t_ne_one B
  have hs1 : s ≠ 1 := by intro h; rw [h, orderOf_one] at hs2; omega
  have ht2 : B.t ^ 2 = 1 := by have h := pow_orderOf_eq_one B.t; rwa [B.t_order] at h
  have hssq : s ^ 2 = 1 := by have h := pow_orderOf_eq_one s; rwa [hs2] at h
  have hts : B.t ≠ s := fun h => hsE (h ▸ ht)
  have hcomm : B.t * s = s * B.t :=
    mem_centralizer_singleton.mp (bSetup_S_le_H B hsS)
  have hV4 : IsFourGroup V := by
    rw [hVdef]
    exact c13_isFourGroup_zpowers_sup ht2 hssq hcomm ht1 hs1 hts
  have hVE : V ⊓ E = Subgroup.zpowers B.t := by
    rw [hVdef, hEdef]
    exact c13_inf_zpowers_sup_eq_zpowers_of_isFourGroup hV4 ht hsE B.t_order
  have hyinv : y⁻¹ * s * y = B.t := by
    calc y⁻¹ * s * y = y⁻¹ * (y * B.t * y⁻¹) * y := by rw [hy]
      _ = B.t := by group
  have hsEy : s ∈ conjSub y E := by
    rw [mem_conjSub_iff, hyinv]
    exact ht
  have htEy : B.t ∉ conjSub y E := by
    intro hcon
    rw [mem_conjSub_iff] at hcon
    have hyinvN : y⁻¹ ∈ Subgroup.normalizer (V : Set G) := (Subgroup.normalizer _).inv_mem hyV
    have hmemV : y⁻¹ * B.t * y ∈ V := by
      have h2 : B.t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
      have h3 : y⁻¹ * B.t * (y⁻¹)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyinvN B.t).mp h2
      simpa using h3
    have hmem : y⁻¹ * B.t * y ∈ V ⊓ E := ⟨hmemV, hcon⟩
    rw [hVE] at hmem
    have hord : orderOf (y⁻¹ * B.t * y) = 2 := by
      have hsemi : SemiconjBy y⁻¹ B.t (y⁻¹ * B.t * y) := by simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq y⁻¹ hsemi).symm.trans B.t_order
    have heq : y⁻¹ * B.t * y = B.t := by
      have h := eq_of_orderOf_eq_two_of_isCyclic
        (H := ↥(Subgroup.zpowers B.t)) (a := ⟨y⁻¹ * B.t * y, hmem⟩)
        (b := ⟨B.t, Subgroup.mem_zpowers B.t⟩) ?_ ?_
      · exact congrArg Subtype.val h
      · rw [Subgroup.orderOf_mk]; exact hord
      · rw [Subgroup.orderOf_mk]; exact B.t_order
    have hconj' : y * B.t * y⁻¹ = B.t := by
      have h2 : y * (y⁻¹ * B.t * y) * y⁻¹ = y * B.t * y⁻¹ :=
        congrArg (fun z => y * z * y⁻¹) heq
      rw [show y * (y⁻¹ * B.t * y) * y⁻¹ = B.t from by group] at h2
      exact h2.symm
    exact hts (hconj'.symm.trans hy)
  have hVEy : V ⊓ conjSub y E = Subgroup.zpowers s := by
    have hV4' : IsFourGroup (Subgroup.zpowers s ⊔ Subgroup.zpowers B.t : Subgroup G) :=
      c13_isFourGroup_zpowers_sup hssq ht2 hcomm.symm hs1 ht1 hts.symm
    have h := c13_inf_zpowers_sup_eq_zpowers_of_isFourGroup (E := conjSub y E) (t := s)
      (s := B.t) hV4' hsEy htEy hs2
    rwa [sup_comm] at h
  by_contra hne
  obtain ⟨w, hwW0, hwN, hwV⟩ :=
    c13_exists_normalizer_witness hW0 hVW0 (fun h => hne h.symm)
  have hwHhat : w ∈ B.Hhat := (Subgroup.mem_inf.mp (hW0le hwW0)).1
  have hwHy : w ∈ conjSub y B.Hhat := (Subgroup.mem_inf.mp (hW0le hwW0)).2
  -- `w` centralizes `t`
  have hwt : w * B.t * w⁻¹ = B.t := by
    have hmemV : w * B.t * w⁻¹ ∈ V := by
      have h2 : B.t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
      exact (Subgroup.mem_normalizer_iff.mp hwN B.t).mp h2
    have hmemE : w * B.t * w⁻¹ ∈ E := by
      rw [hEdef]
      exact c13_layerIn_normal B.Hhat w hwHhat B.t ht
    have hmem : w * B.t * w⁻¹ ∈ V ⊓ E := ⟨hmemV, hmemE⟩
    rw [hVE] at hmem
    have hord : orderOf (w * B.t * w⁻¹) = 2 := by
      have hsemi : SemiconjBy w B.t (w * B.t * w⁻¹) := by simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq w hsemi).symm.trans B.t_order
    have h := eq_of_orderOf_eq_two_of_isCyclic
      (H := ↥(Subgroup.zpowers B.t)) (a := ⟨w * B.t * w⁻¹, hmem⟩)
      (b := ⟨B.t, Subgroup.mem_zpowers B.t⟩) ?_ ?_
    · exact congrArg Subtype.val h
    · rw [Subgroup.orderOf_mk]; exact hord
    · rw [Subgroup.orderOf_mk]; exact B.t_order
  -- `w` centralizes `s`
  have hws : w * s * w⁻¹ = s := by
    have hmemV : w * s * w⁻¹ ∈ V := by
      have h2 : s ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
      exact (Subgroup.mem_normalizer_iff.mp hwN s).mp h2
    have hmemE : w * s * w⁻¹ ∈ conjSub y E := by
      rw [mem_conjSub_iff]
      have h1 : y⁻¹ * w * y ∈ B.Hhat := mem_conjSub_iff.mp hwHy
      have h2 : y⁻¹ * s * y ∈ layerIn B.Hhat := mem_conjSub_iff.mp hsEy
      have h3 : (y⁻¹ * w * y) * (y⁻¹ * s * y) * (y⁻¹ * w * y)⁻¹ ∈ layerIn B.Hhat :=
        c13_layerIn_normal B.Hhat (y⁻¹ * w * y) h1 (y⁻¹ * s * y) h2
      rw [hEdef]
      convert h3 using 1
      group
    have hmem : w * s * w⁻¹ ∈ V ⊓ conjSub y E := ⟨hmemV, hmemE⟩
    rw [hVEy] at hmem
    have hord : orderOf (w * s * w⁻¹) = 2 := by
      have hsemi : SemiconjBy w s (w * s * w⁻¹) := by simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq w hsemi).symm.trans hs2
    have h := eq_of_orderOf_eq_two_of_isCyclic
      (H := ↥(Subgroup.zpowers s)) (a := ⟨w * s * w⁻¹, hmem⟩)
      (b := ⟨s, Subgroup.mem_zpowers s⟩) ?_ ?_
    · exact congrArg Subtype.val h
    · rw [Subgroup.orderOf_mk]; exact hord
    · rw [Subgroup.orderOf_mk]; exact hs2
  -- `V ⊔ ⟨w⟩` is an abelian `2`-subgroup of `G`
  have hwt' : w * B.t = B.t * w := by
    calc w * B.t = (w * B.t * w⁻¹) * w := by group
      _ = B.t * w := by rw [hwt]
  have hws' : w * s = s * w := by
    calc w * s = (w * s * w⁻¹) * w := by group
      _ = s * w := by rw [hws]
  have hwCentV : w ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hVle : V ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [hVdef]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton]; exact hwt'
      · rw [mem_centralizer_singleton]; exact hws'
    exact (mem_centralizer_singleton.mp (hVle hx)).symm
  have hVcomm : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
  have hzw_comm : IsMulCommutative ↥(Subgroup.zpowers w) := by
    haveI : IsCyclic ↥(Subgroup.zpowers w) :=
      (Subgroup.isCyclic_iff_exists_zpowers_eq_top (Subgroup.zpowers w)).mpr ⟨w, rfl⟩
    exact IsCyclic.isMulCommutative
  have hab : IsMulCommutative ↥(V ⊔ Subgroup.zpowers w) :=
    isMulCommutative_sup_of_le_centralizer (Subgroup.zpowers_le.mpr hwCentV) hVcomm hzw_comm
  have hgrp : IsPGroup 2 ↥(V ⊔ Subgroup.zpowers w) :=
    IsPGroup.to_sup_of_normal_left' (p := 2) (H := V) (K := Subgroup.zpowers w)
      (hW0.to_le hVW0) (hW0.to_le (Subgroup.zpowers_le.mpr hwW0))
      (Subgroup.zpowers_le.mpr hwN)
  have hnotcyc : ¬ IsCyclic ↥(V ⊔ Subgroup.zpowers w) := by
    intro hc
    haveI : IsCyclic ↥(V ⊔ Subgroup.zpowers w) := hc
    haveI : IsCyclic ↥V :=
      Subgroup.isCyclic_of_le (H' := V ⊔ Subgroup.zpowers w) le_sup_left
    refine hts ?_
    have hBt : (⟨B.t, Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)⟩ : ↥V) =
        ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic ?_ ?_
    · exact congrArg Subtype.val hBt
    · rw [Subgroup.orderOf_mk]; exact B.t_order
    · rw [Subgroup.orderOf_mk]; exact hs2
  rcases c13_isCyclic_or_card_le_four_of_isPGroup hbc.sylow hgrp hab with hcyc | hcard
  · exact hnotcyc hcyc
  · have hcardV : Nat.card ↥V = 4 := hV4.1
    have hle : Nat.card ↥V ≤ Nat.card ↥(V ⊔ Subgroup.zpowers w) :=
      Subgroup.card_le_of_le le_sup_left
    have hEq : V = (V ⊔ Subgroup.zpowers w : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    exact hwV (hEq.symm ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w))

end Aux

theorem c13_exists_twoSubgroup_lt {G : Type} [Group G] [Finite G] {M E0 V : Subgroup G}
    (hE0le : E0 ≤ M)
    (hE0nM : (E0.subgroupOf M).Normal) (hVle : V ≤ M) (hV4 : IsFourGroup V)
    (hVinf : Nat.card ↥(V ⊓ E0) = 2) (h4 : 4 ∣ Nat.card ↥E0) :
    ∃ W0 : Subgroup G, IsPGroup 2 W0 ∧ W0 ≤ M ∧ V ≤ W0 ∧ W0 ≠ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVg : IsPGroup 2 ↥(V.subgroupOf M) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVle).toEquiv, hV4.1]
    norm_num
  obtain ⟨W, hV'W⟩ := hVg.exists_le_sylow
  refine ⟨W.map M.subtype, ?_, Subgroup.map_subtype_le (H := M) W, ?_, ?_⟩
  · exact (W.isPGroup').of_equiv (Subgroup.equivMapOfInjective W M.subtype M.subtype_injective)
  · have h := Subgroup.map_mono (f := M.subtype) hV'W
    rwa [Subgroup.map_subgroupOf_eq_of_le hVle] at h
  · intro hWV
    have hW' : W = V.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [hWV, Subgroup.map_subgroupOf_eq_of_le hVle]
    have hcardW : Nat.card ↥W = 4 := by
      have h1 : Nat.card ↥W = Nat.card ↥(W.map M.subtype) :=
        Nat.card_congr (Subgroup.equivMapOfInjective W M.subtype M.subtype_injective).toEquiv
      rw [h1, hWV]; exact hV4.1
    set E0' : Subgroup ↥M := E0.subgroupOf M with hE0'def
    have hE0'n : E0'.Normal := hE0nM
    set Q : Subgroup ↥E0' := ((W : Subgroup ↥M) ⊓ E0').subgroupOf E0' with hQdef
    have hQodd : Odd Q.index := (odd_index_inf_sylow_subgroupOf_aux W E0' hE0'n).2
    have hcardE0' : Nat.card ↥E0' = Nat.card ↥E0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0le).toEquiv
    have h4E0' : 4 ∣ Nat.card ↥E0' := by rw [hcardE0']; exact h4
    have hprod : Nat.card ↥E0' = Nat.card ↥Q * Q.index := (Subgroup.card_mul_index Q).symm
    have h4Q : 4 ∣ Nat.card ↥Q := by
      rw [hprod] at h4E0'
      have hcop : Nat.Coprime 4 Q.index := by
        have h2 : Nat.Coprime 2 Q.index := Nat.coprime_two_left.mpr hQodd
        have h3 : Nat.Coprime (2 ^ 2) Q.index :=
          (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 Q.index).mpr h2
        simpa using h3
      exact hcop.dvd_of_dvd_mul_right h4E0'
    have hQcard : Nat.card ↥Q = Nat.card ↥((W : Subgroup ↥M) ⊓ E0') :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hinf : (W : Subgroup ↥M) ⊓ E0' = (V ⊓ E0).subgroupOf M := by
      rw [hW', hE0'def]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    have hMge : V ⊓ E0 ≤ M := le_trans inf_le_right hE0le
    have hVinfcard : Nat.card ↥((V ⊓ E0).subgroupOf M) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMge).toEquiv]
      exact hVinf
    have hQeq : Nat.card ↥Q = 2 := by rw [hQcard, hinf, hVinfcard]
    have hQ4 : 4 ≤ Nat.card ↥Q := Nat.le_of_dvd Nat.card_pos h4Q
    omega

/-- **The leaf of the CORE2A area.**  In a minimal counterexample, if the layer of `Ĥ` is
nontrivial then `Ĥ` has a single class of involutions. -/
theorem c13_thm26bOneClass (T : Work.GW2.LocalToolkit) (hTor : Work.GW2.Thm26bTorusProp) :
    Work.GW2.Thm26bOneClassProp := by
  intro G _instG _instF hFT hbc B hE
  classical
  suffices hS : (B.S : Subgroup G) ≤ layerIn B.Hhat from
    c13_oneInvClassIn_of_sylow_le_layer T hFT hbc B hE hS
  by_contra hSnot
  have htE : B.t ∈ layerIn B.Hhat := Thm26bTmemLayer T hFT hbc B hE
  have hS8 : 8 ≤ Nat.card (B.S : Subgroup G) := by
    obtain ⟨k, hk⟩ := (B.S).isPGroup'.exists_card_eq
    have h4 := fnbt_card_S_ge_four (B := B)
    have h2k : 2 ^ 2 ≤ 2 ^ k := by rw [← hk]; simpa using h4
    have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h2k
    rcases eq_or_lt_of_le hk2 with h2 | h3
    · exfalso
      exact hSnot (c13_sylow_le_layerIn_of_card_eq_four T hFT hbc B hE
        (by rw [hk, ← h2]; norm_num))
    · calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
        _ = Nat.card (B.S : Subgroup G) := hk.symm
  obtain ⟨s, hsS, hs2, hsE⟩ := c13_exists_involution_notMem hbc B hSnot
  obtain ⟨y, hyV, hy, h4dvd⟩ := hTor G hFT hbc B htE hS8 s hsS hs2 hsE
  set V : Subgroup G := Subgroup.zpowers B.t ⊔ Subgroup.zpowers s with hVdef
  set M : Subgroup G := B.Hhat ⊓ conjSub y B.Hhat with hMdef
  set E0 : Subgroup G := layerIn B.Hhat ⊓ conjSub y B.Hhat with hE0def
  have ht1 : B.t ≠ 1 := bSetup_t_ne_one B
  have hs1 : s ≠ 1 := by intro h; rw [h, orderOf_one] at hs2; omega
  have ht2 : B.t ^ 2 = 1 := by have h := pow_orderOf_eq_one B.t; rwa [B.t_order] at h
  have hssq : s ^ 2 = 1 := by have h := pow_orderOf_eq_one s; rwa [hs2] at h
  have hts : B.t ≠ s := fun h => hsE (h ▸ htE)
  have hcomm : B.t * s = s * B.t :=
    mem_centralizer_singleton.mp (bSetup_S_le_H B hsS)
  have hV4 : IsFourGroup V := by
    rw [hVdef]
    exact c13_isFourGroup_zpowers_sup ht2 hssq hcomm ht1 hs1 hts
  -- membership of `t` and `s` in `Ĥ^y`
  have hyinv : y⁻¹ * s * y = B.t := by
    calc y⁻¹ * s * y = y⁻¹ * (y * B.t * y⁻¹) * y := by rw [hy]
      _ = B.t := by group
  have hVleHhat : V ≤ B.Hhat := by
    rw [hVdef]
    exact sup_le (Subgroup.zpowers_le.mpr (bSetup_t_mem_Hhat B))
      (Subgroup.zpowers_le.mpr (bSetup_S_le_Hhat B hsS))
  have hsY : s ∈ conjSub y B.Hhat := by
    rw [mem_conjSub_iff, hyinv]
    exact bSetup_t_mem_Hhat B
  have htY : B.t ∈ conjSub y B.Hhat := by
    rw [mem_conjSub_iff]
    have hyinvN : y⁻¹ ∈ Subgroup.normalizer (V : Set G) := (Subgroup.normalizer _).inv_mem hyV
    have h2 : B.t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
    have h3 : y⁻¹ * B.t * (y⁻¹)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyinvN B.t).mp h2
    have h4 : y⁻¹ * B.t * y ∈ V := by simpa using h3
    exact hVleHhat h4
  have hVleM : V ≤ M := by
    rw [hMdef]
    exact le_inf hVleHhat (c13_zpowers_sup_le_conjSub_iff.mpr ⟨htY, hsY⟩)
  have hE0le : E0 ≤ M := by
    rw [hE0def, hMdef]
    exact inf_le_inf (Subgroup.map_subtype_le (layer ↥B.Hhat)) le_rfl
  have hEsub : ((layerIn B.Hhat).subgroupOf B.Hhat).Normal := by
    have h1 : ((layerIn B.Hhat).subgroupOf B.Hhat) = layer ↥B.Hhat := by
      show ((layer ↥B.Hhat).map B.Hhat.subtype).subgroupOf B.Hhat = layer ↥B.Hhat
      exact c13_subgroupOf_map_subtype B.Hhat (layer ↥B.Hhat)
    rw [h1]; exact c13_layer_normal ↥B.Hhat
  have hE0nM : (E0.subgroupOf M).Normal := by
    haveI := hEsub
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A' := layerIn B.Hhat)
      (A := B.Hhat) (conjSub y B.Hhat)
    rw [hE0def, hMdef]
    exact h
  have hVE : V ⊓ layerIn B.Hhat = Subgroup.zpowers B.t := by
    rw [hVdef]
    exact c13_inf_zpowers_sup_eq_zpowers_of_isFourGroup hV4 htE hsE B.t_order
  have hVinfE0 : Nat.card ↥(V ⊓ E0) = 2 := by
    have h1 : V ⊓ E0 = Subgroup.zpowers B.t := by
      rw [hVdef, hE0def, ← inf_assoc, hVE]
      exact inf_eq_left.mpr (Subgroup.zpowers_le.mpr htY)
    rw [h1, Nat.card_zpowers, B.t_order]
  obtain ⟨W0, hW0p, hW0le, hVW0, hW0ne⟩ :=
    c13_exists_twoSubgroup_lt hE0le hE0nM hVleM hV4 hVinfE0 h4dvd
  exact hW0ne (c13_K3_aux T hFT hbc B htE hS8 s hsS hs2 hsE y hyV hy W0 hW0p hW0le hVW0)

end Work.CORE2A
