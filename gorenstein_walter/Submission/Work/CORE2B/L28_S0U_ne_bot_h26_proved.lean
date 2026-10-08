import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.L28_t_mem_layer_proved
import Submission.Work.Dihedral.Defs
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

/-!
# AREA CORE2B — the leaf `Work.CORE2B.L28_S0U_ne_bot_h26` (Bender 1981, Lemma 2.8, p. 221)

Bender's Lemma 2.8: if `I_U(s) ⊴ U` for every `s ∈ S − S₀`, then `[S₀,U] ≠ 1`.  This file proves
the first assertion (with Theorem 2.6 available).

**Proof.**  Assume `[S₀,U] = ⊥`, i.e. `S₀ ≤ C(U)`.  By Theorem 2.6 (`h26`) the subgroup
`Γ := S ⊓ C(U)` equals `O₂(Ĥ)`, and `S₀ ≤ Γ ≤ S` with `[S : S₀] = 2`, so `Γ = S` or `Γ = S₀`.

* If `Γ = S`, then `S ≤ C(U)`, so for `s ∈ S − S₀` the set `I_U(s)` is trivial (an element of
  `U` commuting with `s` and inverted by `s` has order dividing `2` and dividing the odd number
  `|U|`, hence is `1`).  Taking `I := ⊥` gives exactly the configuration of Bender's Lemma 2.2
  (`h22`): `S₀ ≤ C(U)`, `I_U(s) = 1` is normal in `U`, and `N_G(X) ≤ H` holds vacuously for every
  `1 ≠ X ≤ I`.  Contradiction.

* If `Γ = S₀`, then `O₂(Ĥ) = S₀`, and the second alternative of Theorem 2.6 would make `S₀` a
  four-group, contradicting its cyclicity; hence `Ĥ = H`.  Again `(a)` and `(b)` of the
  configuration of Lemma 2.2 hold, so `(c)` must fail: there is `1 ≠ X ≤ I_U(s)` with
  `N_G(X) ≰ H`.  Put `M := N_G(X)`.  Then `S ≤ M` (`S₀ ≤ C(U) ≤ C(X)` and `s` inverts `X`), so
  `M ≠ ⊤`, `M ≰ Ĥ`, and `Ĥ ⇝ M` (the witness is `X` itself, which lies in `F(Ĥ)`: it is contained
  in `I_U(s)`, which is abelian and normal in `Ĥ`); hence `t ∈ E(M)` by the second assertion of
  Lemma 2.8 (`h27`, `L28_t_mem_layer_proved`).  But `M` is solvable: `C_M(X) = C_G(X)` has the
  cyclic Sylow 2-subgroup `S₀` (this is where the assumption `S₀ ≤ C(U)` and `X ≠ 1` are used),
  and `M/C_G(X)` has order `2·odd`; both are solvable by Burnside's normal `2`-complement theorem
  and Feit–Thompson.  A solvable group has trivial layer, so `t ∈ E(M) = 1`, contradiction.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-! ## 0. Ports of helper statements proved (as `private` lemmas) in `L28_t_mem_layer_proved` -/

section Ports

/-- **Auxiliary dihedral computation.**  In `DihedralGroup n` with `n ≥ 2`, a cyclic subgroup `T`
of index two consists of rotations, so every element outside `T` is a reflection of order `2`. -/
private lemma dihedral_cyclic_index_two_aux (n : ℕ) (hn : 2 ≤ n) (T : Subgroup (DihedralGroup n))
    (hcyc : IsCyclic T) (hidx : T.relIndex ⊤ = 2) :
    ∀ y : DihedralGroup n, y ∉ T → orderOf y = 2 := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hcardT : Nat.card T = n := by
    have h := Subgroup.relIndex_mul_card T ⊤
    rw [hidx, inf_top_eq, Subgroup.card_top, DihedralGroup.nat_card] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  intro y hy
  rcases eq_or_ne n 2 with hn2 | hn2
  · subst hn2
    have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem T)
    exact (orderOf_eq_two_iff (IsKleinFour.exponent_two (G := DihedralGroup 2))).mpr hy1
  · have hn3 : 3 ≤ n := by omega
    have hTrot : T = Work.Dihedral.rot n := by
      obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top T).mp hcyc
      have hordg : orderOf g = n := by rw [← Nat.card_zpowers g, hg, hcardT]
      have hgR : g ∈ Work.Dihedral.rot n := by
        rcases Work.Dihedral.eq_r_or_sr g with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact Work.Dihedral.r_mem_rot i
        · rw [DihedralGroup.orderOf_sr] at hordg; omega
      have hTR : T ≤ Work.Dihedral.rot n := by
        rw [← hg]; exact Subgroup.zpowers_le.mpr hgR
      exact Subgroup.eq_of_le_of_card_ge hTR (by rw [Work.Dihedral.nat_card_rot, hcardT])
    have hyR : y ∉ Work.Dihedral.rot n := by rw [← hTrot]; exact hy
    obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hyR
    exact DihedralGroup.orderOf_sr i

/-- Every element of `S \ S₀` has order `2`, when `S ≅ DihedralGroup n` (`n ≥ 2`) and `S₀ ≤ S` is
cyclic of index `2`. -/
private theorem dihedral_index_two {G : Type} [Group G] (n : ℕ) (hn : 2 ≤ n) (S S0 : Subgroup G)
    (hD : Nonempty (S ≃* DihedralGroup n)) (hS0 : S0 ≤ S) (hcyc : IsCyclic S0)
    (hidx : S0.relIndex S = 2) : ∀ s ∈ S, s ∉ S0 → orderOf s = 2 := by
  classical
  obtain ⟨e⟩ := hD
  intro s hs hs0
  have hcardS : Nat.card S = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
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
  have hy : e ⟨s, hs⟩ ∉ T := by
    rw [hT, Subgroup.mem_map]
    rintro ⟨x, hx, hxe⟩
    rw [Subgroup.mem_subgroupOf] at hx
    rw [e.injective hxe] at hx
    exact hs0 hx
  have h2 : orderOf (e ⟨s, hs⟩) = 2 :=
    dihedral_cyclic_index_two_aux n hn T hcycT hidxT (e ⟨s, hs⟩) hy
  have h2' : orderOf ((⟨s, hs⟩ : ↥S) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    rw [← orderOf_injective e.toMonoidHom e.injective (⟨s, hs⟩ : ↥S)]
    exact h2
  exact h2'

/-- `O(K)` has odd order. -/
private theorem oddCoreIn_odd {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Odd (Nat.card (Work.GW2.oddCoreIn K)) := by
  rw [Work.GW2.oddCoreIn]
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact Work.CORE2B.oddCore_odd (G := ↥K)

/-- `|S| = 2 * |S₀|`. -/
private theorem card_S_eq {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Nat.card (B.S : Subgroup G) = 2 * Nat.card B.S0 := by
  have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
  rw [B.S0_index, inf_eq_left.mpr B.S0_le] at h
  exact h.symm

/-- `S` has an element outside `S₀`. -/
private theorem exists_notMem_S0 {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    ∃ s0 ∈ (B.S : Subgroup G), s0 ∉ B.S0 := by
  by_contra h
  have hle : (B.S : Subgroup G) ≤ B.S0 := by
    intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  have heq : (B.S : Subgroup G) = B.S0 := le_antisymm hle B.S0_le
  have hcard := card_S_eq B
  rw [heq] at hcard
  have hpos : 0 < Nat.card B.S0 := Nat.card_pos
  omega

/-- `S` is dihedral of order `2n` with `n ≥ 2`. -/
private theorem S_dihedral {G : Type} [Group G] [Finite G] (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) := Work.CORE2B.BenderCtx_sylow_not_cyclic hCtx B.S
  rcases hCtx.sylow B.S with hcyc | ⟨n, hn⟩
  · exact absurd hcyc hnc
  · obtain ⟨heven, hne⟩ :=
      Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic hn.some B.S.isPGroup' hnc
    refine ⟨n, ?_, hn⟩
    obtain ⟨k, hk⟩ := heven
    have hne0 : n ≠ 0 := NeZero.ne n
    omega

/-- Every element of `S \ S₀` is an involution. -/
private theorem S_diff_S0_order_two {G : Type} [Group G] [Finite G] (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) :
    ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → orderOf s = 2 := by
  obtain ⟨n, hn2, ⟨e⟩⟩ := S_dihedral hCtx B
  exact dihedral_index_two n hn2 (B.S : Subgroup G) B.S0 ⟨e⟩ B.S0_le B.S0_cyclic B.S0_index

/-- `S₀ ◁ S`. -/
private theorem S0_normal_in_S {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    ∀ x ∈ (B.S : Subgroup G), ∀ y ∈ B.S0, x * y * x⁻¹ ∈ B.S0 := by
  have hidx : (B.S0.subgroupOf (B.S : Subgroup G)).index = 2 := B.S0_index
  have hNormal : (B.S0.subgroupOf (B.S : Subgroup G)).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  intro x hx y hy
  have h := hNormal.conj_mem (⟨y, B.S0_le hy⟩ : ↥(B.S : Subgroup G)) hy
    (⟨x, hx⟩ : ↥(B.S : Subgroup G))
  rw [Subgroup.mem_subgroupOf] at h
  exact h

/-- `t` is the central involution of `S`: it commutes with every element of `S`. -/
private theorem t_central_in_S {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := by
  classical
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  haveI := Fintype.ofFinite ↥B.S0
  have huniq : ∀ a b : ↥B.S0, orderOf a = 2 → orderOf b = 2 → a = b := by
    intro a b ha hb
    have hd : 2 ∣ Fintype.card ↥B.S0 := by
      rw [← Nat.card_eq_fintype_card, ← ha]
      exact orderOf_dvd_natCard a
    have hcard : Fintype.card {x : ↥B.S0 // orderOf x = 2} = 1 := by
      rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := ↥B.S0) hd, Nat.totient_two]
    exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)
  intro x hx
  have hxt : x * B.t * x⁻¹ ∈ B.S0 := S0_normal_in_S B x hx B.t B.t_mem
  have h2 : orderOf (⟨x * B.t * x⁻¹, hxt⟩ : ↥B.S0) = 2 := by
    rw [Subgroup.orderOf_mk]
    have key : orderOf (MulAut.conj x B.t) = orderOf B.t := by
      simpa using orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective B.t
    rw [← MulAut.conj_apply x B.t, key]
    exact B.t_order
  have ht2 : orderOf (⟨B.t, B.t_mem⟩ : ↥B.S0) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact B.t_order
  have heq : (⟨x * B.t * x⁻¹, hxt⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ := huniq _ _ h2 ht2
  have hval : x * B.t * x⁻¹ = B.t := congrArg Subtype.val heq
  calc x * B.t = (x * B.t * x⁻¹) * x := by group
    _ = B.t * x := by rw [hval]

/-- `S ≤ H = C_G(t)`. -/
private theorem S_le_H {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    (B.S : Subgroup G) ≤ B.H := by
  intro x hx
  rw [Work.GW2.BenderSetup.H, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (t_central_in_S B x hx).symm

/-- `H ≤ N_G(U)`. -/
private theorem H_le_normalizer_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.H ≤ Subgroup.normalizer (B.U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh u hu
  have hu' : u ∈ (Work.GW2.oddCore ↥B.H).map B.H.subtype := hu
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu'
  refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥B.H) * y * (⟨h, hh⟩ : ↥B.H)⁻¹, ?_, rfl⟩
  exact (Work.GW2.oddCore_normal ↥B.H).conj_mem y hy _

end Ports

/-! ## 1. Elementary helpers -/

/-- A cyclic group is not a four-group. -/
private theorem not_isFourGroup_of_isCyclic {G : Type} [Group G] {V : Subgroup G}
    (hcyc : IsCyclic V) : ¬ Work.GW2.IsFourGroup V := by
  intro hV
  obtain ⟨hcard, hsq⟩ := hV
  haveI := hcyc
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := ↥V)).mp hcyc
  have hord : orderOf g = 4 := by
    rw [← Nat.card_zpowers g, hg, Subgroup.card_top]
    exact hcard
  have h2 : g ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hsq (g : G) g.2
  have hd : orderOf g ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using h2
  have h12 : orderOf g = 1 ∨ orderOf g = 2 := (Nat.dvd_prime Nat.prime_two).mp hd
  omega

/-- `S = S₀ ⊔ ⟨s⟩` for `s ∈ S − S₀`. -/
private theorem S_eq_sup_zpowers {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) :
    B.S0 ⊔ Subgroup.zpowers s = (B.S : Subgroup G) := by
  have hle : B.S0 ⊔ Subgroup.zpowers s ≤ (B.S : Subgroup G) :=
    sup_le B.S0_le (Subgroup.zpowers_le.mpr hsS)
  have hne : B.S0 ⊔ Subgroup.zpowers s ≠ B.S0 := by
    intro h
    have hs : s ∈ B.S0 ⊔ Subgroup.zpowers s :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    rw [h] at hs
    exact hs0 hs
  have hpos : 0 < Nat.card B.S0 := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : B.S0 ≤ B.S0 ⊔ Subgroup.zpowers s)
  obtain ⟨l, hl⟩ := Subgroup.card_dvd_of_le hle
  have hkl : k * l = 2 := by
    have h : Nat.card B.S0 * (k * l) = 2 * Nat.card B.S0 := by
      rw [← Nat.mul_assoc, ← hk, ← hl, card_S_eq B]
    exact Nat.mul_left_cancel hpos (by rw [h, mul_comm])
  have hk2 : k = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp ⟨l, hkl.symm⟩ with h1 | h2
    · exfalso
      rw [h1, mul_one] at hk
      exact hne (Subgroup.eq_of_le_of_card_ge (H := B.S0) le_sup_left (le_of_eq hk)).symm
    · exact h2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hk, hk2, card_S_eq B]
  exact le_of_eq (Nat.mul_comm _ _)

/-- An abelian subgroup `J ≤ K` that is normalized by `K` lies in `F(K)`. -/
private theorem le_fittingIn_of_abelian_normal {G : Type} [Group G] {K J : Subgroup G}
    (hJK : J ≤ K) (hJnorm : K ≤ Subgroup.normalizer (J : Set G)) (hJab : IsMulCommutative J) :
    J ≤ Work.GW2.fittingIn K := by
  have hsub : J.subgroupOf K ≤ Work.GW2.fitting ↥K := by
    rw [Work.GW2.fitting]
    haveI hJn : (J.subgroupOf K).Normal := ⟨fun n hn g => by
      have hn' : (n : G) ∈ J := Subgroup.mem_subgroupOf.mp hn
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hJnorm g.2) (n : G)).mp hn'⟩
    rw [Subgroup.normal_le_normalCore]
    refine le_sSup ⟨hJn, ?_⟩
    haveI : IsMulCommutative ↥(J.subgroupOf K) :=
      isMulCommutative_iff.mpr (fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        have h := hJab.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp a.2⟩
          ⟨(b : G), Subgroup.mem_subgroupOf.mp b.2⟩
        simpa using h)
    exact CommGroup.isNilpotent
  have hmap : (J.subgroupOf K).map K.subtype = J := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJK]
  rw [Work.GW2.fittingIn, ← hmap]
  exact Subgroup.map_mono hsub

/-- A solvable group has trivial layer (it has no nontrivial quasisimple subgroup). -/
private theorem layer_eq_bot_of_isSolvable {X : Type} [Group X] (h : Group.IsSolvable X) :
    Work.GW2.layer X = ⊥ := by
  rw [Work.GW2.layer]
  refine le_bot_iff.mp (sSup_le ?_)
  rintro E ⟨hEn, hEq⟩
  by_contra hne
  haveI : Nontrivial ↥E := by
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
      simpa [Subgroup.eq_bot_iff_forall, le_bot_iff] using hne
    exact ⟨⟨x, hx⟩, 1, by simpa using hx1⟩
  haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hEq.1
  haveI : Group.IsSolvable ↥E := inferInstance
  exact (Group.IsPerfect.not_isSolvable ↥E) inferInstance

/-- A solvable subgroup `K` of `G` has trivial `E(K)`. -/
private theorem layerIn_eq_bot_of_isSolvable {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hsol : Group.IsSolvable ↥K) : Work.GW2.layerIn K = ⊥ := by
  rw [Work.GW2.layerIn, layer_eq_bot_of_isSolvable hsol, Subgroup.map_bot]

/-! ## 2. Finite groups with a cyclic Sylow 2-subgroup are solvable -/

/-- A finite group with a cyclic Sylow `2`-subgroup is solvable (given Feit–Thompson for groups of
odd order): Burnside's normal `2`-complement theorem (Mathlib's `IsCyclic.isComplement'`) produces
a normal complement `K` of odd order, solvable by Feit–Thompson, while the quotient is isomorphic
to the cyclic (hence solvable) Sylow subgroup. -/
theorem solvable_of_cyclic_sylow_two {N : Type} [Group N] [Finite N]
    (hFT : ∀ (K : Type) [Group K] [Finite K], Odd (Nat.card K) → Group.IsSolvable K)
    (P : Sylow 2 N) (hP : IsCyclic ↥(P : Subgroup N)) : Group.IsSolvable N := by
  by_cases hodd : Odd (Nat.card N)
  · exact hFT N hodd
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2dvd : 2 ∣ Nat.card N := by
      rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
      exact hodd
    have hmin : (Nat.card N).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2dvd
    let K : Subgroup N := (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hmin)).ker
    have hcomp : K.IsComplement' (P : Subgroup N) := IsCyclic.isComplement' hmin hP
    haveI hKnorm : K.Normal := MonoidHom.normal_ker _
    have hKodd : Odd (Nat.card K) := by
      rw [← Subgroup.IsComplement'.index_eq_card hcomp]
      exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact P.not_dvd_index)
    haveI : Group.IsSolvable ↥K := hFT ↥K hKodd
    haveI : Group.IsSolvable ↥(P : Subgroup N) := inferInstance
    have hiso : N ⧸ K ≃* ↥(P : Subgroup N) := Subgroup.IsComplement'.QuotientMulEquiv hcomp.symm
    haveI : Group.IsSolvable (N ⧸ K) :=
      Group.isSolvable_of_surjective (f := hiso.symm.toMonoidHom) hiso.symm.surjective
    exact Group.isSolvable_of_subgroup_quotient K

/-- A finite group of order `2 * m` with `m` odd is solvable (given Feit–Thompson): its Sylow
`2`-subgroups have order `2`, hence are cyclic. -/
private theorem solvable_of_card_two_mul_odd {N : Type} [Group N] [Finite N]
    (hFT : ∀ (K : Type) [Group K] [Finite K], Odd (Nat.card K) → Group.IsSolvable K)
    (m : ℕ) (hcard : Nat.card N = 2 * m) (hm : Odd m) : Group.IsSolvable N := by
  by_cases htriv : Nat.card N = 1
  · haveI : Subsingleton N := (Nat.card_eq_one_iff_unique.mp htriv).1
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2dvd : 2 ∣ Nat.card N := by rw [hcard]; exact dvd_mul_right 2 m
    obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := N)
    have hPne : (P : Subgroup N) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P h2dvd
    have hPcard : Nat.card ↥(P : Subgroup N) = 2 := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(P : Subgroup N))).mp P.isPGroup'
      have hdvd : 2 ^ j ∣ 2 * m := by
        rw [← hj, ← hcard]
        simpa using Subgroup.card_dvd_of_le (le_top : (P : Subgroup N) ≤ ⊤)
      have hcop : Nat.Coprime (2 ^ j) m :=
        Nat.Coprime.pow_left j ((Nat.coprime_two_right.mpr hm).symm)
      have hdvd2 : 2 ^ j ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
      have hne1 : 2 ^ j ≠ 1 := by
        intro h1
        have hc1 : Nat.card ↥(P : Subgroup N) = 1 := by rw [hj, h1]
        haveI : Subsingleton ↥(P : Subgroup N) := (Nat.card_eq_one_iff_unique.mp hc1).1
        refine hPne ((Subgroup.eq_bot_iff_forall (P : Subgroup N)).mpr fun x hx => ?_)
        exact congrArg Subtype.val
          (Subsingleton.elim (⟨x, hx⟩ : ↥(P : Subgroup N)) 1)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exact absurd h1 hne1
      · rw [hj, h2]
    have hcycP : IsCyclic ↥(P : Subgroup N) := by
      obtain ⟨g, hg⟩ : ∃ g : ↥(P : Subgroup N), g ≠ 1 := by
        by_contra h
        push_neg at h
        refine hPne ((Subgroup.eq_bot_iff_forall (P : Subgroup N)).mpr fun x hx => ?_)
        have := h ⟨x, hx⟩
        simpa using congrArg Subtype.val this
      refine (isCyclic_iff_exists_zpowers_eq_top).mpr ⟨g, ?_⟩
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      have hord : orderOf g = 2 := by
        have hdvd : orderOf g ∣ Nat.card ↥(P : Subgroup N) := orderOf_dvd_natCard g
        rw [hPcard] at hdvd
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hg
        · exact h
      rw [Subgroup.card_top, hPcard, Nat.card_zpowers, hord]
    exact solvable_of_cyclic_sylow_two hFT P hcycP

/-! ## 3. `N_G(X)` is solvable -/

/-- **The group-theoretic core of Lemma 2.8.**  Let `X ≠ 1` be a subgroup of `U = O(C(t))`
inverted by `s ∈ S − S₀`, with `S₀ ≤ C(U)`.  Then `N_G(X)` is solvable: `S ≤ N_G(X)`,
`C_G(X) ⊓ S = S₀` is a cyclic Sylow 2-subgroup of `C_G(X)`, and `N_G(X)/C_G(X)` has order
`2 · odd`. -/
theorem normalizer_solvable {G : Type} [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (B : Work.GW2.BenderSetup G)
    (hUodd : Odd (Nat.card B.U)) (hSc : B.S0 ≤ Subgroup.centralizer (B.U : Set G))
    (s : G) (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (X : Subgroup G) (hX : X ≠ ⊥) (hXle : X ≤ Work.GW2.invSet B.U s) :
    Group.IsSolvable ↥(Subgroup.normalizer (X : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := Subgroup.normalizer (X : Set G) with hM
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hXU : X ≤ B.U := fun x hx => (hXle hx).1
  have hinv : ∀ x ∈ X, s * x * s⁻¹ = x⁻¹ := fun x hx => (hXle hx).2
  have hS0C : B.S0 ≤ C := fun c hc => by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hSc hc) x (hXU hx)
  have hCM : C ≤ M := by rw [hM, hC]; exact Subgroup.centralizer_le_normalizer _
  have hsM : s ∈ M := by
    rw [hM, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rw [hinv x hx]; exact X.inv_mem hx
    · intro hx
      have h2 : s * (s * x * s⁻¹) * s⁻¹ = (s * x * s⁻¹)⁻¹ := hinv _ hx
      have h3 : s * x * s⁻¹ = x⁻¹ := by
        have key : s⁻¹ * (s * (s * x * s⁻¹) * s⁻¹) * s =
            s⁻¹ * (s * x * s⁻¹)⁻¹ * s := by rw [h2]
        simpa [mul_assoc] using key
      rw [h3] at hx
      simpa using X.inv_mem hx
  have hSM : (B.S : Subgroup G) ≤ M := by
    rw [← S_eq_sup_zpowers B hsS hs0]
    exact sup_le (hS0C.trans hCM) (Subgroup.zpowers_le.mpr hsM)
  have hs2C : s * s ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : s * x * s⁻¹ = x⁻¹ := hinv x hx
    have h2 : s * x⁻¹ * s⁻¹ = x := by
      have h := congrArg (fun z : G => z⁻¹) h1
      simpa [mul_inv_rev, mul_assoc] using h
    have hconj : (s * s) * x * (s * s)⁻¹ = x := by
      have e1 : (s * s) * x * (s * s)⁻¹ = s * (s * x * s⁻¹) * s⁻¹ := by group
      have e2 : s * (s * x * s⁻¹) * s⁻¹ = s * x⁻¹ * s⁻¹ := by rw [h1]
      exact e1.trans (e2.trans h2)
    have hx1 : (s * s) * x = x * (s * s) := by
      have hx2 := congrArg (fun y => y * (s * s)) hconj
      simpa [mul_assoc] using hx2
    exact hx1.symm
  have hsCnot : s ∉ C := by
    intro hsin
    have hsc : ∀ x ∈ X, x * s = s * x := Subgroup.mem_centralizer_iff.mp hsin
    have hXbot : X ≤ ⊥ := by
      intro x hx
      rw [Subgroup.mem_bot]
      have h1 : s * x * s⁻¹ = x := by rw [← hsc x hx]; group
      have hxeq : x = x⁻¹ := h1.symm.trans (hinv x hx)
      have hsq : x * x = 1 := by
        have h := mul_inv_cancel x
        rwa [← hxeq] at h
      have hd2 : orderOf x ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
      have hdU : orderOf x ∣ Nat.card B.U := by
        have := orderOf_dvd_natCard (⟨x, hXU hx⟩ : ↥B.U)
        rwa [Subgroup.orderOf_mk] at this
      have hodd : ¬ 2 ∣ Nat.card B.U :=
        fun h => (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr h)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1' | h2'
      · exact orderOf_eq_one_iff.mp h1'
      · exact absurd (h2' ▸ hdU) hodd
    exact hX (le_bot_iff.mp hXbot)
  haveI hCn : (C.subgroupOf M).Normal := by
    rw [hC, hM, ← Subgroup.normalizerMonoidHom_ker X]
    infer_instance
  -- `S ∩ C = S₀`
  have hSC : (B.S : Subgroup G) ⊓ C = B.S0 := by
    have hle : B.S0 ≤ (B.S : Subgroup G) ⊓ C := le_inf B.S0_le hS0C
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
    obtain ⟨l, hl⟩ := Subgroup.card_dvd_of_le (inf_le_left : (B.S : Subgroup G) ⊓ C ≤ _)
    have hpos : 0 < Nat.card B.S0 := Nat.card_pos
    have hkl : k * l = 2 := by
      have h : Nat.card B.S0 * (k * l) = 2 * Nat.card B.S0 := by
        rw [← Nat.mul_assoc, ← hk, ← hl, card_S_eq B]
      exact Nat.mul_left_cancel hpos (by rw [h, mul_comm])
    rcases (Nat.dvd_prime Nat.prime_two).mp ⟨l, hkl.symm⟩ with hk1 | hk2
    · refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [hk, hk1, mul_one]
    · exfalso
      have hcard : Nat.card ((B.S : Subgroup G) ⊓ C : Subgroup G) ≥ Nat.card (B.S : Subgroup G) := by
        rw [hk, hk2, card_S_eq B]
        exact le_of_eq (Nat.mul_comm _ _)
      have hSeq : (B.S : Subgroup G) ⊓ C = (B.S : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left hcard
      have hsCin : s ∈ C := by
        have h1 : s ∈ (B.S : Subgroup G) ⊓ C := by rw [hSeq]; exact hsS
        exact h1.2
      exact hsCnot hsCin
  -- the index computation
  have hrel : (B.S : Subgroup G).relIndex C * C.relIndex M =
      2 * (B.S : Subgroup G).relIndex M := by
    have h1 : (B.S : Subgroup G).relIndex C * C.relIndex M =
        ((B.S : Subgroup G) ⊓ C).relIndex M := by
      have h := Subgroup.relIndex_inf_mul_relIndex (B.S : Subgroup G) C M
      rwa [inf_eq_left.mpr hCM] at h
    rw [h1, hSC, ← Subgroup.relIndex_mul_relIndex B.S0 (B.S : Subgroup G) M B.S0_le hSM,
      B.S0_index]
  have hoddS : ¬ 2 ∣ (B.S : Subgroup G).relIndex M := by
    have hnot := (B.S.subtype hSM).not_dvd_index (p := 2)
    simpa [Subgroup.relIndex] using hnot
  have hs2M : 2 ∣ C.relIndex M := by
    have hmem : (QuotientGroup.mk' (C.subgroupOf M)) ⟨s, hsM⟩ ≠ 1 := by
      intro h1
      have hmem' : (⟨s, hsM⟩ : ↥M) ∈ (C.subgroupOf M) := by
        rw [← QuotientGroup.ker_mk' (C.subgroupOf M), MonoidHom.mem_ker]
        exact h1
      exact hsCnot (Subgroup.mem_subgroupOf.mp hmem')
    have hsq : ((QuotientGroup.mk' (C.subgroupOf M)) ⟨s, hsM⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have hmem' : (⟨s, hsM⟩ : ↥M) ^ 2 ∈ (C.subgroupOf M) := by
        rw [Subgroup.mem_subgroupOf]
        simpa [pow_two] using hs2C
      rw [← QuotientGroup.ker_mk' (C.subgroupOf M), MonoidHom.mem_ker] at hmem'
      exact hmem'
    have hord : orderOf ((QuotientGroup.mk' (C.subgroupOf M)) ⟨s, hsM⟩) = 2 := by
      have hd : orderOf ((QuotientGroup.mk' (C.subgroupOf M)) ⟨s, hsM⟩) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; exact hsq
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hmem
      · exact h2
    have hfin := orderOf_dvd_natCard ((QuotientGroup.mk' (C.subgroupOf M)) ⟨s, hsM⟩)
    rw [hord] at hfin
    simpa [Subgroup.relIndex, Subgroup.index] using hfin
  have hS0oddC : ¬ 2 ∣ B.S0.relIndex C := by
    have h1 : (B.S : Subgroup G).relIndex C = B.S0.relIndex C := by
      rw [← Subgroup.inf_relIndex_right (B.S : Subgroup G) C, hSC]
    rw [← h1]
    intro h2dvd
    have h4 : 2 * 2 ∣ (B.S : Subgroup G).relIndex C * C.relIndex M :=
      Nat.mul_dvd_mul h2dvd hs2M
    rw [hrel] at h4
    obtain ⟨k, hk⟩ := h4
    exact hoddS ⟨k, by omega⟩
  have hnot4M : ¬ 4 ∣ C.relIndex M := by
    intro h4
    have h1 : 4 ∣ (B.S : Subgroup G).relIndex C * C.relIndex M :=
      dvd_mul_of_dvd_right h4 _
    rw [hrel] at h1
    obtain ⟨k, hk⟩ := h1
    exact hoddS ⟨k, by omega⟩
  -- `C` is solvable: `S₀` is a cyclic Sylow 2-subgroup of `C`
  have hS0group : IsPGroup 2 ↥(B.S0.subgroupOf C) := by
    rw [IsPGroup.iff_card]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (B.S.isPGroup'.to_le B.S0_le)
    exact ⟨n, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0C).toEquiv, hn]⟩
  have hcycS0C : IsCyclic ↥(B.S0.subgroupOf C) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hS0C)).mpr B.S0_cyclic
  have hsolC : Group.IsSolvable ↥C :=
    solvable_of_cyclic_sylow_two hFT (hS0group.toSylow hS0oddC) hcycS0C
  -- `M/C` is solvable: its order is `2 * odd`
  have hcardQ : Nat.card (↥M ⧸ (C.subgroupOf M)) = 2 * (C.relIndex M / 2) := by
    have h1 : Nat.card (↥M ⧸ (C.subgroupOf M)) = C.relIndex M := by
      rw [← Subgroup.index_eq_card (C.subgroupOf M)]
      rfl
    obtain ⟨k, hk⟩ := hs2M
    rw [h1, hk, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  have hoddQ : Odd (C.relIndex M / 2) := by
    obtain ⟨k, hk⟩ := hs2M
    have hkodd : ¬ 2 ∣ k := by
      intro h2
      obtain ⟨l, hl⟩ := h2
      exact hnot4M ⟨l, by omega⟩
    have hdiv : C.relIndex M / 2 = k := by
      rw [hk, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    rw [hdiv]
    exact Nat.not_even_iff_odd.mp (fun he => hkodd (even_iff_two_dvd.mp he))
  have hsolQ : Group.IsSolvable (↥M ⧸ (C.subgroupOf M)) :=
    solvable_of_card_two_mul_odd hFT (C.relIndex M / 2) hcardQ hoddQ
  haveI : Group.IsSolvable (↥M ⧸ (C.subgroupOf M)) := hsolQ
  haveI : Group.IsSolvable ↥(C.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hCM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hCM).injective
  exact Group.isSolvable_of_subgroup_quotient (C.subgroupOf M)

/-! ## 4. The leaf -/

/-- **Bender 1981, Lemma 2.8, first assertion**, with Theorem 2.6 available: if `I_U(s) ⊴ U` for
every `s ∈ S − S₀`, then `[S₀,U] ≠ 1`. -/
theorem L28_S0U_ne_bot_h26_proved : Work.CORE2B.L28_S0U_ne_bot_h26 := by
  intro T h22 h26 h27 G _ _ hFT hCtx B hinv hbot
  have ha : B.S0 ≤ Subgroup.centralizer (B.U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  obtain ⟨hUeq, hCS, hdisj⟩ := h26 G hFT hCtx B
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * Nat.card B.S0 := card_S_eq B
  -- `Γ := S ⊓ C(U) = O₂(Ĥ)` is `S₀` or `S`
  have hcases : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) = B.S0 ∨
      (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) = (B.S : Subgroup G) := by
    have hS0Γ : B.S0 ≤ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) :=
      le_inf B.S0_le ha
    have hΓS : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) ≤ (B.S : Subgroup G) :=
      inf_le_left
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hS0Γ
    obtain ⟨l, hl⟩ := Subgroup.card_dvd_of_le hΓS
    have hpos : 0 < Nat.card B.S0 := Nat.card_pos
    have hkl : k * l = 2 := by
      have h : Nat.card B.S0 * (k * l) = 2 * Nat.card B.S0 := by
        rw [← Nat.mul_assoc, ← hk, ← hl, hcardS]
      exact Nat.mul_left_cancel hpos (by rw [h, mul_comm])
    rcases (Nat.dvd_prime Nat.prime_two).mp ⟨l, hkl.symm⟩ with hk1 | hk2
    · left
      refine (Subgroup.eq_of_le_of_card_ge hS0Γ ?_).symm
      rw [hk, hk1, mul_one]
    · right
      refine Subgroup.eq_of_le_of_card_ge hΓS ?_
      rw [hk, hk2, hcardS]
      exact le_of_eq (Nat.mul_comm _ _)
  rcases hcases with hΓS0 | hΓS
  · -- Case `Γ = S₀`: `Ĥ = H`
    have hO2 : Work.GW2.pCoreIn 2 B.Hhat = B.S0 := by rw [← hCS, hΓS0]
    have hHhat : B.Hhat = B.H := by
      rcases hdisj with h | h
      · exact h.2
      · exact absurd (hO2 ▸ h.1) (not_isFourGroup_of_isCyclic B.S0_cyclic)
    obtain ⟨s, hsS, hs0⟩ := exists_notMem_S0 B
    obtain ⟨I, hIset, hInorm⟩ := hinv.inv_normal s hsS hs0
    have hmem : ∀ x : G, x ∈ I → x ∈ Work.GW2.invSet B.U s := fun x hx => by
      rw [← hIset]; exact hx
    have hIU : I ≤ B.U := fun x hx => (hmem x hx).1
    -- clause (c) of the configuration of Lemma 2.2 must fail
    have hnotc : ¬ (∀ X : Subgroup G, X ≠ ⊥ → X ≤ I →
        Subgroup.normalizer (X : Set G) ≤ B.H) := by
      intro hc
      exact h22 G hFT hCtx B ⟨ha, s, hsS, hs0, I, hIset, hInorm, hc⟩
    obtain ⟨X, hXne, hXle, hXnor⟩ : ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ I ∧
        ¬ Subgroup.normalizer (X : Set G) ≤ B.H := by
      push_neg at hnotc
      exact hnotc
    have hXinv : X ≤ Work.GW2.invSet B.U s := fun x hx => hmem x (hXle hx)
    have hXU : X ≤ B.U := fun x hx => (hXinv hx).1
    have hsinvX : ∀ x ∈ X, s * x * s⁻¹ = x⁻¹ := fun x hx => (hXinv hx).2
    -- `s` normalizes `X`
    have hsX : s ∈ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx; rw [hsinvX x hx]; exact X.inv_mem hx
      · intro hx
        have h2 : s * (s * x * s⁻¹) * s⁻¹ = (s * x * s⁻¹)⁻¹ := hsinvX _ hx
        have h3 : s * x * s⁻¹ = x⁻¹ := by
          have key : s⁻¹ * (s * (s * x * s⁻¹) * s⁻¹) * s =
              s⁻¹ * (s * x * s⁻¹)⁻¹ * s := by rw [h2]
          simpa [mul_assoc] using key
        rw [h3] at hx
        simpa using X.inv_mem hx
    -- `S₀` centralizes `X`
    have hfix : ∀ c ∈ B.S0, ∀ x ∈ X, c * x * c⁻¹ = x := by
      intro c hc x hx
      have hcx := Subgroup.mem_centralizer_iff.mp (ha hc) x (hXU hx)
      rw [← hcx]; group
    have hS0X : B.S0 ≤ Subgroup.normalizer (X : Set G) := fun c hc => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => by rw [hfix c hc x hx]; exact hx, fun hx => ?_⟩
      have hy := hfix c hc (c * x * c⁻¹) hx
      have hcx : c * x * c⁻¹ = x := by
        have key : c⁻¹ * (c * (c * x * c⁻¹) * c⁻¹) * c = c⁻¹ * (c * x * c⁻¹) * c := by
          rw [hy]
        simpa [mul_assoc] using key
      rw [← hcx]
      exact hx
    have hSM : (B.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
      rw [← S_eq_sup_zpowers B hsS hs0]
      exact sup_le hS0X (Subgroup.zpowers_le.mpr hsX)
    -- `M := N_G(X)` is proper
    have hMne : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
      haveI hsimple : IsSimpleGroup G := hCtx.simple
      intro htop
      have hXnorm : X.Normal := ⟨fun n hn g => by
        have hg : g ∈ Subgroup.normalizer (X : Set G) := by rw [htop]; trivial
        rw [Subgroup.mem_normalizer_iff] at hg
        exact (hg n).mp hn⟩
      have hXtop : X = ⊤ := by
        rcases hXnorm.eq_bot_or_eq_top with h | h
        · exact absurd h hXne
        · exact h
      have hle : X ≤ B.Hhat :=
        hXU.trans (Work.CORE2B.BenderSetup_basics B).2.2.2.2.1
      exact (Work.CORE2B.BenderSetup_basics B).2.2.2.2.2.1 (le_antisymm le_top (hXtop ▸ hle))
    have hMnotle : ¬ Subgroup.normalizer (X : Set G) ≤ B.Hhat := by rw [hHhat]; exact hXnor
    -- `X ≤ F(Ĥ)`
    have hs2 : orderOf s = 2 := S_diff_S0_order_two hCtx B s hsS hs0
    have hsNU : s ∈ Subgroup.normalizer (B.U : Set G) :=
      (S_le_H B).trans (H_le_normalizer_U B) hsS
    obtain ⟨-, -, hkey⟩ := T.c15 G hFT B.U s hs2 (oddCoreIn_odd B.H) hsNU
    have hIab : IsMulCommutative I := (hkey I hIset).1
    have hsinvI : ∀ y ∈ I, s * y * s⁻¹ = y⁻¹ := fun y hy =>
      (hIset ▸ hy : y ∈ Work.GW2.invSet B.U s).2
    have hs1sq : s * s = 1 := by
      have h : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
      simpa [pow_two] using h
    have hUleNI : B.U ≤ Subgroup.normalizer (I : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro u hu x hx
      have hx' : (⟨x, hIU hx⟩ : ↥B.U) ∈ I.subgroupOf B.U := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      have h := hInorm.conj_mem (⟨x, hIU hx⟩ : ↥B.U) hx' (⟨u, hu⟩ : ↥B.U)
      rw [Subgroup.mem_subgroupOf] at h
      exact h
    have hSleNI : (B.S : Subgroup G) ≤ Subgroup.normalizer (I : Set G) := by
      rw [← S_eq_sup_zpowers B hsS hs0]
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.le_normalizer_iff]
        intro c hc x hx
        have : c * x * c⁻¹ = x := by
          have hcx := Subgroup.mem_centralizer_iff.mp (ha hc) x (hIU hx)
          rw [← hcx]; group
        rw [this]; exact hx
      · rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          rw [hsinvI x hx]; exact I.inv_mem hx
        · intro hx
          have hmem : s * (s * x * s⁻¹) * s⁻¹ ∈ I := by
            rw [hsinvI _ hx]; exact I.inv_mem hx
          have hcancel : s * (s * x * s⁻¹) * s⁻¹ = x := by
            have h1 : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs1sq, inv_one]
            calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
              _ = 1 * x * 1 := by rw [hs1sq, h1]
              _ = x := by group
          rwa [hcancel] at hmem
    have hSplit : B.U ⊔ (B.S : Subgroup G) = B.H := by
      obtain ⟨n, hn2, hdih⟩ := S_dihedral hCtx B
      exact T.split G B.S n hn2 hdih B.t (B.S0_le B.t_mem) B.t_order (t_central_in_S B)
    have hHhatNI : B.Hhat ≤ Subgroup.normalizer (I : Set G) := by
      rw [hHhat, ← hSplit]
      exact sup_le hUleNI hSleNI
    have hIfit : I ≤ Work.GW2.fittingIn B.Hhat :=
      le_fittingIn_of_abelian_normal (hIU.trans (Work.CORE2B.BenderSetup_basics B).2.2.2.2.1)
        hHhatNI hIab
    have hXfit : X ≤ Work.GW2.fittingIn B.Hhat := hXle.trans hIfit
    have hBRel : Work.GW2.BRel B.Hhat (Subgroup.normalizer (X : Set G)) :=
      ⟨X, hXfit, inf_le_left⟩
    -- `t ∈ E(N_G(X))` by Lemma 2.8 (second assertion) ...
    have hlayer : B.t ∈ Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) :=
      L28_t_mem_layer_proved T h22 h27 G hFT hCtx B hinv _
        ⟨hMne, hBRel, hMnotle, hSM⟩
    -- ... but `N_G(X)` is solvable
    have hsol : Group.IsSolvable ↥(Subgroup.normalizer (X : Set G)) :=
      normalizer_solvable hFT B (oddCoreIn_odd B.H) ha s hsS hs0 X hXne hXinv
    have hbotlayer : Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) = ⊥ :=
      layerIn_eq_bot_of_isSolvable _ hsol
    have ht1 : B.t = 1 := by
      have : B.t ∈ (⊥ : Subgroup G) := by rw [← hbotlayer]; exact hlayer
      simpa using this
    exact absurd ht1 (by
      intro h
      have := B.t_order
      rw [h, orderOf_one] at this
      omega)
  · -- Case `Γ = S`: `S ≤ C(U)`, so `I_U(s) = 1` for `s ∈ S − S₀`
    obtain ⟨s, hsS, hs0⟩ := exists_notMem_S0 B
    have hsC : s ∈ Subgroup.centralizer (B.U : Set G) := by
      have hle : (B.S : Subgroup G) ≤ Subgroup.centralizer (B.U : Set G) := by
        rw [← hΓS]; exact inf_le_right
      exact hle hsS
    have hIset : ((⊥ : Subgroup G) : Set G) = Work.GW2.invSet B.U s := by
      ext x
      constructor
      · intro hx
        have hx1 : x = 1 := by simpa using hx
        rw [hx1]
        exact Work.CORE2B.one_mem_invSet B.U s
      · intro hx
        obtain ⟨hxU, hxc⟩ := hx
        have hxc' : s * x * s⁻¹ = x := by
          have := (Subgroup.mem_centralizer_iff.mp hsC) x hxU
          rw [← this]; group
        have hxeq : x = x⁻¹ := hxc'.symm.trans hxc
        have hsq : x * x = 1 := by
          have h := mul_inv_cancel x
          rwa [← hxeq] at h
        have hd2 : orderOf x ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
        have hdU : orderOf x ∣ Nat.card B.U := by
          have := orderOf_dvd_natCard (⟨x, hxU⟩ : ↥B.U)
          rwa [Subgroup.orderOf_mk] at this
        have hodd : ¬ 2 ∣ Nat.card B.U :=
          fun h => (Nat.not_even_iff_odd.mpr (oddCoreIn_odd B.H)) (even_iff_two_dvd.mpr h)
        rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
        · show x ∈ (⊥ : Subgroup G)
          rw [Subgroup.mem_bot]
          exact orderOf_eq_one_iff.mp h1
        · exact absurd (h2 ▸ hdU) hodd
    refine h22 G hFT hCtx B ⟨ha, s, hsS, hs0, ⊥, hIset, ?_, ?_⟩
    · have hbot : (⊥ : Subgroup G).subgroupOf B.U = ⊥ :=
        (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
          Subtype.ext (Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp hx))
      rw [hbot]
      infer_instance
    · intro X hXne hXle
      exact absurd (le_bot_iff.mp hXle) hXne

end Work.CORE2B
