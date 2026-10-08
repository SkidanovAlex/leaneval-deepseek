import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.Dihedral.Defs
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

/-!
# AREA CORE2B — the leaf `Work.CORE2B.L28_t_mem_layer` (Bender 1981, Lemma 2.8, p. 221)

Bender's Lemma 2.8 says: if `I_U(s) ⊴ U` for every `s ∈ S − S₀`, then `[S₀,U] ≠ 1` and `t ∈ E(M)`
whenever `Ĥ ⇝ M` with `M ≠ Ĥ` and `S ≤ M`.  This file proves the second assertion.

**Mathematics.**

1. `t` is the central involution of `S`: `S₀ ≤ S` has index `2`, hence is normal in `S`, so for
   `x ∈ S` the conjugate `x t x⁻¹` is another involution of the cyclic group `S₀`, and a finite
   cyclic group has a unique involution.  Hence `S ≤ C(t) = H`.

2. Since `U = O(H) ◁ H`, we get `S ≤ N_G(U)`.

3. Every `s ∈ S − S₀` is an involution (an element outside the cyclic index-two subgroup of a
   dihedral group is a reflection).  For such an `s`, `I := I_U(s) = invSet U s` is given normal in
   `U`, and Bender 1.5(iii) gives `I ≤ F(U)`.  Moreover `[s,u] ∈ I` for every `u ∈ U`, since
   `[s,u] = u · (u⁻¹ s u s⁻¹) · u⁻¹` and `u⁻¹ s u s⁻¹ ∈ I_U(s)` because `s² = 1`.

4. Every `g ∈ S₀` is a product `s₀ · (s₀ g)` of two elements of `S − S₀`, whence (using
   `[ab,u] = a·[b,u]·a⁻¹·[a,u]` and `[b,u]^a = [b^a, u^a]`) every `[g,u]` is a product of
   commutators of type (3).  Therefore `[S,U] ≤ F(U)` by `Subgroup.commutator_le`.

5. `[S,U] ≤ F(U)` contradicts the second conclusion of Bender's Lemma 2.7 (`h27`): with `S ≤ M`
   the subgroup `S` is a Sylow 2-subgroup of `M`, so every Sylow 2-subgroup of `M` is non-cyclic
   (`BenderCtx_sylow_not_cyclic`), and the size hypothesis of `L27Hyp` holds because
   `4 ∣ |S| = |S ⊓ M|`.  Hence `t ∉ E(M)` is impossible.

-/

open scoped MatrixGroups commutatorElement

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-!
## 0. Ports of two standard facts

The area `CORE2B` carries its own copy of the `Work.GW2` vocabulary (`CORE2B/Defs.lean`), so the
versions of these facts proved in the sibling areas `CORE2A` / `COPR` cannot be imported.  They are
reproved here (`private`, so that no clash arises with the sibling modules).
-/

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
cyclic of index `2`.  (This is the "elements outside the rotation subgroup are reflections" fact.) -/
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

/-- **Bender 1981, 1.5(iii).**  If an involution `s` acts on the odd-order group `X` and
`I := I_X(s) = invSet X s` is a subgroup, then `I` is abelian, normal in `X`, and lies in `F(X)`
(stated as `Work.GW2.fittingIn X` in the ambient group). -/
private theorem coprime15_sub {G : Type} [Group G] [Finite G] (X : Subgroup G) (s : G)
    (hs : orderOf s = 2) (hodd : Odd (Nat.card X))
    (hN : s ∈ Subgroup.normalizer (X : Set G)) :
    ∀ I : Subgroup G, (I : Set G) = Work.GW2.invSet X s →
      IsMulCommutative I ∧ (I.subgroupOf X).Normal ∧ I ≤ Work.GW2.fittingIn X := by
  intro I hI
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs] at h
    simpa [pow_two] using h
  let c : MulAut G := MulAut.conj s
  have hc : ∀ y : G, c y = s * y * s⁻¹ := fun y => MulAut.conj_apply s y
  have hcc : c * c = 1 := by
    have h : MulAut.conj (s * s) = MulAut.conj s * MulAut.conj s :=
      map_mul (MulAut.conj : G →* MulAut G) s s
    rw [hs2, map_one (MulAut.conj : G →* MulAut G)] at h
    exact h.symm
  have hc2 : ∀ y : G, c (c y) = y := by
    intro y
    rw [← MulAut.mul_apply, hcc]
    rfl
  have hnorm : ∀ x : G, x ∈ X → s * x * s⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  have hmem : ∀ x : G, x ∈ I → x ∈ X ∧ s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have hx' : x ∈ Work.GW2.invSet X s := by rw [← hI]; exact hx
    exact hx'
  have hIX : I ≤ X := fun x hx => (hmem x hx).1
  have hinv : ∀ x ∈ I, c x = x⁻¹ := fun x hx => (hc x).trans (hmem x hx).2
  have hcomm : IsMulCommutative I := isMulCommutative_iff.mpr (fun (x : I) (y : I) => by
    have hx := hinv x x.2
    have hy := hinv y y.2
    have hxy := hinv (x * y) (I.mul_mem x.2 y.2)
    have key : (x : G)⁻¹ * (y : G)⁻¹ = (y : G)⁻¹ * (x : G)⁻¹ := by
      calc (x : G)⁻¹ * (y : G)⁻¹
          = c (x : G) * c (y : G) := by rw [hx, hy]
        _ = c ((x : G) * (y : G)) := (map_mul c _ _).symm
        _ = ((x : G) * (y : G))⁻¹ := hxy
        _ = (y : G)⁻¹ * (x : G)⁻¹ := by rw [mul_inv_rev]
    have keyG : (x : G) * (y : G) = (y : G) * (x : G) := by
      have := congrArg (fun t : G => t⁻¹) key
      simpa [mul_inv_rev, inv_inv] using this.symm
    exact Subtype.ext keyG
  )
  have hcommG : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a := fun a ha b hb => by
    have h := (hcomm.is_comm).comm (⟨a, ha⟩ : I) (⟨b, hb⟩ : I)
    simpa using h
  have hd : ∀ b : G, b ∈ X → b⁻¹ * c b ∈ I := by
    intro b hb
    have hbX : b⁻¹ * c b ∈ X := by
      rw [hc b]; exact X.mul_mem (X.inv_mem hb) (hnorm b hb)
    have heq : c (b⁻¹ * c b) = (b⁻¹ * c b)⁻¹ := by
      rw [map_mul, map_inv, hc2 b, mul_inv_rev, inv_inv]
    have hthis : b⁻¹ * c b ∈ Work.GW2.invSet X s :=
      ⟨hbX, (hc (b⁻¹ * c b)).symm.trans heq⟩
    rw [← hI] at hthis
    exact hthis
  have hnormI : (I.subgroupOf X).Normal := ⟨fun n hn g => by
    have ha : (n : G) ∈ I := Subgroup.mem_subgroupOf.mp hn
    have hb : (g : G) ∈ X := g.2
    rw [Subgroup.mem_subgroupOf]
    show ((g : G) * (n : G) * (g : G)⁻¹) ∈ I
    have hu : (g : G)⁻¹ * c (g : G) ∈ I := hd (g : G) hb
    have hua : ((g : G)⁻¹ * c (g : G)) * (n : G)⁻¹ * ((g : G)⁻¹ * c (g : G))⁻¹
        = (n : G)⁻¹ := by
      have h := hcommG _ hu _ (I.inv_mem ha)
      rw [h]; group
    have hmain : c ((g : G) * (n : G) * (g : G)⁻¹)
        = ((g : G) * (n : G) * (g : G)⁻¹)⁻¹ := by
      have step1 : c ((g : G) * (n : G) * (g : G)⁻¹)
          = c (g : G) * c (n : G) * (c (g : G))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      have step2 : c (g : G) * c (n : G) * (c (g : G))⁻¹
          = ((g : G) * ((g : G)⁻¹ * c (g : G))) * (n : G)⁻¹
              * ((g : G) * ((g : G)⁻¹ * c (g : G)))⁻¹ := by
        rw [show (g : G) * ((g : G)⁻¹ * c (g : G)) = c (g : G) from by group]
        rw [hinv (n : G) ha]
      have step3 : ((g : G) * ((g : G)⁻¹ * c (g : G))) * (n : G)⁻¹
              * ((g : G) * ((g : G)⁻¹ * c (g : G)))⁻¹
          = (g : G) * (n : G)⁻¹ * (g : G)⁻¹ := by
        rw [show (g : G) * ((g : G)⁻¹ * c (g : G)) * (n : G)⁻¹
                  * ((g : G) * ((g : G)⁻¹ * c (g : G)))⁻¹
                = (g : G) * (((g : G)⁻¹ * c (g : G)) * (n : G)⁻¹
                  * ((g : G)⁻¹ * c (g : G))⁻¹) * (g : G)⁻¹ from by group]
        rw [hua]
      have step4 : (g : G) * (n : G)⁻¹ * (g : G)⁻¹
          = ((g : G) * (n : G) * (g : G)⁻¹)⁻¹ := by group
      exact step1.trans (step2.trans (step3.trans step4))
    have hthis : ((g : G) * (n : G) * (g : G)⁻¹) ∈ Work.GW2.invSet X s :=
      ⟨X.mul_mem (X.mul_mem hb (hIX ha)) (X.inv_mem hb),
        (hc ((g : G) * (n : G) * (g : G)⁻¹)).symm.trans hmain⟩
    rw [← hI] at hthis
    exact hthis
  ⟩
  refine ⟨hcomm, hnormI, ?_⟩
  have hnilpI : Group.IsNilpotent ↥I := CommGroup.isNilpotent
  have hnilpK : Group.IsNilpotent ↥(I.subgroupOf X) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hIX)).mpr hnilpI
  have hKle : I.subgroupOf X ≤ Work.GW2.fitting ↥X := by
    rw [Work.GW2.fitting]
    haveI : (I.subgroupOf X).Normal := hnormI
    rw [Subgroup.normal_le_normalCore]
    exact le_sSup ⟨hnormI, hnilpK⟩
  have hmap : (I.subgroupOf X).map X.subtype = I := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact hIX
  rw [Work.GW2.fittingIn, ← hmap]
  exact Subgroup.map_mono hKle

end Ports

/-!
## 1. Elementary consequences of the `BenderSetup` fields
-/

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

/-- `4 ∣ |S|`. -/
private theorem four_dvd_card_S {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    4 ∣ Nat.card (B.S : Subgroup G) := by
  rw [card_S_eq B]
  have h2 : 2 ∣ Nat.card B.S0 := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr B.t_mem)
    rwa [Nat.card_zpowers, B.t_order] at h
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, by rw [hk]; ring⟩

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

/-!
## 2. `[S, U] ≤ F(U)` from the hypothesis `I_U(s) ⊴ U`
-/

/-- **The key step.**  If `I_U(s) ⊴ U` for every `s ∈ S − S₀`, then `[S,U] ≤ F(U)`. -/
private theorem su_le_fittingIn_of_L28Hyp {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (hinv : L28Hyp B) :
    ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U := by
  have hSH : (B.S : Subgroup G) ≤ B.H := S_le_H B
  have hHN : B.H ≤ Subgroup.normalizer (B.U : Set G) := H_le_normalizer_U B
  have hSN : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := hSH.trans hHN
  have hoddU : Odd (Nat.card B.U) := oddCoreIn_odd B.H
  have hord : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → orderOf s = 2 := S_diff_S0_order_two hCtx B
  have key : ∀ φ ∈ (B.S : Subgroup G), φ ∉ B.S0 →
      ∀ u ∈ B.U, ⁅φ, u⁆ ∈ Work.GW2.fittingIn B.U := by
    intro φ hφS hφ0 u hu
    obtain ⟨I, hIeq, hInorm⟩ := hinv.inv_normal φ hφS hφ0
    have hIle : I ≤ Work.GW2.fittingIn B.U :=
      (coprime15_sub B.U φ (hord φ hφS hφ0) hoddU (hSN hφS) I hIeq).2.2
    have hI : I ≤ B.U := fun x hx => (hIeq ▸ hx : x ∈ Work.GW2.invSet B.U φ).1
    have hφ2 : φ * φ = 1 := by
      have h := hord φ hφS hφ0
      rw [orderOf_eq_iff (by norm_num : 0 < 2)] at h
      simpa [pow_two] using h.1
    have hmem : u⁻¹ * (φ * u * φ⁻¹) ∈ I := by
      have hs : u⁻¹ * (φ * u * φ⁻¹) ∈ (I : Set G) := by
        rw [hIeq, Work.GW2.invSet]
        refine ⟨?_, ?_⟩
        · exact B.U.mul_mem (B.U.inv_mem hu)
            ((Subgroup.mem_normalizer_iff.mp (hSN hφS) u).mp hu)
        · show φ * (u⁻¹ * (φ * u * φ⁻¹)) * φ⁻¹ = (u⁻¹ * (φ * u * φ⁻¹))⁻¹
          have hφinv : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφ2
          have e1 : (u⁻¹ * (φ * u * φ⁻¹))⁻¹ = φ * u⁻¹ * φ * u := by
            rw [show (u⁻¹ * (φ * u * φ⁻¹))⁻¹ = φ * u⁻¹ * φ⁻¹ * u from by group, hφinv]
          rw [e1, hφinv]
          have e2 : φ * (u⁻¹ * (φ * u * φ)) * φ = φ * u⁻¹ * φ * u * (φ * φ) := by group
          rw [e2, hφ2, mul_one]
      exact hs
    have hconj : u * (u⁻¹ * (φ * u * φ⁻¹)) * u⁻¹ ∈ I :=
      (Subgroup.normal_subgroupOf_iff hI).mp hInorm (u⁻¹ * (φ * u * φ⁻¹)) u hmem hu
    refine hIle ?_
    convert hconj using 1
    rw [commutatorElement_def]
    group
  obtain ⟨s0, hs0S, hs00⟩ := exists_notMem_S0 B
  have hs02 : s0 * s0 = 1 := by
    have h := hord s0 hs0S hs00
    rw [orderOf_eq_iff (by norm_num : 0 < 2)] at h
    simpa [pow_two] using h.1
  rw [Subgroup.commutator_le]
  intro g hg u hu
  by_cases hg0 : g ∈ B.S0
  · have hyS : s0 * g ∈ (B.S : Subgroup G) := (B.S).mul_mem hs0S hg
    have hy0 : s0 * g ∉ B.S0 := by
      intro h
      apply hs00
      have h' : s0 = (s0 * g) * g⁻¹ := by group
      rw [h']
      exact B.S0.mul_mem h (B.S0.inv_mem hg0)
    have h1 : ⁅s0, u⁆ ∈ Work.GW2.fittingIn B.U := key s0 hs0S hs00 u hu
    have hgs0S : g * s0 ∈ (B.S : Subgroup G) := (B.S).mul_mem hg hs0S
    have hgs00 : g * s0 ∉ B.S0 := by
      intro h
      apply hs00
      have h' : s0 = g⁻¹ * (g * s0) := by group
      rw [h']
      exact B.S0.mul_mem (B.S0.inv_mem hg0) h
    have h2 : s0 * ⁅s0 * g, u⁆ * s0⁻¹ ∈ Work.GW2.fittingIn B.U := by
      have hbase : ⁅g * s0, s0 * u * s0⁻¹⁆ ∈ Work.GW2.fittingIn B.U :=
        key (g * s0) hgs0S hgs00 (s0 * u * s0⁻¹)
          ((Subgroup.mem_normalizer_iff.mp (hSN hs0S) u).mp hu)
      have heq : s0 * (s0 * g) * s0⁻¹ = g * s0 := by
        rw [← mul_assoc s0 s0 g, hs02, one_mul, inv_eq_of_mul_eq_one_right hs02]
      rw [conjugate_commutatorElement (s0 * g) u s0, heq]
      exact hbase
    have hdecomp : ⁅g, u⁆ = s0 * ⁅s0 * g, u⁆ * s0⁻¹ * ⁅s0, u⁆ := by
      have hg : g = s0 * (s0 * g) := by rw [← mul_assoc, hs02, one_mul]
      conv_lhs => rw [hg]
      exact commutatorElement_mul_left_eq_conj_mul s0 (s0 * g) u
    rw [hdecomp]
    exact (Work.GW2.fittingIn B.U).mul_mem h2 h1
  · exact key g hg hg0 u hu

/-!
## 3. The Sylow 2-subgroups of `M` are non-cyclic, and the size hypothesis
-/

/-- Every Sylow 2-subgroup of `M` is non-cyclic, when `S ≤ M`. -/
private theorem sylow_two_M_not_cyclic {G : Type} [Group G] [Finite G] (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hSM : (B.S : Subgroup G) ≤ M) :
    ∀ P : Sylow 2 M, ¬ IsCyclic P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) := Work.CORE2B.BenderCtx_sylow_not_cyclic hCtx B.S
  intro P hP
  let S' : Sylow 2 M := B.S.subtype hSM
  have hS' : (S' : Subgroup M) = (B.S : Subgroup G).subgroupOf M :=
    Sylow.coe_subtype B.S hSM
  have h1 : IsCyclic ↥(S' : Subgroup M) := (MulEquiv.isCyclic (Sylow.equiv P S')).mp hP
  rw [hS'] at h1
  exact hnc ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hSM)).mp h1)

/-- The size hypothesis of `L27Hyp`, when `S ≤ M`. -/
private theorem size_hyp_of_S_le_M {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hSM : (B.S : Subgroup G) ≤ M) :
    8 ≤ Nat.card ((B.S : Subgroup G) ⊓ M : Subgroup G) ∨ Nat.card (B.S : Subgroup G) = 4 ∨
      B.t ∈ Work.GW2.twoResidualIn M := by
  have hcard : Nat.card ((B.S : Subgroup G) ⊓ M : Subgroup G) = Nat.card (B.S : Subgroup G) := by
    rw [inf_eq_left.mpr hSM]
  obtain ⟨k, hk⟩ := four_dvd_card_S B
  have hpos : 0 < Nat.card (B.S : Subgroup G) := Nat.card_pos
  have harith : Nat.card (B.S : Subgroup G) = 4 ∨ 8 ≤ Nat.card (B.S : Subgroup G) := by
    omega
  rcases harith with h4 | h8
  · right; left; exact h4
  · left; rw [hcard]; exact h8

/-!
## 4. The leaf
-/

theorem L28_t_mem_layer_proved : Work.CORE2B.L28_t_mem_layer := by
  intro T h22 h27 G _ _ hFT hCtx B hinv M hM
  by_contra htnot
  have hSM : (B.S : Subgroup G) ≤ M := hM.S_le_M
  have htM : B.t ∈ M := hSM (B.S0_le B.t_mem)
  have hres := h27 G hFT hCtx B M hM.M_ne_top hM.rel hM.not_le htM htnot
    (sylow_two_M_not_cyclic hCtx B M hSM) (size_hyp_of_S_le_M B M hSM)
  exact hres.2.1 (su_le_fittingIn_of_L28Hyp hCtx B hinv)

end Work.CORE2B
