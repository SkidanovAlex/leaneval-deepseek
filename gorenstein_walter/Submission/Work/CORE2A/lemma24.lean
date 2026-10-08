/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.fstar_eq_pCore_of_isPGroup
import Submission.Work.CORE2A.fstar_ne_bot
import Submission.Work.CORE2A.ZJ_ne_bot
import Submission.Work.CORE2A.map_ZJ_subtype
import Submission.Work.CORE2A.ZJ_conj
import Submission.Work.CORE2A.normalizer_le_normalizer_ZJ
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.CORE2A.map_sylow_isSylow

/-!
# CORE2A: Bender's Lemma 2.4

This file proves `Work.CORE2A.lemma24`: Bender 1981, Lemma 2.4 (p. 220), the last ingredient
of the `Ĥ ⇒ M` step of Bender's maximal-subgroup method.

**Statement.** Let `G` be a minimal counterexample (`BenderCtx G`), `B` a Bender setup with
maximal subgroup `Ĥ = B.Hhat`, `M` a maximal subgroup with `Ĥ ⇝ M` (`BRel`), and `p ≠ 2` a prime
such that `F*(Ĥ)` and `F*(M)` are `p`-groups. Then `Ĥ = M`.

**Proof** (following the paper, with the bookkeeping made explicit).

* `Ĥ` and `M` are proper subgroups, hence (by the minimal-counterexample hypothesis `ih`)
  D-groups with dihedral/cyclic Sylow 2-subgroups.  `D16Prop` (Bender 1.6) shows that a
  nontrivial D-group has `F*(X) ≠ 1`, and `fstar_eq_pCore_of_isPGroup` shows that when `F*(X)`
  is a `p`-group it *is* `O_p(X)`.  Consequently the hypothesis of Glauberman's `Z(J)`-theorem
  (`ZJAProp`) — `C(O_p(X)) ≤ O_p(X)` — holds for `X = Ĥ` and `X = M`, by `FStarProp` (`T.fstar`).
* Applying `ZJAProp` to `Ĥ` with `P ∈ Syl_p(Ĥ)` gives `Z(J(P)) ⊴ Ĥ`; as `Z(J(P)) ≠ 1` and `Ĥ` is
  maximal, `N_G(Z(J(P))) = Ĥ`.  The same holds for `M`.
* Since `Z(J(P))` is fixed by `N_G(P)` (`N_G(P) ≤ N_G(Z(J(P)))`), the maximality argument gives
  `N_G(P) ≤ Ĥ`, which forces `P` itself to be a Sylow `p`-subgroup of `G` (normalizer condition
  in the Sylow subgroup of `G` containing it).  Hence the two Sylow subgroups are conjugate, and
  so are `Ĥ` and `M`: `M = Ĥ^γ`.
* Let `W = Z(O_p(Ĥ))`; it is a nontrivial normal subgroup of `Ĥ`, so `N_G(W) = Ĥ`, and it
  centralizes `F(Ĥ) = O_p(Ĥ)`, so `W ≤ M` by `BRel`.  Also `W ≤ P` for every Sylow of `Ĥ`.
  Replacing `γ` by `m γ` for a suitable `m ∈ M` (making `W^{γ⁻¹} ⊆ P`) we may assume
  `W^γ ⊆ P`, so Theorem B (`ZJBProp`) applies to `W` and `γ⁻¹`: `γ⁻¹ = c·n` with
  `c ∈ C_G(W) ⊆ N_G(W) = Ĥ` and `n ∈ N_G(Z(J(P))) = Ĥ`.  Hence `γ ∈ Ĥ` and `M = Ĥ^γ = Ĥ`.
-/

open scoped MatrixGroups Pointwise

namespace Work.CORE2A

open Subgroup

/-! ## Auxiliary lemmas -/

/-- A proper subgroup of a finite group has smaller cardinality. -/
theorem natCard_lt_of_lt_top {G : Type*} [Group G] [Finite G] {H : Subgroup G} (h : H < ⊤) :
    Nat.card ↥H < Nat.card G := by
  have hidx : 1 < H.index := Subgroup.one_lt_index_of_ne_top (ne_of_lt h)
  have hcm := Subgroup.card_mul_index H
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  rw [← hcm]
  nlinarith

/-- Conjugation commutes with taking centralizers. -/
theorem conjSub_centralizer {G : Type*} [Group G] (g : G) (A : Subgroup G) :
    Work.GW2.conjSub g (Subgroup.centralizer (A : Set G)) =
      Subgroup.centralizer (Work.GW2.conjSub g A : Set G) := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h y hy
    change y ∈ Work.GW2.conjSub g A at hy
    rw [mem_conjSub_iff] at hy
    have h1 : (g⁻¹ * y * g) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * (g⁻¹ * y * g) :=
      Subgroup.mem_centralizer_iff.mp h _ hy
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = x * y := by group
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hy : g * w * g⁻¹ ∈ Work.GW2.conjSub g A := by
      rw [mem_conjSub_iff]
      have hc : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rwa [hc]
    have h1 : (g * w * g⁻¹) * x = x * (g * w * g⁻¹) := h _ hy
    calc w * (g⁻¹ * x * g) = g⁻¹ * ((g * w * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * w * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * x * g) * w := by group

/-- The normalizer of a subgroup conjugated by `g`. -/
theorem normalizer_conjSub {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    Subgroup.normalizer (Work.GW2.conjSub g K : Set G) =
      Work.GW2.conjSub g (Subgroup.normalizer (K : Set G)) := by
  rw [conjSub_eq_map, conjSub_eq_map]
  exact (Subgroup.map_normalizer_eq_of_bijective K (MulEquiv.bijective (MulAut.conj g))).symm

/-- A subgroup of `↥K` normal in `↥K` has an image in `G` normalized by `K`. -/
theorem le_normalizer_map_of_normal {G : Type*} [Group G] (K : Subgroup G) {N : Subgroup ↥K}
    (hN : N.Normal) : K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have h1 : (⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹) ∈ N := hN.conj_mem y hy ⟨k, hk⟩
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, h1, ?_⟩
    rw [← hyx]
    rfl
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have h1 : (⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩) ∈ N := by
      simpa using hN.conj_mem y hy ⟨k, hk⟩⁻¹
    have hx' : x = k⁻¹ * K.subtype y * k := by
      rw [hyx]
      group
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩, h1, ?_⟩
    rw [hx']
    show K.subtype (⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩) = k⁻¹ * K.subtype y * k
    simp only [map_mul, map_inv]
    rfl

/-- An element of `K` normalizes the image in `G` of any normal subgroup of `↥K`. -/
theorem conjSub_map_subtype_eq_of_normal {G : Type*} [Group G] (K : Subgroup G)
    {N : Subgroup ↥K} (hN : N.Normal) {k : G} (hk : k ∈ K) :
    Work.GW2.conjSub k (N.map K.subtype) = N.map K.subtype := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have h1 : (⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹) ∈ N := hN.conj_mem y hy ⟨k, hk⟩
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, h1, ?_⟩
    have hx' : x = k * K.subtype y * k⁻¹ := by
      rw [hyx]
      group
    rw [hx']
    show K.subtype (⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹) = k * K.subtype y * k⁻¹
    simp only [map_mul, map_inv]
    rfl
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have h1 : (⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩) ∈ N := by
      simpa using hN.conj_mem y hy ⟨k, hk⟩⁻¹
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩, h1, ?_⟩
    rw [← hyx]
    show K.subtype (⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩) = k⁻¹ * K.subtype y * k
    simp only [map_mul, map_inv]
    rfl

/-- An injective image of a nontrivial subgroup is nontrivial. -/
theorem map_ne_bot_of_injective {G N : Type*} [Group G] [Group N] (f : G →* N)
    (hf : Function.Injective f) {H : Subgroup G} (hH : H ≠ ⊥) : H.map f ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := H)).mp hH
  have hmem : f x.1 ∈ (⊥ : Subgroup N) := by
    rw [← hbot]
    exact Subgroup.mem_map_of_mem f x.2
  have h1 : f x.1 = 1 := Subgroup.mem_bot.mp hmem
  exact hx (Subtype.ext (hf (by simpa using h1)))

/-- `O_p(X)` is a `p`-group (it is contained in the supremum of the normal `p`-subgroups). -/
theorem pCore_isPGroup' {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] :
    IsPGroup p (Work.GW2.pCore p X) := by
  have hsup : IsPGroup p ↥(sSup {N : Subgroup X | N.Normal ∧ IsPGroup p N}) :=
    Sylow.sSup_of_normal (G := X) (p := p) {N : Subgroup X | N.Normal ∧ IsPGroup p N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  exact hsup.to_le (Subgroup.normalCore_le _)

/-- `O_p(X)` lies in every Sylow `p`-subgroup of `X`. -/
theorem pCore_le_sylow' {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) : Work.GW2.pCore p X ≤ (P : Subgroup X) :=
  IsPGroup.le_sylow_of_normal (pCore_isPGroup' (X := X) (p := p)) P

/-- A nontrivial `p`-group has nontrivial center, in the shape of an intersection. -/
theorem inf_centralizer_ne_bot_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {K : Subgroup X} (hK : IsPGroup p K) (hne : K ≠ ⊥) :
    K ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := by
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  haveI : Finite ↥K := inferInstance
  have hc : Nontrivial ↥(Subgroup.center ↥K) := IsPGroup.center_nontrivial hK
  obtain ⟨z, hzne⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Subgroup.center ↥K)).mp
    ((Subgroup.nontrivial_iff_ne_bot _).mp hc)
  refine fun hbot => hzne ?_
  have hxc : ((z : ↥K) : X) ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 (⟨w, hw⟩ : ↥K))
  have hxmem : ((z : ↥K) : X) ∈ (K ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) :=
    ⟨(z : ↥K).2, hxc⟩
  rw [hbot] at hxmem
  apply Subtype.ext
  exact Subtype.ext (by simpa using hxmem)

/-- A subgroup is fixed by conjugation by its own elements. -/
theorem conjSub_eq_self_of_mem {G : Type*} [Group G] {K : Subgroup G} {g : G} (hg : g ∈ K) :
    Work.GW2.conjSub g K = K := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact K.mul_mem (K.mul_mem hg hy) (K.inv_mem hg)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

/-- `conjSub` is a left action: `(ab)⁻¹...` -/
theorem conjSub_mul {G : Type*} [Group G] (a b : G) (K : Subgroup G) :
    Work.GW2.conjSub (a * b) K = Work.GW2.conjSub a (Work.GW2.conjSub b K) := by
  ext x
  rw [mem_conjSub_iff, mem_conjSub_iff, mem_conjSub_iff]
  have h : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [h]

/-- Conjugating a subgroup pointwise is mapping by conjugation. -/
theorem smul_conj_eq_map {G : Type*} [Group G] (κ : G) (S : Subgroup G) :
    (MulAut.conj κ • S : Subgroup G) = S.map (MulAut.conj κ).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.mp hx
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    rw [← hyx]
    show (MulAut.conj κ) y = κ * y * κ⁻¹
    rw [MulAut.conj_apply]
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine Set.mem_smul_set.mpr ⟨y, hy, ?_⟩
    rw [← hyx]
    show (MulAut.conj κ) y = κ * y * κ⁻¹
    rw [MulAut.conj_apply]

/-- The underlying subgroup of `g • P` is the conjugate of the underlying subgroup of `P`. -/
theorem sylow_smul_coe_eq_conjSub {G : Type*} [Group G] {p : ℕ} (P Q : Sylow p G) (g : G)
    (h : g • P = Q) : ((Q : Subgroup G)) = Work.GW2.conjSub g ((P : Subgroup G)) := by
  have hset : ((g • P : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [h]
  rw [← hset, Sylow.coe_subgroup_smul]
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.mp hx
    show g⁻¹ * x * g ∈ (P : Subgroup G)
    have hyx' : x = g * y * g⁻¹ := by
      rw [← hyx]
      show (MulAut.conj g) y = g * y * g⁻¹
      rw [MulAut.conj_apply]
    rw [hyx']
    have h1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [h1]
    exact hy
  · intro hx
    refine Set.mem_smul_set.mpr ⟨g⁻¹ * x * g, hx, ?_⟩
    show (MulAut.conj g) (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

/-- The image in `G` of the conjugate of a subgroup of `↥K` is the conjugate of its image. -/
theorem map_subtype_conj {G : Type*} [Group G] (K : Subgroup G) (P : Subgroup ↥K) (κ : ↥K) :
    (P.map (MulAut.conj κ).toMonoidHom).map K.subtype =
      Work.GW2.conjSub (κ : G) (P.map K.subtype) := by
  rw [Subgroup.map_map, conjSub_eq_map, Subgroup.map_map]
  have hhom : (K.subtype.comp (MulAut.conj κ).toMonoidHom) =
      ((MulAut.conj (κ : G)).toMonoidHom.comp K.subtype) := by
    ext x
    show K.subtype (κ * x * κ⁻¹) = (κ : G) * K.subtype x * (κ : G)⁻¹
    simp [map_mul, map_inv]
  rw [hhom]

/-! ## Bender's Lemma 2.4 -/

theorem lemma24 (T : Work.GW2.LocalToolkit) (hZA : Work.GW2.ZJAProp) (hZB : Work.GW2.ZJBProp) : Work.GW2.Lemma24Prop := by
  intro G instG instF hFT hctx B M hMcoat hBRel p hp hp2 hFH hFM
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hctx.simple
  -- ## 0 : both maximal subgroups are nontrivial D-groups
  have hdihH : Work.GW2.DihOrCycSylow ↥B.Hhat := dihOrCycSylow_subgroup hctx.sylow B.Hhat
  have hdihM : Work.GW2.DihOrCycSylow ↥M := dihOrCycSylow_subgroup hctx.sylow M
  have hDGH : Work.GW2.IsDGroup ↥B.Hhat :=
    hctx.ih ↥B.Hhat (natCard_lt_of_lt_top B.Hhat_coatom.lt_top) hdihH
  have hDGM : Work.GW2.IsDGroup ↥M := hctx.ih ↥M (natCard_lt_of_lt_top hMcoat.lt_top) hdihM
  have hHnt : Nontrivial ↥B.Hhat :=
    ⟨⟨B.t, bSetup_t_mem_Hhat B⟩, 1, fun h => bSetup_t_ne_one B (Subtype.ext_iff.mp h)⟩
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hle : M ≤ Subgroup.zpowers B.t :=
      hbot.symm ▸ (bot_le : (⊥ : Subgroup G) ≤ Subgroup.zpowers B.t)
    rcases hMcoat.le_iff.mp hle with h | h
    · haveI : IsCyclic G := ⟨B.t, fun x => Subgroup.mem_zpowers_iff.mp (h.symm ▸ Subgroup.mem_top x)⟩
      obtain ⟨a, b, hab⟩ := hctx.nonab
      exact hab (mul_comm' a b)
    · exact bSetup_t_ne_one B (Subgroup.zpowers_eq_bot.mp (by rw [h, hbot]))
  have hMnt : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  -- ## 1 : F*(X) = O_p(X) ≠ 1 for both groups
  have hfH1 : IsPGroup p (Work.GW2.fstar ↥B.Hhat) :=
    IsPGroup.of_equiv hFH (Subgroup.equivMapOfInjective (Work.GW2.fstar ↥B.Hhat)
      B.Hhat.subtype B.Hhat.subtype_injective).symm
  have hfH2 : Work.GW2.fstar ↥B.Hhat = Work.GW2.pCore p ↥B.Hhat := fstar_eq_pCore_of_isPGroup hfH1
  have hOpne : Work.GW2.pCore p ↥B.Hhat ≠ ⊥ := by
    rw [← hfH2]
    exact fstar_ne_bot T.d16 hHnt hFT hdihH hDGH
  have hfM1 : IsPGroup p (Work.GW2.fstar ↥M) :=
    IsPGroup.of_equiv hFM (Subgroup.equivMapOfInjective (Work.GW2.fstar ↥M) M.subtype
      M.subtype_injective).symm
  have hfM2 : Work.GW2.fstar ↥M = Work.GW2.pCore p ↥M := fstar_eq_pCore_of_isPGroup hfM1
  have hOpMne : Work.GW2.pCore p ↥M ≠ ⊥ := by
    rw [← hfM2]
    exact fstar_ne_bot T.d16 hMnt hFT hdihM hDGM
  -- ## 2 : hypotheses of Glauberman's Z(J)-theorem in both groups
  have hconstrH : Subgroup.centralizer (Work.GW2.pCore p ↥B.Hhat : Set ↥B.Hhat) ≤
      Work.GW2.pCore p ↥B.Hhat := by
    have h := T.fstar ↥B.Hhat hFT hdihH hDGH
    rwa [hfH2] at h
  have hconstrM : Subgroup.centralizer (Work.GW2.pCore p ↥M : Set ↥M) ≤
      Work.GW2.pCore p ↥M := by
    have h := T.fstar ↥M hFT hdihM hDGM
    rwa [hfM2] at h
  -- ## 3 : Sylow subgroups, Z(J(P)) and the normalizers
  obtain ⟨P⟩ : Nonempty (Sylow p ↥B.Hhat) := inferInstance
  obtain ⟨Pm⟩ : Nonempty (Sylow p ↥M) := inferInstance
  haveI hPTG : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
  haveI hPTM : MulAction.IsPretransitive ↥M (Sylow p ↥M) := Sylow.isPretransitive_of_finite
  have hPne : (P : Subgroup ↥B.Hhat) ≠ ⊥ := fun h =>
    hOpne (le_bot_iff.mp (h ▸ pCore_le_sylow' P))
  have hPmne : (Pm : Subgroup ↥M) ≠ ⊥ := fun h =>
    hOpMne (le_bot_iff.mp (h ▸ pCore_le_sylow' Pm))
  set Q : Subgroup G := (P : Subgroup ↥B.Hhat).map B.Hhat.subtype with hQdef
  set Qm : Subgroup G := (Pm : Subgroup ↥M).map M.subtype with hQmdef
  have hZQ : Work.GW2.ZJ Q = (Work.GW2.ZJ (P : Subgroup ↥B.Hhat)).map B.Hhat.subtype := by
    rw [hQdef]
    exact (map_ZJ_subtype B.Hhat P).symm
  have hZQm : Work.GW2.ZJ Qm = (Work.GW2.ZJ (Pm : Subgroup ↥M)).map M.subtype := by
    rw [hQmdef]
    exact (map_ZJ_subtype M Pm).symm
  have hZJP : (Work.GW2.ZJ (P : Subgroup ↥B.Hhat)).Normal := hZA ↥B.Hhat p hp2 hdihH hconstrH P
  have hZJPm : (Work.GW2.ZJ (Pm : Subgroup ↥M)).Normal := hZA ↥M p hp2 hdihM hconstrM Pm
  have hZQne : Work.GW2.ZJ Q ≠ ⊥ := by
    rw [hZQ]
    exact map_ne_bot_of_injective B.Hhat.subtype B.Hhat.subtype_injective
      (ZJ_ne_bot P.isPGroup' hPne)
  have hZQle : Work.GW2.ZJ Q ≤ B.Hhat := by
    rw [hZQ]
    exact Subgroup.map_subtype_le _
  have hZQnorm : B.Hhat ≤ Subgroup.normalizer (Work.GW2.ZJ Q : Set G) := by
    rw [hZQ]
    exact le_normalizer_map_of_normal B.Hhat hZJP
  have hNZQ : Subgroup.normalizer (Work.GW2.ZJ Q : Set G) = B.Hhat :=
    normalizer_eq_of_coatom B.Hhat_coatom hZQle hZQne hZQnorm
  have hZQmne : Work.GW2.ZJ Qm ≠ ⊥ := by
    rw [hZQm]
    exact map_ne_bot_of_injective M.subtype M.subtype_injective (ZJ_ne_bot Pm.isPGroup' hPmne)
  have hZQmle : Work.GW2.ZJ Qm ≤ M := by
    rw [hZQm]
    exact Subgroup.map_subtype_le _
  have hZQmnorm : M ≤ Subgroup.normalizer (Work.GW2.ZJ Qm : Set G) := by
    rw [hZQm]
    exact le_normalizer_map_of_normal M hZJPm
  have hNZQm : Subgroup.normalizer (Work.GW2.ZJ Qm : Set G) = M :=
    normalizer_eq_of_coatom hMcoat hZQmle hZQmne hZQmnorm
  -- the images of the Sylow subgroups are Sylow subgroups of `G`
  have hNQ : Subgroup.normalizer (Q : Set G) ≤ B.Hhat :=
    (normalizer_le_normalizer_ZJ Q).trans (le_of_eq hNZQ)
  obtain ⟨P', hP'⟩ := map_sylow_isSylow P hNQ
  have hNQm : Subgroup.normalizer (Qm : Set G) ≤ M :=
    (normalizer_le_normalizer_ZJ Qm).trans (le_of_eq hNZQm)
  obtain ⟨P'm, hP'm⟩ := map_sylow_isSylow Pm hNQm
  -- ## 4 : `Ĥ` and `M` are conjugate
  obtain ⟨γ, hγ⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) (α := Sylow p G) P' P'm
  have hQm_eq : Qm = Work.GW2.conjSub γ Q := by
    rw [hQmdef, hQdef, ← hP'm, ← hP']
    exact sylow_smul_coe_eq_conjSub P' P'm γ hγ
  have hMeq : M = Work.GW2.conjSub γ B.Hhat := by
    rw [← hNZQm]
    have h2 : Work.GW2.ZJ Qm = Work.GW2.conjSub γ (Work.GW2.ZJ Q) := by
      rw [hQm_eq]
      exact ZJ_conj Q γ
    rw [h2, normalizer_conjSub, hNZQ]
  -- ## 5 : `W = Z(O_p(Ĥ))` is a nontrivial normal subgroup of `Ĥ` contained in `M`
  obtain ⟨X, hXF, hXle⟩ := hBRel
  have hFitH : Work.GW2.fittingIn B.Hhat ≤ (Work.GW2.pCore p ↥B.Hhat).map B.Hhat.subtype := by
    change (Work.GW2.fitting ↥B.Hhat).map B.Hhat.subtype ≤ _
    exact Subgroup.map_mono (le_trans le_sup_left (le_of_eq hfH2))
  have hXOp : X ≤ (Work.GW2.pCore p ↥B.Hhat).map B.Hhat.subtype := hXF.trans hFitH
  set OpG : Subgroup G := (Work.GW2.pCore p ↥B.Hhat).map B.Hhat.subtype with hOpGdef
  have hOpGp : IsPGroup p OpG := (pCore_isPGroup' (X := ↥B.Hhat) (p := p)).map B.Hhat.subtype
  have hOpGne : OpG ≠ ⊥ := map_ne_bot_of_injective B.Hhat.subtype B.Hhat.subtype_injective hOpne
  set W : Subgroup G := OpG ⊓ Subgroup.centralizer (OpG : Set G) with hWdef
  have hWp : IsPGroup p W := hOpGp.to_le inf_le_left
  have hWne : W ≠ ⊥ := inf_centralizer_ne_bot_of_isPGroup hOpGp hOpGne
  have hfstarIn_eq : Work.GW2.fstarIn B.Hhat = OpG := by
    change (Work.GW2.fstar ↥B.Hhat).map B.Hhat.subtype = OpG
    rw [hfH2, ← hOpGdef]
  have hWleN : W ≤ Subgroup.normalizer (X : Set G) := by
    intro w hw
    have hwc : ∀ y ∈ X, y * w = w * y := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hw.2 y (hXOp hy)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [show w * x * w⁻¹ = x by rw [← hwc x hx]; group]
      exact hx
    · intro hx
      have h1 : w * x = w * (w * x * w⁻¹) := by
        calc w * x = (w * x * w⁻¹) * w := by group
          _ = w * (w * x * w⁻¹) := hwc (w * x * w⁻¹) hx
      have hx' : x = w * x * w⁻¹ := mul_left_cancel h1
      rw [← hx'] at hx
      exact hx
  have hWleOpG : W ≤ OpG := by
    rw [hWdef]
    exact inf_le_left
  have hWleM : W ≤ M := fun w hw =>
    hXle ⟨hWleN hw, by rw [hfstarIn_eq]; exact hWleOpG hw⟩
  have hWleH : W ≤ B.Hhat := hWleOpG.trans (Subgroup.map_subtype_le _)
  have hWleQ : W ≤ Q := hWleOpG.trans (Subgroup.map_mono (pCore_le_sylow' P))
  have hWnorm : B.Hhat ≤ Subgroup.normalizer (W : Set G) := by
    intro h hh
    have hconj : Work.GW2.conjSub h W = W := by
      rw [hWdef, conjSub_inf h OpG (Subgroup.centralizer (OpG : Set G)), conjSub_centralizer,
        conjSub_map_subtype_eq_of_normal B.Hhat (Work.GW2.pCore_normal p ↥B.Hhat) hh]
    have hconj' : Work.GW2.conjSub h⁻¹ W = W := by
      calc Work.GW2.conjSub h⁻¹ W = Work.GW2.conjSub h⁻¹ (Work.GW2.conjSub h W) := by rw [hconj]
        _ = W := conjSub_inv_conjSub h W
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [show (h * x * h⁻¹ ∈ W) ↔ (x ∈ Work.GW2.conjSub h⁻¹ W) from
      (mem_conjSub_iff' (g := h) (K := W)).symm, hconj']
  have hNW : Subgroup.normalizer (W : Set G) = B.Hhat :=
    normalizer_eq_of_coatom B.Hhat_coatom hWleH hWne hWnorm
  -- ## 6 : adjust `γ` on the right so that `W^{γ⁻¹} ⊆ Q`
  have hWconjH : Work.GW2.conjSub γ⁻¹ W ≤ B.Hhat := by
    have h1 : Work.GW2.conjSub γ⁻¹ W ≤ Work.GW2.conjSub γ⁻¹ (Work.GW2.conjSub γ B.Hhat) :=
      conjSub_mono (hMeq ▸ hWleM) γ⁻¹
    rwa [conjSub_inv_conjSub] at h1
  set W' : Subgroup ↥B.Hhat := (Work.GW2.conjSub γ⁻¹ W).comap B.Hhat.subtype with hW'def
  have hW'map : W'.map B.Hhat.subtype = Work.GW2.conjSub γ⁻¹ W := by
    rw [hW'def, Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hWconjH]
  have hW'p : IsPGroup p W' :=
    IsPGroup.of_equiv (by rw [hW'map]; exact hWp.map (MulAut.conj γ⁻¹).toMonoidHom)
      (Subgroup.equivMapOfInjective W' B.Hhat.subtype B.Hhat.subtype_injective).symm
  obtain ⟨k, hk⟩ := IsPGroup.exists_le_sylow hW'p
  obtain ⟨κ, hκ⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := ↥B.Hhat) (α := Sylow p ↥B.Hhat) P k
  have hW'le : W' ≤ (P : Subgroup ↥B.Hhat).map (MulAut.conj κ).toMonoidHom := by
    rw [← hκ] at hk
    rw [Sylow.coe_subgroup_smul, smul_conj_eq_map] at hk
    exact hk
  have hmapκ : ((P : Subgroup ↥B.Hhat).map (MulAut.conj κ).toMonoidHom).map B.Hhat.subtype
      = Work.GW2.conjSub (κ : G) Q := by
    rw [hQdef]
    exact map_subtype_conj B.Hhat P κ
  have hW'leG : W'.map B.Hhat.subtype ≤ Work.GW2.conjSub (κ : G) Q := by
    rw [← hmapκ]
    exact Subgroup.map_mono hW'le
  have hWleconj : Work.GW2.conjSub ((γ * (κ : G))⁻¹) W ≤ Q := by
    have heq : Work.GW2.conjSub ((γ * (κ : G))⁻¹) W =
        Work.GW2.conjSub (κ : G)⁻¹ (Work.GW2.conjSub γ⁻¹ W) := by
      rw [mul_inv_rev, conjSub_mul]
    rw [heq, show Work.GW2.conjSub γ⁻¹ W = W'.map B.Hhat.subtype from hW'map.symm,
      conjSub_le_iff]
    simpa using hW'leG
  -- ## 7 : Theorem B
  have hWsub : (W : Set G) ⊆ (P' : Subgroup G) := by
    intro w hw
    rw [hP']
    exact hWleQ hw
  have hWnonempty : (W : Set G).Nonempty := by
    obtain ⟨w, hw⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := W)).mp hWne
    exact ⟨w, w.2⟩
  have hxWx : ∀ w ∈ (W : Set G),
      (γ * (κ : G))⁻¹ * w * (γ * (κ : G))⁻¹⁻¹ ∈ (P' : Subgroup G) := by
    intro w hw
    rw [hP']
    refine hWleconj ?_
    rw [mem_conjSub_iff]
    have h2 : (γ * (κ : G))⁻¹⁻¹ * ((γ * (κ : G))⁻¹ * w * (γ * (κ : G))⁻¹⁻¹) *
        (γ * (κ : G))⁻¹ = w := by group
    rw [h2]
    exact hw
  obtain ⟨c, n, hc, hn, hcn⟩ :=
    hZB G p hp2 hctx.sylow P' (W : Set G) (γ * (κ : G))⁻¹ hWnonempty hWsub hxWx
  have hnH : n ∈ B.Hhat := by
    have h1 : n ∈ Subgroup.normalizer (Work.GW2.ZJ Q : Set G) := by
      rwa [hP'] at hn
    rwa [hNZQ] at h1
  have hcH : c ∈ B.Hhat := by
    have h1 : c ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.centralizer_le_normalizer (W : Set G) hc
    rwa [hNW] at h1
  have hginvH : (γ * (κ : G))⁻¹ ∈ B.Hhat := by
    rw [hcn]
    exact B.Hhat.mul_mem hcH hnH
  have hγH : γ ∈ B.Hhat := by
    have h1 : γ * (κ : G) ∈ B.Hhat := by simpa using B.Hhat.inv_mem hginvH
    have h3 : γ * (κ : G) * (κ : G)⁻¹ ∈ B.Hhat := B.Hhat.mul_mem h1 (B.Hhat.inv_mem κ.2)
    rwa [show γ * (κ : G) * (κ : G)⁻¹ = γ by group] at h3
  rw [hMeq, conjSub_eq_self_of_mem hγH]

end Work.CORE2A
