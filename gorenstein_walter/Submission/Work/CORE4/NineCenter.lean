/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — step (9), the centre leaf `NineCenter`

Bender 1981, §4, p. 226 (the line following "This proves that `E/Z(E)` is isomorphic to some
`L₂(q)`"):

> `|F(M)|` is prime to `q` by (7), whence `Z(E) = 1`: `E ≅ L₂(q)`. (9)

`Work.GW2.NineCenterProp I` says: from the §4 (1)–(8) budget `Hyp9`, the `L₂(q)`-shape data
`NineShape C.D p e` (`E/Z(E) ≅ L₂(p ^ e)`, `|Z(E)|` odd) and the numerical data
`NineKData C.D (p ^ e) k k'` (`|K| ∣ k`, `3 ≤ |K|`, `2k = p ^ e ± 1`), the layer
`E = E(M) = layerIn C.D.M` itself is isomorphic to `PSL(2, p ^ e)` — i.e. `Z(E) = 1`.

## Route

* `nine_center_map_subtype_le_fittingIn`: `Z(E)` is abelian, hence nilpotent, and normal in `M`
  (`E ⊴ M` and the centre is characteristic in `E`), so `Z(E) ≤ F(M)`.
* `nine_twoMulPow_not_dvd`: the arithmetic `p ∤ k` when `2k = p ^ e ± 1` and `e ≥ 1`.
* Bender's (7) (`Case2SevenFacts`) gives `π(F(M)) ⊆ π = π(K₀)` and `K₀ ≤ K`, so a prime divisor
  `p` of `|Z(E)|` would divide `|K|`, hence `k` — contradicting the previous line. Thus
  `Nat.Coprime |Z(E)| p`.
* `E` is quasisimple (`LayerCtx6`), hence perfect as an abstract group
  (`nine_commutator_top_eq_top`); with `|Z(E)|` odd and `E/Z(E) ≅ L₂(p ^ e)`, `I.toolkit.l19`
  gives `Z(E) = ⊥`.
* `E ≅ E/⊥ ≅ E/Z(E) ≅ PSL(2, p ^ e)`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

/-! ## Auxiliary group theory -/

/-- A normal nilpotent subgroup of a group `X` lies in the Fitting subgroup `F(X)`
(the normal core of the join of the normal nilpotent subgroups is that join itself). -/
theorem nine_normal_nilpotent_le_fitting {X : Type*} [Group X] {N : Subgroup X}
    (hN : N.Normal) (hNil : Group.IsNilpotent ↥N) : N ≤ Work.GW2.fitting X := by
  haveI := hN
  haveI := hNil
  rw [Work.GW2.fitting]
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, inferInstance⟩)

/-- **`Z(E) ≤ F(M)` for `E ⊴ M`.**  The centre of `E`, viewed in the ambient group, is an abelian,
hence nilpotent, normal subgroup of `M`; so it lies in the Fitting subgroup of `M`. -/
theorem nine_center_map_subtype_le_fittingIn {G : Type*} [Group G] [Finite G] (M E : Subgroup G)
    (hEM : E ≤ M) (hN : (E.subgroupOf M).Normal) :
    (Subgroup.center ↥E).map E.subtype ≤ Work.GW2.fittingIn M := by
  set N : Subgroup G := (Subgroup.center ↥E).map E.subtype with hNdef
  have hNleM : N ≤ M := (Subgroup.map_subtype_le (Subgroup.center ↥E)).trans hEM
  -- `E ⊴ M` in elementwise form
  have hconjE : ∀ h k : G, h ∈ E → k ∈ M → k * h * k⁻¹ ∈ E :=
    (Subgroup.normal_subgroupOf_iff hEM).mp hN
  -- `N = Z(E)` is normal in `M`
  have hconj : ∀ h k : G, h ∈ N → k ∈ M → k * h * k⁻¹ ∈ N := by
    intro h k hh hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    have hyc : ∀ e ∈ E, (y : G) * e = e * (y : G) := fun e he => by
      have h1 := Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hy ⟨e, he⟩)
      simpa using h1.symm
    refine Subgroup.mem_map.mpr ⟨⟨k * (y : G) * k⁻¹, hconjE (y : G) k y.2 hk⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hk1 : k⁻¹ * (g : G) * k ∈ E := by
      simpa using hconjE (g : G) k⁻¹ g.2 (M.inv_mem hk)
    have key : (k * (y : G) * k⁻¹) * (g : G) = (g : G) * (k * (y : G) * k⁻¹) := by
      calc (k * (y : G) * k⁻¹) * (g : G)
          = k * ((y : G) * (k⁻¹ * (g : G) * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * (g : G) * k) * (y : G)) * k⁻¹ := by rw [hyc _ hk1]
        _ = (g : G) * (k * (y : G) * k⁻¹) := by group
    exact Subtype.ext key.symm
  have hNnorm : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff hNleM).mpr hconj
  -- `↥(N.subgroupOf M) ≃* ↥(Z(E))`, so it is abelian, hence nilpotent
  have hiso : ↥(N.subgroupOf M) ≃* ↥(Subgroup.center ↥E) :=
    (Subgroup.subgroupOfEquivOfLe hNleM).trans
      (Subgroup.equivMapOfInjective (Subgroup.center ↥E) E.subtype
        (Subgroup.subtype_injective E)).symm
  haveI : Group.IsNilpotent ↥(Subgroup.center ↥E) := inferInstance
  have hnil : Group.IsNilpotent ↥(N.subgroupOf M) := Group.nilpotent_of_mulEquiv hiso.symm
  have hle : N.subgroupOf M ≤ Work.GW2.fitting ↥M :=
    nine_normal_nilpotent_le_fitting hNnorm hnil
  have h1 := Subgroup.map_mono (f := M.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hNleM] at h1
  exact h1

/-- **Perfectness as an abstract group.**  If a subgroup `E ≤ X` equals its commutator subgroup
`⁅E, E⁆`, then `↥E` is perfect in its own right.  (The perfectness input of `I.toolkit.l19` for
the group `↥E`, from the quasisimplicity of `E` given by `LayerCtx6`.) -/
theorem nine_commutator_top_eq_top {X : Type*} [Group X] {E : Subgroup X}
    (h : ⁅E, E⁆ = E) : ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆ = ⊤ := by
  apply Subgroup.map_injective (f := E.subtype) Subtype.coe_injective
  simp only [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, h]

/-! ## Auxiliary arithmetic -/

/-- If `2k = p ^ e ± 1` with `p` prime and `e ≥ 1`, then `p ∤ k`.  (Indeed `p ∣ p ^ e`, so
`p ∣ k` would force `p ∣ 1`.) -/
theorem nine_twoMulPow_not_dvd {p e k : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (h : 2 * k = p ^ e + 1 ∨ 2 * k = p ^ e - 1) : ¬ p ∣ k := by
  intro hpk
  have hp2 : 2 ≤ p := hp.two_le
  have hpdvd2k : p ∣ 2 * k := by rw [mul_comm]; exact dvd_mul_of_dvd_left hpk 2
  have hpe : p ∣ p ^ e := dvd_pow_self p (by omega)
  have hdvd1 : p ∣ 1 := by
    rcases h with h | h
    · have hp1 : p ∣ p ^ e + 1 := h ▸ hpdvd2k
      have hsub := Nat.dvd_sub hp1 hpe
      have h1 : p ^ e + 1 - p ^ e = 1 := by omega
      simpa [h1] using hsub
    · have hp1 : p ∣ p ^ e - 1 := h ▸ hpdvd2k
      have hsub := Nat.dvd_sub hpe hp1
      have h1 : p ^ e - (p ^ e - 1) = 1 := by
        have : 1 ≤ p ^ e := Nat.one_le_pow e p (by omega)
        omega
      simpa [h1] using hsub
  have hpid : p = 1 := Nat.dvd_one.mp hdvd1
  omega

/-! ## The leaf -/

/-- **LEAF C10.N3 `NineCenter`** (Bender pp. 226–227): "`|F(M)|` is prime to `q` by (7), whence
`Z(E) = 1`: `E ≅ L₂(q)`".

`NineCenterProp I` gives, from `Hyp9 G B C`, `NineShape C.D p e` and `NineKData C.D (p^e) k k'`:
`Nonempty (layerIn C.D.M ≃* PSL(2, GaloisField p e))`, i.e. `E ≅ L₂(q)` (not merely `E/Z(E)`).

Route (design pass 10 §3.3, N3):
* `Z(E)` is an abelian normal subgroup of `M`, so `Z(E) ≤ F(M)`;
* `π(F(M)) ⊆ π = π(K₀) ⊆ π(K)` (from `Case2SevenFacts` conjuncts 5 and 2, and `K₀ ≤ K`), while
  `|K| ∣ k` and `2k = q ± 1` is prime to `p` (`q = p^e`), so `Nat.Coprime |Z(E)| p`;
* `I.toolkit.l19` (`L19Prop`, whose perfectness hypothesis is `IsQuasisimple E` from
  `LayerCtx6`/`lay`) then gives `Z(E) = ⊥`, and `E ≅ E/⊥ ≅ L₂(q)`.

This is the leaf that the older `CORE4/NineImpl9/NineCoprime` (declared under-hypothesised) was
missing: (7) is now the hypothesis `Case2SevenFacts`. -/
theorem NineCenter (I : Work.GW2.C4Inputs) : Work.GW2.NineCenterProp I := by
  intro G _instG _instF B C hH p e hpFact hshape k k' hkData
  obtain ⟨hbc, hc2, hpp, h7, h8⟩ := hH
  obtain ⟨hpodd, h5, ⟨hiso⟩, hoddZ⟩ := hshape
  obtain ⟨hkeven, hk'odd, hcases, hkdvd, hK3, hKodd⟩ := hkData
  have hp : p.Prime := hpFact.out
  -- `E = E(M) = layerIn M`
  set E : Subgroup G := Work.GW2.layerIn C.D.M with hEdef
  have hEM : E ≤ C.D.M := by rw [hEdef, Work.GW2.layerIn]; exact Subgroup.map_subtype_le _
  have hEnorm : (E.subgroupOf C.D.M).Normal := by
    have hEq : E.subgroupOf C.D.M = Work.GW2.layer ↥C.D.M := by
      rw [hEdef, Work.GW2.layerIn]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective C.D.M)
        (Work.GW2.layer ↥C.D.M)
    rw [hEq]
    change (sSup {F : Subgroup ↥C.D.M | F.Normal ∧ IsQuasisimple F}).Normal
    exact Subgroup.sSup_normal _ (fun H hH => hH.1)
  -- `Z(E) ≤ F(M)`
  have hZle : (Subgroup.center ↥E).map E.subtype ≤ Work.GW2.fittingIn C.D.M :=
    nine_center_map_subtype_le_fittingIn C.D.M E hEM hEnorm
  -- arithmetic: `p ∤ k`
  have he1 : 1 ≤ e := by
    by_contra hcon
    have h0 : e = 0 := by omega
    subst h0
    simp at h5
  have hqcases : 2 * k = p ^ e + 1 ∨ 2 * k = p ^ e - 1 :=
    hcases.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hnotdvdk : ¬ p ∣ k := nine_twoMulPow_not_dvd hp he1 hqcases
  have hnotdvdK : ¬ p ∣ Nat.card C.D.K := fun h => hnotdvdk (dvd_trans h hkdvd)
  -- `p ∤ |Z(E)|`: `π(Z(E)) ⊆ π(F(M)) ⊆ π(K₀) ⊆ π(K)`
  have hnotdvdZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥E) := by
    intro hpZ
    have h1 : p ∣ Nat.card ↥((Subgroup.center ↥E).map E.subtype) := by
      rwa [Subgroup.card_map_of_injective E.subtype_injective]
    have h2 : p ∣ Nat.card ↥(Work.GW2.fittingIn C.D.M) :=
      dvd_trans h1 (Subgroup.card_dvd_of_le hZle)
    have hfit : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn C.D.M) := by
      refine hp.mem_primeFactors h2 ?_
      have := Nat.card_pos (α := ↥(Work.GW2.fittingIn C.D.M))
      omega
    have hpi : p ∈ B.piFU := h7.2.2.2.2.1 hfit
    have hK0mem : p ∈ Work.GW2.primesOf C.D.K0 := by
      rw [h7.2.1]; exact hpi
    have hpK0 : p ∣ Nat.card ↥(C.D.K0) := (Nat.mem_primeFactors.mp hK0mem).2.1
    have hpK : p ∣ Nat.card ↥(C.D.K) :=
      dvd_trans hpK0 (Subgroup.card_dvd_of_le (inf_le_right : C.D.K0 ≤ C.D.K))
    exact hnotdvdK hpK
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥E)) p :=
    Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnotdvdZ)
  -- perfectness of `E` (`LayerCtx6`)
  have hD : Work.GW2.DihOrCycSylow ↥C.D.M := Work.CORE4.DihOrCycSub hbc.sylow C.D.M
  obtain ⟨hq, -, -⟩ := Work.CORE4.LayerCtx6 I hbc C hD
  have hperf : ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆ = ⊤ := by
    rw [hEdef]
    exact nine_commutator_top_eq_top hq.1
  -- `I.toolkit.l19`: `Z(E) = ⊥`
  have hZbot : Subgroup.center ↥E = ⊥ :=
    I.toolkit.l19 ↥E p e hpodd h5 hperf ⟨hiso⟩ hoddZ hcop
  -- `E ≅ E/⊥ ≅ E/Z(E) ≅ PSL(2, p^e)`
  exact ⟨(QuotientGroup.quotientBot (G := ↥E)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZbot.symm).trans hiso)⟩

end Work.CORE4
