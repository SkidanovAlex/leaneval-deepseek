import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.d16_case_a_false
import Submission.Work.CORE2A.false_of_isCyclic_sylow_of_center_quotient
import Submission.Work.BMAX.LayerCentralizesFitting

/-!
# CORE2A: Bender 1.6(d) cannot occur for `X = Ĥ` when `O₂(Ĥ) ⊄ S₀`

The target theorem `Work.CORE2A.d16_case_d_false` says that in Bender's minimal-counterexample
setting, case (d) of `Work.GW2.D16Prop` for the maximal subgroup `X = Ĥ` is incompatible with
`O₂(Ĥ) ⊄ S₀`.

## The mathematics

`Ĥ` is a proper subgroup of `G`, hence a `D`-group by `BenderCtx.ih`.  Let `E ⊴ Ĥ` be quasisimple
with `Ĥ/E` solvable.  By Bender's Lemma 1.6 (`Work.GW2.LayerProp`, the toolkit field `T.lay`)
`layer Ĥ = E`, `Z(E)` has odd order, and `E/Z(E)` is `A₇` or `L₂(q)`, `q ≥ 5`.

Let `V = O₂(Ĥ)`, a normal `2`-subgroup of `Ĥ`.  Since `V` is nilpotent and `E` is quasisimple,
`[V, E] = 1` (`Work.BMAX.nilpotent_normal_le_centralizer_of_isQuasisimple`); as `V` is a `2`-group
and `Z(E)` has odd order this gives `V ⊓ E = ⊥`.  So `E` embeds into `Ĥ/V`.

Now `V ≤ S` (a normal `2`-subgroup lies in every Sylow `2`-subgroup), and `V ⊄ S₀` is exactly the
hypothesis.  Since `S₀` has index `2` in `S`, this forces `S = S₀ V`, hence the image
`S V/V = S/V ≅ S₀/(S₀ ⊓ V)` of `S` in `Ĥ/V` is **cyclic**.  It is a Sylow `2`-subgroup of `Ĥ/V`
(`Sylow.mapSurjective`), so every `2`-subgroup of `Ĥ/V` is cyclic.

Therefore every `2`-subgroup of `E` — in particular its Sylow `2`-subgroups — is cyclic.  But
`E/Z(E) ≅ A₇` or `L₂(q)`, and those have non-cyclic Sylow `2`-subgroups, while `Z(E)` has odd
order; this is impossible
(`Work.CORE2A.false_of_isCyclic_sylow_of_center_quotient`).

The hypothesis `h21` (`Lemma21Prop`) is not needed for this branch; it is kept because the caller
supplies it uniformly.
-/

set_option linter.unusedVariables false

namespace Work.CORE2A

open Subgroup

/-! ## 1. Two elementary transfer lemmas -/

/-- In a finite group with a cyclic Sylow `2`-subgroup, every `2`-subgroup is cyclic. -/
theorem isCyclic_of_isPGroup_two_of_sylow_isCyclic {Y : Type} [Group Y] [Finite Y]
    (H : Sylow 2 Y) (hH : IsCyclic ↥(H : Subgroup Y)) {P : Subgroup Y} (hP : IsPGroup 2 ↥P) :
    IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hle⟩ := hP.exists_le_sylow
  haveI hQcyc : IsCyclic ↥(Q : Subgroup Y) := by
    -- `Q` and `H` are conjugate Sylow subgroups, so `Q` is cyclic.
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Y) Q H
    have hmap : ((Q : Subgroup Y).map (MulAut.conj g).toMonoidHom) = (H : Subgroup Y) := by
      have h1 : ((g • Q : Sylow 2 Y) : Subgroup Y)
          = (Q : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul]
        rfl
      rw [← h1, hg]
    have he : ↥(Q : Subgroup Y) ≃* ↥(H : Subgroup Y) :=
      (Subgroup.equivMapOfInjective (Q : Subgroup Y) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hmap)
    exact (MulEquiv.isCyclic he).mpr hH
  exact isCyclic_of_le hle

/-- If `Y` embeds into a finite group `Z` all of whose `2`-subgroups are cyclic, then every
`2`-subgroup of `Y` is cyclic. -/
theorem isCyclic_of_isPGroup_two_of_injective {Y Z : Type} [Group Y] [Finite Y] [Group Z] [Finite Z]
    (f : Y →* Z) (hf : Function.Injective f) (H : Sylow 2 Z)
    (hH : IsCyclic ↥(H : Subgroup Z)) {P : Subgroup Y} (hP : IsPGroup 2 ↥P) :
    IsCyclic ↥P := by
  have hmap : IsPGroup 2 ↥((P.map f : Subgroup Z)) := hP.map f
  have hcyc : IsCyclic ↥(P.map f : Subgroup Z) :=
    isCyclic_of_isPGroup_two_of_sylow_isCyclic H hH hmap
  exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective P f hf)).mpr hcyc

/-! ## 2. The target theorem -/

/-- Bender 1.6(d) cannot occur for `X = Ĥ` together with `O₂(Ĥ) ⊄ S₀`.

`Ĥ` is a proper subgroup of `G`, hence a `D`-group (`BenderCtx.ih`,
`Work.CORE2A.dihOrCycSylow_subgroup`, `IsCoatom.card_lt_card`).  Let `E ⊴ Ĥ` be quasisimple
with `Ĥ/E` solvable.  By `Work.GW2.LayerProp` (`T.lay`, applicable because `Ĥ` is a `D`-group)
`Z(E)` is odd and `E/Z(E) ≅ A₇` or `L₂(q)`, `q ≥ 5`.  Since `V = O₂(Ĥ) ≠ 1` is a `2`-group
normal in `Ĥ`, `V ∩ E ≤ O₂(E) ≤ Z(E)` is both a `2`-group and odd, so `V ∩ E = 1`, whence
`[V, E] = 1` and `V ≤ C_Ĥ(E)`.  Also `E` has even order (a quasisimple group is not solvable),
so `E` contains an involution `u`, and `t ~ u` in `G` (all involutions conjugate).  Suggested
route: use `T.lay`/`T.a7`/`T.l2*` (the structure of involutions and their centralizers in
`A₇` and `L₂(q)`) together with `InvolutionFusionProp` and `h21` to reach a contradiction with
`E ≤ Ĥ`, `Ĥ/E` solvable. -/
theorem d16_case_d_false (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0 →
        (∃ (E : Subgroup ↥B.Hhat) (_ : E.Normal), Work.GW2.IsQuasisimple E ∧
          Group.IsSolvable (↥B.Hhat ⧸ E)) → False := by
  intro G _ _ hFT hctx B hnotle hex
  obtain ⟨E, hEnorm, hEquasi, hsolv⟩ := hex
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `V = O₂(Ĥ)`, viewed inside `X = ↥Ĥ`, and `K = S`, `A = S₀`.
  set V : Subgroup ↥B.Hhat := Work.GW2.pCore 2 ↥B.Hhat with hV
  set K : Subgroup ↥B.Hhat := (B.S : Subgroup G).subgroupOf B.Hhat with hK
  set A : Subgroup ↥B.Hhat := B.S0.subgroupOf B.Hhat with hA
  haveI hVnorm : V.Normal := by rw [hV]; exact Work.GW2.pCore_normal 2 ↥B.Hhat
  -- ## 2.1 `Ĥ` is a `D`-group, hence Bender 1.6 gives the layer structure.
  have hlt : Nat.card ↥B.Hhat < Nat.card G := by
    have h1 : B.Hhat < (⊤ : Subgroup G) := B.Hhat_coatom.lt_top
    simpa using Subgroup.card_lt_of_lt h1
  have hDHC : Work.GW2.DihOrCycSylow ↥B.Hhat :=
    Work.CORE2A.dihOrCycSylow_subgroup hctx.sylow B.Hhat
  have hDG : Work.GW2.IsDGroup ↥B.Hhat := hctx.ih _ hlt hDHC
  obtain ⟨hlayer, hoddZ, hshape⟩ := T.lay ↥B.Hhat hFT hDHC hDG E hEnorm hEquasi
  -- ## 2.2 `V ⊓ E = ⊥`.
  have hVnil : Group.IsNilpotent ↥V := by
    rw [hV]
    exact (Work.CORE2A.pCore_isPGroup_of_finite (H := ↥B.Hhat) (p := 2)).isNilpotent
  have hVcent : V ≤ Subgroup.centralizer (E : Set ↥B.Hhat) := by
    rw [hV]
    exact Work.BMAX.nilpotent_normal_le_centralizer_of_isQuasisimple hEnorm hEquasi
      (Work.GW2.pCore_normal 2 ↥B.Hhat) hVnil
  have hEV : E ⊓ V = ⊥ := by
    have hle : (E ⊓ V).subgroupOf E ≤ Subgroup.center ↥E := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hVcent hx.2) (y : ↥B.Hhat) y.2
    have hpg : IsPGroup 2 ↥((E ⊓ V).subgroupOf E) := by
      have h1 : IsPGroup 2 ↥(E ⊓ V) := by
        rw [hV]
        exact (Work.CORE2A.pCore_isPGroup_of_finite (H := ↥B.Hhat) (p := 2)).to_le inf_le_right
      exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    have hpi : Subgroup.IsPiSubgroup ({2}ᶜ : Set ℕ) (Subgroup.center ↥E) := by
      intro q hq
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hq2
      subst hq2
      obtain ⟨-, hdvd, -⟩ := Nat.mem_primeFactors.mp hq
      exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hoddZ)
    have hbot : (E ⊓ V).subgroupOf E = ⊥ :=
      Work.CORE2A.eq_bot_of_le_of_isPGroup_two_of_isPiSubgroup_compl hpg hpi hle
    have h2 : ((E ⊓ V).subgroupOf E).map E.subtype = ⊥ := by rw [hbot, Subgroup.map_bot]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at h2
    exact h2
  -- ## 2.3 `V ≤ S` and `S = S₀ ⊔ V` (this is where `O₂(Ĥ) ⊄ S₀` is used).
  have hVleK : V ≤ K := by
    intro x hx
    rw [hK, Subgroup.mem_subgroupOf]
    rw [hV] at hx
    exact Work.CORE2A.pCoreIn_le_S B (Subgroup.mem_map_of_mem B.Hhat.subtype hx)
  have hAleK : A ≤ K := by
    intro x hx
    rw [hA, Subgroup.mem_subgroupOf] at hx
    rw [hK, Subgroup.mem_subgroupOf]
    exact B.S0_le hx
  have hS_eq : K = A ⊔ V := by
    have hri : A.relIndex K = 2 := by
      rw [hA, hK, Subgroup.relIndex_subgroupOf (Work.CORE2A.bSetup_S_le_Hhat B)]
      exact B.S0_index
    have hchain := Subgroup.relIndex_mul_relIndex A (A ⊔ V) K le_sup_left (sup_le hAleK hVleK)
    rw [hri] at hchain
    have hne : A.relIndex (A ⊔ V) ≠ 1 := by
      intro h1
      have hVA : V ≤ A := le_trans le_sup_right (Subgroup.relIndex_eq_one.mp h1)
      apply hnotle
      rw [show Work.GW2.pCoreIn 2 B.Hhat = V.map B.Hhat.subtype from by rw [hV]; rfl]
      refine Subgroup.map_le_iff_le_comap.mpr ?_
      rw [hA] at hVA
      rw [Subgroup.subgroupOf] at hVA
      exact hVA
    have h2 : A.relIndex (A ⊔ V) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp ⟨(A ⊔ V).relIndex K, hchain.symm⟩ with h | h
      · exact absurd h hne
      · exact h
    have h3 : (A ⊔ V).relIndex K = 1 := by
      rw [h2] at hchain
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) (sup_le hAleK hVleK)
  -- ## 2.4 The image of `S` in `↥Ĥ ⧸ V` is a cyclic Sylow `2`-subgroup.
  have hKmap : K.map (QuotientGroup.mk' V) = A.map (QuotientGroup.mk' V) := by
    have hVker : V.map (QuotientGroup.mk' V) = ⊥ :=
      (Subgroup.map_eq_bot_iff V (f := QuotientGroup.mk' V)).mpr
        (by rw [QuotientGroup.ker_mk'])
    rw [hS_eq, Subgroup.map_sup, hVker, sup_bot_eq]
  have hAcyc : IsCyclic ↥(A.map (QuotientGroup.mk' V)) := by
    haveI hAc : IsCyclic ↥A := by
      rw [hA]
      exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe
        (B.S0_le.trans (Work.CORE2A.bSetup_S_le_Hhat B)))).mpr B.S0_cyclic
    refine isCyclic_of_surjective
      (MonoidHom.codRestrict ((QuotientGroup.mk' V).comp A.subtype)
        (A.map (QuotientGroup.mk' V)) (fun x => Subgroup.mem_map_of_mem _ x.2)) ?_
    rintro ⟨y, hy⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨Qhat, hQhat⟩ := Work.CORE2A.sylow_subgroupOf_Hhat B
  have hQhat' : (Qhat : Subgroup ↥B.Hhat) = K := by rw [hQhat, hK]
  let Qbar : Sylow 2 (↥B.Hhat ⧸ V) := Qhat.mapSurjective (QuotientGroup.mk'_surjective V)
  have hQbar_coe : (Qbar : Subgroup (↥B.Hhat ⧸ V)) = K.map (QuotientGroup.mk' V) := by
    rw [Sylow.coe_mapSurjective, hQhat']
  have hQbar_cyc : IsCyclic ↥(Qbar : Subgroup (↥B.Hhat ⧸ V)) := by
    rw [hQbar_coe, hKmap]
    exact hAcyc
  -- ## 2.5 `E` embeds into `↥Ĥ ⧸ V`, so its Sylow `2`-subgroups are cyclic.
  have hφinj : Function.Injective ((QuotientGroup.mk' V).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxV : ((x : ↥E) : ↥B.Hhat) ∈ V := by
      rw [← QuotientGroup.eq_one_iff]
      simpa using hx
    have hxbot : ((x : ↥E) : ↥B.Hhat) ∈ E ⊓ V := ⟨x.2, hxV⟩
    rw [hEV] at hxbot
    exact Subtype.ext (by simpa using hxbot)
  have hEcyc : ∃ Q : Sylow 2 ↥E, IsCyclic ↥(Q : Subgroup ↥E) :=
    ⟨default, isCyclic_of_isPGroup_two_of_injective _ hφinj Qbar hQbar_cyc
      (default : Sylow 2 ↥E).isPGroup'⟩
  -- ## 2.6 Contradiction from the structure of `E/Z(E)`.
  exact Work.CORE2A.false_of_isCyclic_sylow_of_center_quotient T hEcyc hoddZ hshape

end Work.CORE2A
