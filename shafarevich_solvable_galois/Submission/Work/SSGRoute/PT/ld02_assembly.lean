import Mathlib
import Submission.Work.SSGRoute.PT.mkb_ld02_core_of_h3
import Submission.Work.SSGRoute.LTD02Proved.wall_mine
import Submission.Work.SSGRoute.PTUr.mkb_core_inputs
import Submission.Work.SSGRoute.PT.isDiscreteModule_conjHom
import Submission.Work.SSGRoute.kummerBase_euler_ses_decomp
import Submission.Work.SSGRoute.PT.h3loc_decomp_subsingleton
import Submission.Work.SSGRoute.PT.HomFormReduction
import Submission.Work.SSGRoute.PTUr.htop_units
import Submission.Work.SSGRoute.PT.brOpenSubgroupDefs
import Submission.Work.SSGRoute.EulerSymm.h3loc_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The assembly of the `α²`-dévissage at `D_A`: `Deg02HomForm`

This file is the *assembly* of the `α²`-dévissage of Milne, *Arithmetic Duality Theorems*,
Theorem I.1.8 at `r = 2` for the local class formation `(D_A, \bar Ωˣ)`, at the level of the
decomposition group `D_A = SSGRoute.decomp k A` of a finite place of a number field `k`.

The pieces it assembles (all proved elsewhere in the workspace and all axiom-clean):

* the dévissage step `Work.SSGRoute.PT.alphaTwo_bijective_of_devissage`
  (`Submission/Work/SSGRoute/PT/AlphaTwoDevissageAux.lean`) along the short exact sequence
  `0 → N → Coind_U^{D_A} N → N₁ → 0`;
* the *base case* `Work.SSGRoute.PT.mkb_alphaTwo_base_of_trivAction` and its coinduced
  companion `Work.SSGRoute.PT.mkb_alphaTwo_coind_bijective`
  (`Submission/Work/SSGRoute/PT/mkb_ld02_core_of_h3.lean`), i.e. Kummer theory plus Hilbert 90 at
  the open subgroup `U = levelFixSub k Ω A K`;
* Milne's class-formation axiom **(1.1b)** on the `p`-torsion,
  `Work.SSGRoute.LTD02Proved.ltdCorH2_bijective_units_openSubgroup`
  (`Submission/Work/SSGRoute/LTD02Proved/wall_mine.lean`);
* the *first pass* (surjectivity of `α²` for the quotient `N₁`), the retraction lemmas giving the
  exactness of the dual of the invariants sequence, and the `Ext³`-vanishing input `hhtop`.

The conclusion `Work.SSGRoute.PT.ld02_alphaTwo_bijective` is the bijectivity of the cup-product
map `α²(D_A, N)`; with the Tate twist `Hom_ℤ(DualMod p (M ⊗ T), Ωˣ) ≅ M` and the `H0loc` bridge
this yields the dimension identity `dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))`, i.e. the target
`Work.SSGRoute.PT.localTatePairing_deg02`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

open Classical
open scoped TensorProduct

namespace Work.SSGRoute.PT

noncomputable section

/-- **Discreteness passes from a group to a subgroup.**  The stabiliser of an element in `↥U` is
the preimage of its stabiliser in `G`. -/
theorem ld02_isDiscreteModule_subgroup {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
    {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    (h : Work.AbsoluteKummer.IsDiscreteModule G M) :
    Work.AbsoluteKummer.IsDiscreteModule ↥U M := by
  intro m
  have hset : (MulAction.stabilizer ↥U m : Set ↥U)
      = Subtype.val ⁻¹' ((MulAction.stabilizer G m) : Set G) := by
    ext u
    exact Iff.rfl
  rw [hset]
  exact (h m).preimage continuous_subtype_val

/-- For `x ∈ levelFixSub k Ω A K` the restriction `res k K x` is trivial. -/
theorem ld02_res_eq_one_of_mem_levelFixSub
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [Normal k K]
    (A : ValuationSubring Ω) {x : ↥(SSGRoute.decomp k A)}
    (hx : x ∈ Work.SSGRoute.PT.levelFixSub k Ω A K) : SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) = 1 := by
  have hfix : (x : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun y hy => (Work.SSGRoute.PT.mem_levelFixSub).mp hx y hy
  have hmem : (x : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
    rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
      IntermediateField.restrictNormalHom_ker]
    exact hfix
  exact MonoidHom.mem_ker.mp hmem

/-- **Milne's first pass.**  For an open finite-index subgroup `U ≤ G` acting trivially on a finite
`𝔽_p`-module `N`, surjectivity of `α²(G,N)` follows from the base case at `U` and the
corestriction non-degeneracy on the `p`-torsion.  This provides the `hN₁` input of the dévissage
for the quotient `N₁ = (Coind_U^G N)/N`. -/
theorem ld02_alphaTwo_surjective_of_hcor
    (p : ℕ) [Fact p.Prime] {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N]
    (hc : Function.Bijective (fun z : {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} =>
      (⟨Work.SSGRoute.PT.corH2 U hUo C z.1, by rw [← map_nsmul, z.2, map_zero]⟩ :
        {x : Work.AbsoluteKummer.H2 G C // p • x = 0})))
    (hNp : ∀ n : N, p • n = 0)
    (htriv : ∀ (u : ↥U) (n : N), u • n = n)
    (hbaseU : Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := U) (N := N) (C := C))) :
    Function.Surjective (Work.SSGRoute.PT.alphaTwo (G := G) (N := N) (C := C)) := by
  classical
  let ι : N →+ Work.SSGRoute.PT.Coind G U N := Work.SSGRoute.PT.devissageIota (M := N) U
  have hι : Work.GroupCohomology.IsEquivariant G ι :=
    Work.SSGRoute.PT.devissageIota_equivariant (M := N) U
  have hpreι : Work.GroupCohomology.IsEquivariant G
      (Work.SSGRoute.PT.ConjHom.precomp (C := C) ι) :=
    Work.SSGRoute.PTUr.ptu_isEquivariant_conjHom_precomp ι hι
  obtain ⟨r, hr⟩ := Work.SSGRoute.PT.retraction_invariantsHom (p := p) (G := G)
    (N₁ := N) (N₂ := Work.SSGRoute.PT.Coind G U N) (φ := ι) (hφ := hι)
    (Work.SSGRoute.PT.devissageIota_injective (M := N) U)
  have hg' := Work.SSGRoute.PT.mkb_precompHom_surjective_of_retraction
    (X := Work.AbsoluteKummer.H2 G C) (Work.SSGRoute.PT.invariantsHom ι hι) r hr
  have hcoind := Work.SSGRoute.PT.mkb_alphaTwo_coind_bijective (p := p) (G := G) U hUo
    hc hNp hbaseU
  exact Work.SSGRoute.PT.alphaTwo_surjective_of_precomp
    (N₁ := N) (N₂ := Work.SSGRoute.PT.Coind G U N) ι hι hpreι hcoind.2 hg'

/-- **Milne, *ADT*, Theorem I.1.8 at `r = 2` for the decomposition group `D_A`.**  For every finite
place `A`, every finite `𝔽_p[D_A]`-module `N` whose `D_A`-action is the canonical one through
`res k K` (hypothesis `hpinN`), the cup-product map

`α² : H²(D_A, Hom_ℤ(N, Ωˣ)) → Hom_{D_A}(N, H²(D_A, Ωˣ))`

is bijective.  The inputs are the class-formation axiom **(1.1b)** on the `p`-torsion (Milne's
`inv_{D_A} ∘ cor = inv_U`, used through `ltdCorH2_bijective_units_openSubgroup`), the `Ext³`-input
`hhtop` (`H³(D_A, Hom_ℤ(N₁,Ωˣ)) = 0` for the quotient `N₁`), and the retraction/exactness
lemmas for the invariants sequence.

All the Shapiro/cup/retraction bookkeeping is formal; the only arithmetic is `(1.1b)`. -/
theorem ld02_alphaTwo_bijective
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [Finite N]
    [DistribMulAction (K ≃ₐ[k] K) N]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A) N]
    [hsc : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) N]
    (hpinN : instN = SSGRoute.decompDistribMulAction K N A)
    (hhtop : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.ConjHom
      (Work.SSGRoute.PT.devissageM1 (M := N) (Work.SSGRoute.PT.levelFixSub k Ω A K))
      (Additive (Units Ω))) ↥(SSGRoute.decomp k A))) :
    Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥(SSGRoute.decomp k A)) (N := N)
      (C := Additive (Units Ω))) := by
  classical
  -- ### the level-`K` subgroup of the decomposition group
  set U : Subgroup ↥(SSGRoute.decomp k A) := Work.SSGRoute.PT.levelFixSub k Ω A K with hUdef
  have hUeq : U = (K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf (SSGRoute.decomp k A) := by
    rw [hUdef]
    ext x
    simp only [Work.SSGRoute.PT.levelFixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A)) := by
    rw [hUeq]
    exact (Work.SSGRoute.PT.decompK_subgroupOf_facts k Ω K A hA).1
  have hUfi : U.FiniteIndex := by
    rw [hUeq]
    exact (Work.SSGRoute.PT.decompK_subgroupOf_facts k Ω K A hA).2.1
  haveI := hUfi
  haveI : Fintype (↥(SSGRoute.decomp k A) ⧸ U) := by
    rw [hUeq]
    exact (Work.SSGRoute.PT.decompK_subgroupOf_facts k Ω K A hA).2.2.some
  have hsubeq : (K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf (SSGRoute.decomp k A)
      = (K.fixingSubgroup).subgroupOf (SSGRoute.decomp k A) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  haveI hUnorm : U.Normal := by
    have hKnorm : (K.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois K).mpr (inferInstance : IsGalois k K)
    rw [hUeq, hsubeq]
    exact Subgroup.Normal.subgroupOf hKnorm _
  -- ### the coefficient module
  have hpN : ∀ x : N, p • x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]
  have htrivN : ∀ (u : ↥U) (n : N), u • n = n := by
    intro u n
    show (u : ↥(SSGRoute.decomp k A)) • n = n
    rw [hpinN]
    show SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • n = n
    rw [ld02_res_eq_one_of_mem_levelFixSub k Ω K A u.2, one_smul]
  -- ### discreteness
  haveI hMd : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A) N :=
    Work.SSGRoute.isDiscreteModule_decomp_of_compat k Ω K A N (fun h m => by rw [hpinN]; rfl)
  haveI hMUd : Work.AbsoluteKummer.IsDiscreteModule ↥U N := ld02_isDiscreteModule_subgroup hMd
  haveI hCd : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)) :=
    Work.SSGRoute.PTembedding.MupCard.isDiscreteModule_decomp_addUnits (k := k) (Ω := Ω) A
  haveI hDcoind : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.Coind ↥(SSGRoute.decomp k A) U N) :=
    Work.SSGRoute.PT.isDiscreteModule_coind U hUo hMUd
  haveI hDm1 : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.devissageM1 (M := N) U) :=
    Work.SSGRoute.PT.devissage_isDiscreteModule_m1 U hDcoind
  haveI hDN : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom N (Additive (Units Ω))) :=
    Work.SSGRoute.PT.isDiscreteModule_conjHom hMd hCd
  haveI hDCo : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.PT.Coind ↥(SSGRoute.decomp k A) U N)
        (Additive (Units Ω))) :=
    Work.SSGRoute.PTUr.ptu_isDiscreteModule_conjHom_coind U hUo hMUd hCd
  haveI hDM1 : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.PT.devissageM1 (M := N) U)
        (Additive (Units Ω))) :=
    Work.SSGRoute.PTUr.ptu_isDiscreteModule_conjHom_m1 U hDm1 hCd
  -- ### the dévissage short exact sequence
  let S := Work.SSGRoute.PT.AKZmodLin.devissageSESDef
    (M := N) U hUo hMd hMUd
  have hpreφ : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom.precomp (C := Additive (Units Ω)) S.iota) :=
    Work.SSGRoute.PTUr.ptu_isEquivariant_conjHom_precomp S.iota S.iota_equivariant
  have hpreψ : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom.precomp (C := Additive (Units Ω)) S.pi) :=
    Work.SSGRoute.PTUr.ptu_isEquivariant_conjHom_precomp S.pi S.pi_equivariant
  have hcompS : S.pi.comp S.iota = 0 := by
    ext x
    show S.pi (S.iota x) = 0
    have hx : S.iota x ∈ S.pi.ker := by rw [← S.range_iota_eq_ker_pi]; exact ⟨x, rfl⟩
    simpa using hx
  have hker_le : S.pi.ker ≤ S.iota.range := by rw [← S.range_iota_eq_ker_pi]
  haveI hAlgCl : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- ### `htop` from the vanishing of `H³`
  have htop : Function.Surjective
      (Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.ConjHom.precomp (C := Additive (Units Ω)) S.iota)
        hpreφ) := by
    obtain ⟨S', hS'ι, hS'π⟩ :=
      Work.SSGRoute.PT.shortExactSeq_conjHom_with_maps S hDM1 hDCo hDN
    have hsurj : Function.Surjective
        (Work.AbsoluteKummer.mapH2 S'.pi S'.pi_equivariant) :=
      Work.SSGRoute.PT.mkb_mapH2_surjective_of_subsingleton_H3 S' hhtop
    have hpi : S'.pi = Work.SSGRoute.PT.ConjHom.precomp (C := Additive (Units Ω)) S.iota :=
      AddMonoidHom.ext hS'π
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, ((Work.SSGRoute.PT.AlphaTwoCoind.mapH2_apply_eq_of_eq S'.pi
      (Work.SSGRoute.PT.ConjHom.precomp (C := Additive (Units Ω)) S.iota)
      S'.pi_equivariant hpreφ hpi x).symm).trans hx⟩
  -- ### the retraction inputs
  have hbot : (Work.SSGRoute.PT.precompHom (X := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Additive (Units Ω))) (Work.SSGRoute.PT.invariantsHom S.iota S.iota_equivariant)).ker
      ≤ (Work.SSGRoute.PT.precompHom (X := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Additive (Units Ω))) (Work.SSGRoute.PT.invariantsHom S.pi S.pi_equivariant)).range := by
    have hfg : (Work.SSGRoute.PT.invariantsHom S.iota S.iota_equivariant).range
        = (Work.SSGRoute.PT.invariantsHom S.pi S.pi_equivariant).ker :=
      Work.SSGRoute.PT.range_invariantsHom_eq_ker (G := ↥(SSGRoute.decomp k A))
        S.iota S.pi S.iota_equivariant S.pi_equivariant
        S.iota_injective (fun x => by simpa using DFunLike.congr_fun hcompS x) hker_le
    obtain ⟨r, hr⟩ := Work.SSGRoute.PT.retraction_range_invariantsHom (p := p)
      (G := ↥(SSGRoute.decomp k A)) (ψ := S.pi) S.pi_equivariant
    exact Work.SSGRoute.PT.mkb_precompHom_ker_le_range_of_retraction _ _ hfg r hr
  have hg' : Function.Surjective
      (Work.SSGRoute.PT.precompHom (X := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Additive (Units Ω))) (Work.SSGRoute.PT.invariantsHom S.iota S.iota_equivariant)) := by
    obtain ⟨r, hr⟩ := Work.SSGRoute.PT.retraction_invariantsHom (p := p)
      (G := ↥(SSGRoute.decomp k A)) S.iota S.iota_equivariant S.iota_injective
    exact Work.SSGRoute.PT.mkb_precompHom_surjective_of_retraction
      (X := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
      (Work.SSGRoute.PT.invariantsHom S.iota S.iota_equivariant) r hr
  -- ### the first pass for the quotient module
  let N₁ := Work.SSGRoute.PT.devissageM1 (M := N) U
  have htrivM1 : ∀ (u : ↥U) (q : N₁), u • q = q :=
    Work.SSGRoute.PTUr.ptu_devissageM1_sub_smul_eq U htrivN
  have hpM1 : ∀ q : N₁, p • q = 0 := by
    intro q
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p q, ZMod.natCast_self, zero_smul]
  haveI hfinM1 : Finite N₁ :=
    Work.SSGRoute.PTUr.ptu_finite_devissageM1 (M := N) U
  have hbaseM1 := Work.SSGRoute.PT.mkb_alphaTwo_base_of_trivAction p k Ω A hA U hUo N₁ htrivM1
  have hN₁ : Function.Surjective (Work.SSGRoute.PT.alphaTwo (G := ↥(SSGRoute.decomp k A))
      (N := N₁) (C := Additive (Units Ω))) :=
    ld02_alphaTwo_surjective_of_hcor (p := p) (G := ↥(SSGRoute.decomp k A))
      (C := Additive (Units Ω)) U hUo N₁
      (Work.SSGRoute.LTD02Proved.ltdCorH2_bijective_units_openSubgroup p k Ω A hA U hUo)
      hpM1 htrivM1 hbaseM1
  -- ### the base case at the coinduced module
  have hbase := Work.SSGRoute.PT.mkb_alphaTwo_base_of_trivAction p k Ω A hA U hUo N htrivN
  have hN₂ := Work.SSGRoute.PT.mkb_alphaTwo_coind_bijective (p := p)
    (G := ↥(SSGRoute.decomp k A)) U hUo
    (Work.SSGRoute.LTD02Proved.ltdCorH2_bijective_units_openSubgroup p k Ω A hA U hUo)
    hpN hbase
  -- ### the dévissage
  have hcomp' : ∀ x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))),
      (Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.ConjHom.precomp (C := Additive (Units Ω))
          S.iota) hpreφ)
        ((Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.ConjHom.precomp (C := Additive (Units Ω))
          S.pi) hpreψ) x) = 0 :=
    Work.SSGRoute.PT.mkb_hcomp_of_comp_eq_zero S.iota S.pi hcompS hpreφ hpreψ
  exact Work.SSGRoute.PT.alphaTwo_bijective_of_devissage (C := Additive (Units Ω))
    S.iota S.iota_equivariant hpreφ S.pi S.pi_equivariant hpreψ hcomp' htop hbot hg' hN₂ hN₁

/-- **The `H³`-vanishing for a finite coefficient module on which the level subgroup acts
trivially** (Milne, *ADT*, Lemma 1.9): if the finite `𝔽_p[D_A]`-module `N₁` is fixed by
`U = levelFixSub k Ω A K = D_A ∩ Gal(Ω/K)`, then `H³(D_A, Hom_ℤ(N₁, Ωˣ)) = 0`.

The `D_A`-action on `Hom_ℤ(N₁,Ωˣ)` factors through the finite quotient
`D_A/U ≅ im(res k K) ⊆ Gal(K/k)`: `U` acts trivially on `N₁` by hypothesis and on `μ_p = Ωˣ[p]`
because `ζ ∈ K`; so the vanishing reduces to `cd_p(D_A) ≤ 2` for finite coefficients
(`Work.SSGRoute.EulerSymm.h3loc_subsingleton`) through
`Work.SSGRoute.PT.h3_H3_subsingleton_of_image`.

This is the `hhtop` input of `ld02_alphaTwo_bijective`.  (The proof is the one of
`Submission/Work/SSGRoute/LTD02Proved/Htop.lean`, kept here so that this module does not depend on
`PT.localDuality02`, which imports the target.) -/
theorem ld02_h3_units_conjHom_of_trivAction
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (N₁ : Type) [AddCommGroup N₁] [Module (ZMod p) N₁]
    [DistribMulAction ↥(SSGRoute.decomp k A) N₁]
    [SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) N₁] [Finite N₁]
    (htriv : ∀ (u : ↥(Work.SSGRoute.PT.levelFixSub k Ω A K)) (n : N₁), u • n = n) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)))
      ↥(SSGRoute.decomp k A)) := by
  classical
  -- ## the primitive `p`-th root of unity
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero
  let ζu : Ωˣ := Units.mk0 ζ hζ0
  have hζu : IsPrimitiveRoot ζu p :=
    (IsPrimitiveRoot.coe_units_iff (ζ := ζu)).mp (by rw [Units.val_mk0]; exact hζ)
  have hζuK : (ζu : Ω) ∈ K := by rw [Units.val_mk0]; exact hζK
  haveI hNZ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hOneLt : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  -- ## the values of elements of `V = Hom_ℤ(N₁, Ωˣ)` are `p`-torsion
  have hNp : ∀ n : N₁, p • n = 0 := by
    intro n
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p n, ZMod.natCast_self, zero_smul]
  -- ## `U` acts trivially on `V`
  have hfix : ∀ (g : ↥(Work.SSGRoute.PT.levelFixSub k Ω A K)) (y : Additive (Units Ω)),
      p • y = 0 → g • y = y := by
    intro g y hy
    have hgK : ((g : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact fun z hz => (Work.SSGRoute.PT.mem_levelFixSub).mp g.2 z hz
    exact Work.SSGRoute.PTUr.ptu_ptorsion_units_smul_eq (k := k) K ζu hζu hζuK _ hgK y hy
  have htrivV : ∀ (u : ↥(Work.SSGRoute.PT.levelFixSub k Ω A K))
      (v : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))), u • v = v :=
    fun u v =>
      Work.SSGRoute.PTUr.ptu_conjHom_units_smul_eq_of_fix hfix (fun g n => htriv g n) hNp u v
  -- ## finiteness of `V`: every hom out of an exponent-`p` module lands in `μ_p`
  have hmemzp : ∀ (f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) (n : N₁),
      Additive.toMul (f n) ∈ Subgroup.zpowers ζu := by
    intro f n
    have hp : p • f n = 0 := by rw [← map_nsmul, hNp n, map_zero]
    have hpow : Additive.toMul (f n) ^ p = 1 := by
      simpa [toMul_nsmul] using congrArg Additive.toMul hp
    rw [hζu.zpowers_eq]
    exact (mem_rootsOfUnity p (Additive.toMul (f n))).2 hpow
  haveI hfinμ : Finite ↥(Subgroup.zpowers ζu) :=
    Finite.of_injective (fun u => hζu.zmodEquivZPowers.symm (Additive.ofMul u)) (by
      intro a b hab
      have h := hζu.zmodEquivZPowers.symm.injective hab
      simpa using congrArg (fun x : Additive ↥(Subgroup.zpowers ζu) => Additive.toMul x) h)
  haveI hFintypeN₁ : Fintype N₁ := Fintype.ofFinite N₁
  haveI hFintypeμ : Fintype ↥(Subgroup.zpowers ζu) := Fintype.ofFinite _
  haveI hfinV : Finite (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    Finite.of_injective
      (fun f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)) =>
        fun n : N₁ => (⟨Additive.toMul (f n), hmemzp f n⟩ : ↥(Subgroup.zpowers ζu)))
      (by
        intro f g h
        refine Work.SSGRoute.PT.ConjHom.ext_apply (fun n => ?_)
        have h' : (⟨Additive.toMul (f n), hmemzp f n⟩ : ↥(Subgroup.zpowers ζu))
            = ⟨Additive.toMul (g n), hmemzp g n⟩ := congrFun h n
        have h'' : Additive.toMul (f n) = Additive.toMul (g n) := congrArg Subtype.val h'
        simpa using congrArg Additive.ofMul h'')
  -- ## the pointwise `𝔽_p`-module structure on `V`
  have hpV : ∀ f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)), p • f = 0 := by
    intro f
    refine Work.SSGRoute.PT.ConjHom.ext_apply (fun n => ?_)
    show p • f n = 0
    rw [← map_nsmul, hNp n, map_zero]
  have hmod : ∀ (m : ℕ) (f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))),
      (m % p) • f = m • f := by
    intro m f
    conv_rhs => rw [← Nat.mod_add_div m p]
    rw [add_nsmul, mul_nsmul, hpV f, smul_zero, add_zero]
  letI : Module (ZMod p) (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    { smul := fun c f => c.val • f
      one_smul := fun f => by
        show (1 : ZMod p).val • f = f
        rw [ZMod.val_one p, one_nsmul]
      mul_smul := fun c d f => by
        show (c * d).val • f = c.val • (d.val • f)
        rw [ZMod.val_mul, hmod (c.val * d.val) f, mul_nsmul']
      smul_zero := fun c => nsmul_zero _
      zero_smul := fun f => by
        show (0 : ZMod p).val • f = 0
        rw [ZMod.val_zero, zero_nsmul]
      add_smul := fun c d f => by
        show (c + d).val • f = c.val • f + d.val • f
        rw [ZMod.val_add, hmod (c.val + d.val) f, add_nsmul]
      smul_add := fun c f g => nsmul_add _ _ _ }
  -- ## the image of the decomposition group in `Gal(K/k)` and a chosen section
  set im : Subgroup (K ≃ₐ[k] K) := (SSGRoute.decomp k A).map (SSGRoute.res k K) with himdef
  let lift : ↥im → ↥(SSGRoute.decomp k A) := fun g =>
    ⟨(Subgroup.mem_map.mp g.2).choose, (Subgroup.mem_map.mp g.2).choose_spec.1⟩
  have hlift (g : ↥im) :
      SSGRoute.res k K (((lift g : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)) = (g : K ≃ₐ[k] K) :=
    (Subgroup.mem_map.mp g.2).choose_spec.2
  have hmemU : ∀ (x : ↥(SSGRoute.decomp k A)),
      SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) = 1 → x ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := by
    intro x hx
    rw [Work.SSGRoute.PT.levelFixSub, Subgroup.mem_subgroupOf]
    have hmem : (x : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := MonoidHom.mem_ker.mpr hx
    rwa [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
      IntermediateField.restrictNormalHom_ker] at hmem
  -- ## the action of `im` on `V`, transported along the chosen section
  letI imAction : DistribMulAction ↥im
      (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    { smul := fun g v => (lift g) • v
      one_smul := fun v => by
        have h1 : (lift (1 : ↥im) : ↥(SSGRoute.decomp k A))
            ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := hmemU (lift 1) (by rw [hlift 1]; rfl)
        show (lift (1 : ↥im)) • v = v
        exact htrivV ⟨lift 1, h1⟩ v
      mul_smul := fun g h v => by
        have hmem : (lift g * lift h)⁻¹ * lift (g * h)
            ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := by
          refine hmemU _ ?_
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [map_mul, map_inv, map_mul, hlift, hlift, hlift]
          simp only [Subgroup.coe_mul]
          group
        have h3 : ((lift g * lift h)⁻¹ * lift (g * h)) • v = v := htrivV ⟨_, hmem⟩ v
        have h4 : ((lift g * lift h) * ((lift g * lift h)⁻¹ * lift (g * h))) • v
            = (lift g * lift h) • v := by
          rw [mul_smul, h3]
        have h5 : lift (g * h) • v = (lift g * lift h) • v := by
          simpa only [mul_inv_cancel_left] using h4
        show lift (g * h) • v = (lift g) • ((lift h) • v)
        rw [h5, mul_smul]
      smul_zero := fun g => smul_zero (lift g)
      smul_add := fun g v w => smul_add (lift g) v w }
  haveI : SMulCommClass ↥im (ZMod p)
      (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    ⟨fun g c f => by
      show g • (c.val • f) = c.val • (g • f)
      induction c.val with
      | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
      | succ k ih => rw [succ_nsmul, smul_add, ih, succ_nsmul]⟩
  -- ## the compatibility of the two actions and the vanishing of `H³`
  have hcompat : ∀ (σ : ↥(SSGRoute.decomp k A))
      (v : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))),
      σ • v = (⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
        Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩ : ↥im) • v := by
    intro σ v
    show σ • v = (lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
      Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩) • v
    have hmem : (lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)⁻¹ * σ
        ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := by
      refine hmemU _ ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [map_mul, map_inv, hlift]
      group
    have h3 : ((lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)⁻¹ * σ) • v = v := htrivV ⟨_, hmem⟩ v
    have h4 : ((lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)
        * ((lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)⁻¹ * σ)) • v
        = (lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩) • v := by
      rw [mul_smul, h3]
    simpa only [mul_inv_cancel_left] using h4
  exact Work.SSGRoute.PT.h3_H3_subsingleton_of_image p k Ω K A hA
    (Work.SSGRoute.EulerSymm.h3loc_subsingleton p k Ω K A hA)
    (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) hcompat

/-- **The `hhtop` input of the dévissage in the form needed by `ld02_alphaTwo_bijective`**: for a
finite `𝔽_p[D_A]`-module `N` whose action is the canonical one through `res k K`, the third
cohomology of `D_A` with coefficients in `Hom_ℤ(N₁, Ωˣ)` vanishes, where
`N₁ = devissageM1 (levelFixSub k Ω A K) N`. -/
theorem ld02_hhtop_devissageM1
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [Finite N]
    [DistribMulAction (K ≃ₐ[k] K) N] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A) N]
    (hpinN : instN = SSGRoute.decompDistribMulAction K N A) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.ConjHom
      (Work.SSGRoute.PT.devissageM1 (M := N) (Work.SSGRoute.PT.levelFixSub k Ω A K))
      (Additive (Units Ω))) ↥(SSGRoute.decomp k A)) := by
  classical
  let U : Subgroup ↥(SSGRoute.decomp k A) := Work.SSGRoute.PT.levelFixSub k Ω A K
  haveI hUnorm : U.Normal := by
    have hKnorm : (K.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois K).mpr (inferInstance : IsGalois k K)
    show ((K.fixingSubgroup).subgroupOf (SSGRoute.decomp k A)).Normal
    exact Subgroup.Normal.subgroupOf hKnorm _
  have hpinG : ∀ (g : ↥(SSGRoute.decomp k A)) (n : N),
      g • n = SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • n := by
    intro g n
    rw [hpinN]
    rfl
  -- the level subgroup has finite index in `D_A`, and `D_A` acts `𝔽_p`-linearly on `N`
  haveI hUfi : U.FiniteIndex := by
    have hUeq : U = (K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf
        (SSGRoute.decomp k A) := by
      ext x
      simp only [Work.SSGRoute.PT.levelFixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
    rw [hUeq]
    exact (Work.SSGRoute.PT.decompK_subgroupOf_facts k Ω K A hA).2.1
  haveI hscN : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) N :=
    ⟨fun g c n => by
      rw [hpinG g (c • n), hpinG g n]
      exact smul_comm (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) c n⟩
  -- the triviality of the `U`-action on `N`, hence on the cokernel
  have htrivN : ∀ (u : ↥U) (n : N), u • n = n := by
    intro u n
    show (u : ↥(SSGRoute.decomp k A)) • n = n
    rw [hpinG]
    show SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • n = n
    rw [ld02_res_eq_one_of_mem_levelFixSub k Ω K A u.2, one_smul]
  have htrivM1 : ∀ (u : ↥U)
      (q : Work.SSGRoute.PT.devissageM1 (M := N) U), u • q = q :=
    Work.SSGRoute.PTUr.ptu_devissageM1_sub_smul_eq U htrivN
  haveI hfinM1 : Finite (Work.SSGRoute.PT.devissageM1 (M := N) U) :=
    Work.SSGRoute.PTUr.ptu_finite_devissageM1 (M := N) U
  exact ld02_h3_units_conjHom_of_trivAction p k Ω K ζ hζ hζK A hA
    (Work.SSGRoute.PT.devissageM1 (M := N) U) htrivM1

/-- **The dimension form of local Tate duality in degrees `0` and `2` at `D_A`** (Milne, *ADT*,
Cor. I.2.3 at `r = 0`).  With the Tate-dual coefficient module `N = M^∨(1) = DualMod p (M ⊗ T)` and
the bijectivity of `α²(D_A, N)` (`ld02_alphaTwo_bijective`, whose `Ext³`-input is `ld02_hhtop`, i.e.
`cd_p(D_A) ≤ 2`), the Tate twist `Hom_ℤ(N, Ωˣ) ≅ M` and the identification
`N^{D_A} ≅ H⁰_loc(D_A, N^∨(1))` turn the pairing into the dimension identity
`dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))`; the counting step uses the `p`-torsion of the local Brauer
group (`Nakayama.br_pTorsion`).  This is
`Work.SSGRoute.PT.finrank_eq_of_alphaTwo_bijective`. -/
theorem ld02_dimform
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
  intro A hA M _ _ _ _ _
  haveI hTfin : Finite T := Work.SSGRoute.finite_of_finrank_eq_one T hT.1
  haveI hMTfin : Finite (TensorProduct (ZMod p) M T) := Work.SSGRoute.finite_tensor M T
  haveI hNfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Work.SSGRoute.finite_dualMod (TensorProduct (ZMod p) M T)
  letI : DistribMulAction ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    SSGRoute.decompDistribMulAction K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A
  haveI hscN : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    ⟨fun g c n => by
      show SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) •
          (c • n) = c • (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • n)
      exact smul_comm (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) c n⟩
  exact Work.SSGRoute.PT.finrank_eq_of_alphaTwo_bijective p k Ω K ζ hζ hζK T hT A hA M
    (instN := _) (hpinN := rfl)
    (h := Work.SSGRoute.PT.ld02_alphaTwo_bijective p k Ω K A hA _
      (instN := _) (hsc := hscN) (hpinN := rfl)
      (Work.SSGRoute.PT.ld02_hhtop_devissageM1 p k Ω K ζ hζ hζK A hA
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (instN := _) rfl))

end

end Work.SSGRoute.PT
