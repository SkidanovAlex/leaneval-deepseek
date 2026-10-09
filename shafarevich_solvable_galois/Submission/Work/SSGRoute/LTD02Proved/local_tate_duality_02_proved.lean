import Mathlib
import Submission.Work.SSGRoute.LTD02Proved.Basic
import Submission.Work.SSGRoute.LTD02Proved.Htop
import Submission.Work.SSGRoute.LTD02Proved.wall_mine
import Submission.Work.SSGRoute.PT.corH2_bijective_units_openSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open Classical

namespace Work.SSGRoute.LTD02Proved

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

noncomputable section

/-- **The `hhtop` input of the `α²`-dévissage, from the vanishing of `H³` at the level subgroup.**

With `U = levelFixSub k Ω A K = D_A ∩ Gal(Ω/K)` and `N = M^∨(1) = DualMod p (M ⊗ T)`, the module
`N₁ = devissageM1 U N = Coind_U^{D_A} N ⧸ N` is a finite `𝔽_p[D_A]`-module on which `U` acts
trivially (`ptu_devissageM1_sub_smul_eq`), so `H³(D_A, Hom_ℤ(N₁, Ωˣ)) = 0` by
`Work.SSGRoute.LTD02Proved.h3_units_conjHom_of_trivAction`. -/
theorem hhtop_of_trivAction
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))]
    (hpinN : instN = SSGRoute.decompDistribMulAction K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A)
    [hsc : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))] :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.ConjHom
      (Work.SSGRoute.PT.devissageM1 (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Work.SSGRoute.PT.levelFixSub k Ω A K)) (Additive (Units Ω))) ↥(SSGRoute.decomp k A)) := by
  classical
  -- the level subgroup written as `D_A ∩ Gal(Ω/K)`
  have hUeq : Work.SSGRoute.PT.levelFixSub k Ω A K
      = (K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf (SSGRoute.decomp k A) := by
    rw [Work.SSGRoute.PT.levelFixSub]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  -- it is normal in `D_A`, being `D_A ∩ Gal(Ω/K)` for the Galois `K/k`
  have hUnorm : (Work.SSGRoute.PT.levelFixSub k Ω A K).Normal := by
    have hsubeq : (K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf (SSGRoute.decomp k A)
        = (K.fixingSubgroup).subgroupOf (SSGRoute.decomp k A) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    have hKnorm : (K.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois K).mpr (inferInstance : IsGalois k K)
    rw [hUeq, hsubeq]
    exact Subgroup.Normal.subgroupOf hKnorm _
  haveI := hUnorm
  -- it has finite index in `D_A`
  haveI hUfi : (Work.SSGRoute.PT.levelFixSub k Ω A K).FiniteIndex := by
    rw [hUeq]
    exact (Work.SSGRoute.PT.decompK_subgroupOf_facts k Ω K A hA).2.1
  have htrivN : ∀ (u : ↥(Work.SSGRoute.PT.levelFixSub k Ω A K))
      (n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)), u • n = n := by
    intro u n
    show (u : ↥(SSGRoute.decomp k A)) • n = n
    rw [hpinN]
    show SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • n = n
    rw [res_eq_one_of_mem_levelFixSub k Ω K A u.2, one_smul]
  -- the quotient `N₁ = devissageM1 U N` is finite
  haveI hTfin : Finite T := Work.SSGRoute.finite_of_finrank_eq_one T hT.1
  haveI hMTfin : Finite (TensorProduct (ZMod p) M T) := Work.SSGRoute.finite_tensor M T
  haveI hNfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Work.SSGRoute.finite_dualMod (TensorProduct (ZMod p) M T)
  haveI hfinN₁ : Finite (Work.SSGRoute.PT.devissageM1
      (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (Work.SSGRoute.PT.levelFixSub k Ω A K)) :=
    Work.SSGRoute.PTUr.ptu_finite_devissageM1
      (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (Work.SSGRoute.PT.levelFixSub k Ω A K)
  exact h3_units_conjHom_of_trivAction p k Ω K ζ hζ hζK A hA
    (Work.SSGRoute.PT.devissageM1 (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (Work.SSGRoute.PT.levelFixSub k Ω A K))
    (Work.SSGRoute.PTUr.ptu_devissageM1_sub_smul_eq (Work.SSGRoute.PT.levelFixSub k Ω A K) htrivN)

/-- **The `α²`-bijectivity of Milne's dévissage at a decomposition group.**

This is Milne, *Arithmetic Duality Theorems*, Theorem I.1.8 at `r = 2` for the local Galois group
`D_A = decomp k A`: the cup-product map

`α² : H²(D_A, Hom_ℤ(N, Ωˣ)) → (N^{D_A} →⁺ H²(D_A, Ωˣ))`,   `N = M^∨(1) = DualMod p (M ⊗ T)`,

is bijective.  The proof is the dévissage along `0 → N → Coind_U^{D_A} N → N₁ → 0` with
`U = levelFixSub k Ω A K = D_A ∩ Gal(Ω/K)`, whose inputs are the arithmetic hypothesis `hc`
(Milne, *ADT*, (1.1b) on the `p`-torsion) and the vanishing of `H³` supplied by
`hhtop_of_trivAction`; the remaining Shapiro/retraction steps are formal. -/
theorem alphaTwo_bijective_of_hc
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))]
    (hpinN : instN = SSGRoute.decompDistribMulAction K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A)
    (hc : ∀ (U : Subgroup ↥(SSGRoute.decomp k A)) (hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
      [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)],
      Function.Bijective (fun z : {x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • x = 0} =>
        (⟨Work.SSGRoute.PT.corH2 U hUo (Additive (Units Ω)) z.1,
          by rw [← map_nsmul, z.2, map_zero]⟩ :
          {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) // p • x = 0}))) :
    Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥(SSGRoute.decomp k A))
      (N := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (C := Additive (Units Ω))) := by
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
  haveI hTfin : Finite T := Work.SSGRoute.finite_of_finrank_eq_one T hT.1
  haveI hMTfin : Finite (TensorProduct (ZMod p) M T) := Work.SSGRoute.finite_tensor M T
  haveI hNfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Work.SSGRoute.finite_dualMod (TensorProduct (ZMod p) M T)
  have hpN : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T), p • x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]
  have htrivN : ∀ (u : ↥U) (n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      u • n = n := by
    intro u n
    show (u : ↥(SSGRoute.decomp k A)) • n = n
    rw [hpinN]
    show SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • n = n
    rw [res_eq_one_of_mem_levelFixSub k Ω K A u.2, one_smul]
  haveI hscN : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    ⟨fun g c n => by
      have hgen : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          g • x = SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • x := fun x => by rw [hpinN]; rfl
      rw [hgen (c • n), hgen n]
      exact smul_comm (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) c n⟩
  -- ### discreteness
  haveI hMd : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Work.SSGRoute.isDiscreteModule_decomp_of_compat k Ω K A _ (fun h m => by rw [hpinN]; rfl)
  haveI hMUd : Work.AbsoluteKummer.IsDiscreteModule ↥U
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := isDiscreteModule_subgroup hMd
  haveI hCd : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)) :=
    Work.SSGRoute.PTembedding.MupCard.isDiscreteModule_decomp_addUnits (k := k) (Ω := Ω) A
  haveI hDcoind : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.Coind ↥(SSGRoute.decomp k A) U
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) :=
    Work.SSGRoute.PT.isDiscreteModule_coind U hUo hMUd
  haveI hDm1 : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.devissageM1 (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) U) :=
    Work.SSGRoute.PT.devissage_isDiscreteModule_m1 U hDcoind
  haveI hDN : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Additive (Units Ω))) :=
    Work.SSGRoute.PT.isDiscreteModule_conjHom hMd hCd
  haveI hDCo : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.PT.Coind ↥(SSGRoute.decomp k A) U
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) (Additive (Units Ω))) :=
    Work.SSGRoute.PTUr.ptu_isDiscreteModule_conjHom_coind U hUo hMUd hCd
  haveI hDM1 : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.PT.ConjHom
        (Work.SSGRoute.PT.devissageM1 (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) U)
        (Additive (Units Ω))) :=
    Work.SSGRoute.PTUr.ptu_isDiscreteModule_conjHom_m1 U hDm1 hCd
  -- ### the dévissage short exact sequence
  let S := Work.SSGRoute.PT.AKZmodLin.devissageSESDef
    (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) U hUo hMd hMUd
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
  -- ### the `H³`-vanishing input, from `hhtop_of_trivAction`
  have hhtop := hhtop_of_trivAction p k Ω K ζ hζ hζK T hT A hA M (instN := instN) hpinN
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
  let N₁ := Work.SSGRoute.PT.devissageM1
    (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) U
  have htrivM1 : ∀ (u : ↥U) (q : N₁), u • q = q :=
    Work.SSGRoute.PTUr.ptu_devissageM1_sub_smul_eq U htrivN
  have hpM1 : ∀ q : N₁, p • q = 0 := by
    intro q
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p q, ZMod.natCast_self, zero_smul]
  haveI hfinM1 : Finite N₁ :=
    Work.SSGRoute.PTUr.ptu_finite_devissageM1 (M := Work.SSGRoute.DualMod p
      (TensorProduct (ZMod p) M T)) U
  have hbaseM1 := Work.SSGRoute.PT.mkb_alphaTwo_base_of_trivAction p k Ω A hA U hUo N₁ htrivM1
  have hN₁ : Function.Surjective (Work.SSGRoute.PT.alphaTwo (G := ↥(SSGRoute.decomp k A))
      (N := N₁) (C := Additive (Units Ω))) :=
    alphaTwo_surjective_of_hcor (p := p) (G := ↥(SSGRoute.decomp k A)) (C := Additive (Units Ω))
      U hUo N₁ (hc U hUo) hpM1 htrivM1 hbaseM1
  -- ### the base case at the coinduced module
  have hbase := Work.SSGRoute.PT.mkb_alphaTwo_base_of_trivAction p k Ω A hA U hUo
    (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) htrivN
  have hN₂ := Work.SSGRoute.PT.mkb_alphaTwo_coind_bijective (p := p)
    (G := ↥(SSGRoute.decomp k A)) U hUo (hc U hUo) hpN hbase
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

/-! ## The reduction of the target to the arithmetic input `hc`

Everything on the formal side is now in place, including the `H³`-vanishing `hhtop` (proved above in
`hhtop_of_trivAction`).  The remaining input is

* `hc` — Milne, *ADT*, (1.1b): the corestriction `cor : H²(U, Ωˣ) → H²(D_A, Ωˣ)` is bijective on
  the `p`-torsion, for every open subgroup `U ≤ D_A = decomp k A`;

an arithmetic statement of local class field theory, formalised separately
(`Work.SSGRoute.PT.corH2_bijective_units_openSubgroup`). -/

/-- **Tate duality in degrees `0` and `2` at `D_A`, from the arithmetic input `hc`.** -/
theorem target_of_hc
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hc : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (U : Subgroup ↥(SSGRoute.decomp k A)) (hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
      [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)],
      Function.Bijective (fun z : {x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • x = 0} =>
        (⟨Work.SSGRoute.PT.corH2 U hUo (Additive (Units Ω)) z.1,
          by rw [← map_nsmul, z.2, map_zero]⟩ :
          {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) // p • x = 0}))) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) ∧
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A))) := by
  refine target_from_alphaTwo p k Ω K ζ hζ hζK T hT ?_
  intro A hA M _ _ _ _ _ instN hpinN
  exact alphaTwo_bijective_of_hc p k Ω K ζ hζ hζK T hT A hA M
    (instN := instN) (hpinN := hpinN) (hc A hA)

/-- **Tate duality in degrees `0` and `2` for a decomposition group** (Milne, *Arithmetic Duality
Theorems*, Cor. I.2.3 at `r = 0`): for every finite place `A` and every finite
`𝔽_p[Gal(K/k)]`-module `M`,

`dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))`   and   `dim H²(D_A, M^∨(1)) = dim H⁰(D_A, M)`,

where `M^∨(1) = DualMod p (M ⊗ T)`. -/
theorem local_tate_duality_02_proved
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) ∧
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A))) :=
  target_of_hc p k Ω K ζ hζ hζK T hT
    (fun A hA U hUo _ _ => ltdCorH2_bijective_units_openSubgroup p k Ω A hA U hUo)


end

end Work.SSGRoute.LTD02Proved
