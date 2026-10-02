import Mathlib
import Submission.Work.Tubular.LocalDegreeAll
import Submission.Work.Tubular.LocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local degree class at the collapse class is a *generator*

`Work.Tubular.exists_localDegree_at_collapseRelK8_of_connected` produces a class
`U ∈ H^k(ν, ν∖0)` (with `ν = NormalTotal E`) which *implements the local degree*, i.e. which
satisfies

`⟨x ⌣ U, c⟩ = ⟨z^* x, [V]⟩`   for all `x ∈ H⁸(ν)`,

where `c = collapseRelK8` is the collapse class.  For the Pontryagin–Thom chapter one needs `U` to
be a **generator** of the (free, rank one) module `H^k(ν, ν∖0)` — it is the Thom class of the normal
bundle, and as such it must be a `ℤ`-basis element of the relative cohomology of the Thom pair.

Both properties hold for the *same* class, and the reason is visible in the construction of
`exists_localDegree_at_collapseRelK8`: the class produced there is the image under the
homeomorphism-of-pairs `ψ : Z.TotalSpace ≅ ν` (whose induced map on relative cohomology is a
bijection, `Work.Thom.bijective_relCohMap_of_homeomorphA`) of `±UZ₀`, where `UZ₀` is a generator of
`H^k(Z.TotalSpace, Z.TotalSpace∖0)` produced by `Work.ThomBordism.tubeLocalDegreeGlobalSign`.  So
this file repeats that construction and adds the two spanning statements; the extra inputs are only
`Work.ThomBordism.span_neg_eq` (the span does not see the sign) and
`Work.Cohomology.span_singleton_map_eq_top` (a surjection carries a generator to a generator).

This file is self-contained: it proves the statement `Work.ThomBordism.localDegreeSpan` on the nose,
and nothing below depends on any file of the `Tubular` area being modified.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.ThomBordism

noncomputable section

open Work.Cohomology
open Work.Tubular

/-- **The class implementing the local degree at the collapse class is a generator of the relative
cohomology of the Thom pair.**

For a closed oriented smooth `8`-manifold `V`, a rank-`k` (`k ≥ 1`) real bundle `Z` over `V`
identified with the normal bundle `ν = NormalTotal E` of an embedding `E : V ↪ ℝ^{8+k}` along a
homeomorphism `ψ` of pairs, tube data `C, q, g`, there is a class
`U ∈ H^k(ν, ν∖0)` which

* generates `H^k(ν, ν∖0)` as a `ℤ`-module (i.e. is a Thom class of `ν`), and
* realises the local degree: `⟨x ⌣ U, c⟩ = ⟨z^*x, [V]⟩` for every `x ∈ H⁸(ν)`, with `c` the
  collapse class `collapseRelK8 C g hg hR hbox`.

Both properties are met by the class constructed in the proof of
`Work.Tubular.exists_localDegree_at_collapseRelK8`: it is the transport under `ψ` of `±UZ₀` with
`UZ₀` a generator. -/
theorem localDegreeSpan {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hk : 1 ≤ k)
    {ι : Type} (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (ψ : Z.TotalSpace ≃ₜ Work.Tubular.NormalTotal E)
    (hproj : ∀ p : Z.TotalSpace, Work.Tubular.NormalTotal.proj (ψ p) = p.1)
    (hlen : ∀ p : Z.TotalSpace, Work.Thom.fibreNorm Z p ≠ 0 ↔ Work.Tubular.normalNorm E (ψ p) ≠ 0)
    (hvec : ∀ x : V.pt, Work.Tubular.NormalTotal.vec (ψ (Work.Thom.zeroSection Z x)) = 0)
    (hZ : Nonempty (Work.Thom.ThomClass Z k))
    {ε : ℝ} {C : Work.Tubular.TubeChart E ε} (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) :
    ∃ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E),
      Submodule.span ℤ ({U} : Set _) = ⊤ ∧
      (∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) 8 k x U))
          (Work.Tubular.collapseRelK8 C g hg hR hbox)
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c) := by
  classical
  haveI : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  obtain ⟨UZ₀, c₀, s, hs, hUZ₀, hc₀, hpair⟩ :=
    Work.ThomBordism.tubeLocalDegreeGlobalSign (V := V) (k := k) (hk := hk) Z hZ
  have hmemZ : ∀ p : Z.TotalSpace, p ∈ Work.Thom.zeroComplement Z
      ↔ Work.Thom.fibreNorm Z p ≠ 0 := by
    intro p
    rw [Work.Thom.zeroComplement, Set.mem_setOf_eq, Work.Thom.fibreNorm]
    exact norm_ne_zero_iff.symm
  have hAB : ∀ x : NormalTotal E, x ∈ normalNonzero E
      ↔ ψ.symm x ∈ Work.Thom.zeroComplement Z := by
    intro x
    rw [mem_normalNonzero, hmemZ, hlen, ψ.apply_symm_apply]
  have hw : CategoryTheory.CategoryStruct.comp
      (subtypeIncl (TopCat.of (NormalTotal E)) (normalNonzero E)) (TopCat.ofHom (ψ.symm))
      = CategoryTheory.CategoryStruct.comp (TopCat.ofHom ((ψ.symm).subtype hAB))
        (subtypeIncl (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)) := by
    apply TopCat.ext
    intro a
    rfl
  set cZ : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8) :=
    (HomologicalComplex.homologyMap (relChainsMapOf (TopCat.of (NormalTotal E))
      (TopCat.of Z.TotalSpace) (normalNonzero E) (Work.Thom.zeroComplement Z)
      (TopCat.ofHom (ψ.symm)) (TopCat.ofHom ((ψ.symm).subtype hAB)) hw) (k + 8)).hom
      (collapseRelK8 C g hg hR hbox) with hcZ
  haveI hiso := isIso_relChainsMapOf_homeoSub (X := TopCat.of (NormalTotal E))
    (Y := TopCat.of Z.TotalSpace) (ψ.symm) hAB hw (k + 8)
  have hcZgen : Submodule.span ℤ ({cZ} : Set _) = ⊤ := by
    rw [hcZ]
    exact Work.Tubular.span_singleton_map_eq_top
      (f := ((HomologicalComplex.homologyMap (relChainsMapOf (TopCat.of (NormalTotal E))
        (TopCat.of Z.TotalSpace) (normalNonzero E) (Work.Thom.zeroComplement Z)
        (TopCat.ofHom (ψ.symm)) (TopCat.ofHom ((ψ.symm).subtype hAB)) hw) (k + 8)).hom))
      (x := collapseRelK8 C g hg hR hbox)
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      (collapseRelK8_span_top C q hU hR hbox g hg hg2)
  obtain ⟨eT⟩ := Work.ThomBordism.thomPairTopHomologyIsoV2 (hk := hk) Z hZ
  have hcases : cZ = c₀ ∨ cZ = -c₀ :=
    Work.ThomBordism.eq_pm_of_span_eq_top_of_iso eT.toLinearEquiv hcZgen hc₀
  set UZ : Work.Thom.OpenThom Z k :=
    (if s = 1 then (if cZ = c₀ then UZ₀ else -UZ₀) else (if cZ = c₀ then -UZ₀ else UZ₀))
    with hUZdef
  -- **the added ingredient**: the class `UZ` is a generator, since it is `±UZ₀` and `span` does not
  -- see the sign.
  have hUZspan : Submodule.span ℤ ({UZ} : Set (Work.Thom.OpenThom Z k)) = ⊤ := by
    rw [hUZdef]
    by_cases hs1 : s = 1
    · rw [if_pos hs1]
      by_cases hc : cZ = c₀
      · rw [if_pos hc]; exact hUZ₀
      · rw [if_neg hc, Work.ThomBordism.span_neg_eq]; exact hUZ₀
    · rw [if_neg hs1]
      by_cases hc : cZ = c₀
      · rw [if_pos hc, Work.ThomBordism.span_neg_eq]; exact hUZ₀
      · rw [if_neg hc]; exact hUZ₀
  have hf1 : ∀ x ∈ normalNonzero E,
      (ψ.symm : C(NormalTotal E, Z.TotalSpace)) x ∈ Work.Thom.zeroComplement Z :=
    fun x hx => (hAB x).mp hx
  have hg1 : ∀ y ∈ Work.Thom.zeroComplement Z,
      (ψ : C(Z.TotalSpace, NormalTotal E)) y ∈ normalNonzero E :=
    fun y hy => (hAB (ψ y)).mpr (by simpa using hy)
  set U : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E) :=
    (Work.Thom.relCohMap (ψ.symm) (normalNonzero E) (Work.Thom.zeroComplement Z) hf1 ℤ k).hom UZ
    with hUdef
  -- **the second added ingredient**: the transport along a homeomorphism of pairs of a generator
  -- is a generator.  The transport is surjective, with the explicitly given inverse `relCohMap ψ`
  -- (this is also what makes the statement robust: the implicit `hf` argument of
  -- `Work.Thom.bijective_relCohMap_of_homeomorphA` does not unify definitionally with `hf1`
  -- without a costly unfolding of the cochain-level model), and a surjection carries a generator
  -- to a generator.
  have hspan : Submodule.span ℤ ({((Work.Thom.relCohMap (ψ.symm) (normalNonzero E)
      (Work.Thom.zeroComplement Z) hf1 ℤ k).hom UZ)} : Set
        (Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E))) = ⊤ := by
    have hsurj : Function.Surjective (Work.Thom.relCohMap (ψ.symm) (normalNonzero E)
        (Work.Thom.zeroComplement Z) hf1 ℤ k).hom := by
      have hcomp : (ψ : C(Z.TotalSpace, NormalTotal E)).comp
            (ψ.symm : C(NormalTotal E, Z.TotalSpace)) = ContinuousMap.id (NormalTotal E) := by
        apply ContinuousMap.ext
        intro z
        exact ψ.apply_symm_apply z
      have h1 : (Work.Thom.relCohMap (ψ : C(Z.TotalSpace, NormalTotal E))
            (Work.Thom.zeroComplement Z) (normalNonzero E) hg1 ℤ k) ≫
          (Work.Thom.relCohMap (ψ.symm) (normalNonzero E)
            (Work.Thom.zeroComplement Z) hf1 ℤ k)
          = 𝟙 (Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E)) :=
        (Work.Thom.relCohMap_compA (normalNonzero E) (Work.Thom.zeroComplement Z)
            (normalNonzero E) (ψ.symm : C(NormalTotal E, Z.TotalSpace))
            (ψ : C(Z.TotalSpace, NormalTotal E)) hf1 hg1
            (fun x hx => hg1 (ψ.symm x) (hf1 x hx)) ℤ k).trans
          ((Work.Thom.relCohMap_congrA (normalNonzero E) (normalNonzero E) hcomp
              (fun x hx => hg1 (ψ.symm x) (hf1 x hx)) (fun _ hx => hx) ℤ k).trans
            (Work.Thom.relCohMap_idA (normalNonzero E) ℤ k))
      intro y
      exact ⟨(Work.Thom.relCohMap (ψ : C(Z.TotalSpace, NormalTotal E))
          (Work.Thom.zeroComplement Z) (normalNonzero E) hg1 ℤ k).hom y,
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) y⟩
    have hmap : Submodule.map (Work.Thom.relCohMap (ψ.symm) (normalNonzero E)
        (Work.Thom.zeroComplement Z) hf1 ℤ k).hom
        (Submodule.span ℤ ({UZ} : Set _)) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro y
      obtain ⟨v, hv⟩ := hsurj y
      exact Submodule.mem_map.mpr ⟨v, by rw [hUZspan]; exact Submodule.mem_top, hv⟩
    rwa [Submodule.map_span, Set.image_singleton] at hmap
  have hUspan : Submodule.span ℤ ({U} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E))) = ⊤ := by
    rw [hUdef]
    exact hspan
  refine ⟨U, hUspan, ?_⟩
  · intro x
    set xZ : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace) :=
      (Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8).hom x with hxZ
    have hcomp1 : Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
          Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8
        = 𝟙 (Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal E))) := by
      have hcomp : (ψ : C(Z.TotalSpace, NormalTotal E)).comp
            (ψ.symm : C(NormalTotal E, Z.TotalSpace)) = ContinuousMap.id (NormalTotal E) := by
        apply ContinuousMap.ext
        intro y
        exact ψ.apply_symm_apply y
      rw [← Work.Thom.CohMap_comp (ψ.symm : C(NormalTotal E, Z.TotalSpace))
        (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8, hcomp, Work.Thom.CohMap_id]
    have hcx : (Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8).hom xZ = x := by
      rw [hxZ]
      have h2 : (Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8).hom
            ((Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8).hom x)
          = (Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
              Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8).hom x := by
        rw [ModuleCat.hom_comp]
        rfl
      rw [h2, hcomp1]
      rfl
    have hcomp2 : Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
          Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8
        = Work.Thom.CohMap ((ψ : C(Z.TotalSpace, NormalTotal E)).comp
            (Work.Thom.zeroSection Z)) ℤ 8 := by
      rw [Work.Thom.CohMap_comp (Work.Thom.zeroSection Z)
        (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8]
    have hzz : (Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom xZ
        = (Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom x := by
      have h2 : (Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom
            ((Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8).hom x)
          = (Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
              Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom x := by
        rw [ModuleCat.hom_comp]
        rfl
      rw [hxZ, h2, hcomp2, comp_zeroSection_eq_zeroSectionNormal Z ψ hproj hvec]
    have hZs : relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (k + 8)
        ((Nat.add_comm 8 k) ▸ mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          8 k xZ UZ) cZ
        = kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom xZ) V.c := by
      have base := hpair xZ
      rw [hUZdef]
      by_cases hs1 : s = 1
      · rw [if_pos hs1]
        by_cases hc : cZ = c₀
        · rw [if_pos hc, hc, base, hs1]
          ring
        · rw [if_neg hc]
          rcases hcases with hcZ | hcZ
          · exact absurd hcZ hc
          · rw [hcZ, mixedCup_neg_right, cast_neg_rel, relKronH_neg_left, relKronH_neg_right,
            base, hs1]
            ring
      · have hs' : s = -1 := by
          rcases hs with h | h
          · exact absurd h hs1
          · exact h
        rw [if_neg hs1]
        by_cases hc : cZ = c₀
        · rw [if_pos hc, hc, mixedCup_neg_right, cast_neg_rel, relKronH_neg_left, base, hs']
          ring
        · rw [if_neg hc]
          rcases hcases with hcZ | hcZ
          · exact absurd hcZ hc
          · rw [hcZ, relKronH_neg_right, base, hs']
            ring
    have hpu : (Work.Thom.relCohMap (ψ.symm) (normalNonzero E) (Work.Thom.zeroComplement Z)
          (fun x hx => (hAB x).mp hx) ℤ (k + 8)).hom
        ((Nat.add_comm 8 k) ▸ mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          8 k xZ UZ)
        = (Nat.add_comm 8 k) ▸ mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k x U := by
      rw [relCohMap_cast (A := normalNonzero E) (B := Work.Thom.zeroComplement Z)
        (ψ.symm) hf1 (Nat.add_comm 8 k)]
      simp only [mixedCup_topCatOf_eq_mixedCupC]
      rw [Work.Thom.mixedCupC_pairNatural (ψ.symm) (normalNonzero E)
        (Work.Thom.zeroComplement Z) hf1 8 k xZ UZ]
      rw [hcx, hUdef]
    have hK := relKronH_homeoPair (X := TopCat.of (NormalTotal E))
      (Y := TopCat.of Z.TotalSpace) (ψ.symm) hAB hw (k + 8)
      ((Nat.add_comm 8 k) ▸ mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        8 k xZ UZ)
      (collapseRelK8 C g hg hR hbox) cZ rfl
    rw [hpu, hZs, hzz] at hK
    exact hK

end

end Work.ThomBordism
