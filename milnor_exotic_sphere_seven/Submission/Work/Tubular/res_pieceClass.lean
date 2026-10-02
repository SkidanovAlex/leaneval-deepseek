import Mathlib
import Submission.Work.Tubular.normalDiscHalfOrientationData
import Submission.Work.Tubular.tubeExcisionNat
import Submission.Work.Tubular.tubeTransferChain
import Submission.Work.Tubular.exists_halfOrientationFamily_euclidean

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The transfer is compatible with the restriction to a point

`Work.Tubular.res_pieceClass`: the class `pieceClass C K hK hKc a'` over a compact piece `K` of the
disc bundle (the transfer of the ambient class `a'`, cf. `normalDiscHalfOrientationData`) restricts,
at a point `x ∈ K`, to the transferred class `transferredClass C γ₀ x hx`.  This is the coherence
clause of `Work.Orient.IsHalfOrientationFamily` applied to the family assembled in
`exists_halfOrientationFamily_normalDiscSub`.

The proof is a diagram chase in the two naturality squares of the transfer:

* `invChainMap_relCokerMap` (the inverse tubular map is compatible with enlarging the relative set),
* `excisionMap_relCokerMap` (excision is compatible with enlarging the relative set),

together with `ha'` (the ambient class `a'` specialises to `γ₀` at every point of `tubeImage K`) and
the identification `tubeImage {x} = {tubePt C x hx}` (`tubeImage_singleton`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Tubular

noncomputable section

theorem res_pieceClass {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : Work.Tubular.TubeChart E ε)
    (γ₀ : ∀ y : Work.Tubular.Euc (8 + k),
      Work.Orient.LocH (TopCat.of (Work.Tubular.Euc (8 + k))) (8 + k) y)
    {K : Set (Work.Tubular.NormalDiscSub E ε)}
    (hK : ∀ q ∈ K, Work.Tubular.normalNorm E (q : Work.Tubular.NormalTotal E) < ε)
    (hKc : IsCompact K)
    (a' : (Work.Cohomology.relChains (TopCat.of (Work.Tubular.Euc (8 + k)))
      ((Work.Tubular.tubeImage (E := E) K)ᶜ)).homology (8 + k))
    (ha' : ∀ (y : Work.Tubular.Euc (8 + k)) (hy : y ∈ Work.Tubular.tubeImage (E := E) K),
      Work.Orient.resRelH (TopCat.of (Work.Tubular.Euc (8 + k))) (8 + k)
        (Set.singleton_subset_iff.mpr hy) a' = γ₀ y)
    (x : Work.Tubular.NormalDiscSub E ε) (hxK : x ∈ K)
    (hx : Work.Tubular.normalNorm E (x : Work.Tubular.NormalTotal E) < ε) :
    Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalDiscSub E ε)) (8 + k)
        (Set.singleton_subset_iff.mpr hxK)
        (Work.Tubular.pieceClass C K hK hKc a')
      = Work.Tubular.transferredClass C γ₀ x hx := by
  classical
  have hsub : ({x} : Set (Work.Tubular.NormalDiscSub E ε)) ⊆ K :=
    Set.singleton_subset_iff.mpr hxK
  have hxsing : ∀ q ∈ ({x} : Set (Work.Tubular.NormalDiscSub E ε)),
      Work.Tubular.normalNorm E (q : Work.Tubular.NormalTotal E) < ε :=
    fun q hq => by rw [Set.mem_singleton_iff] at hq; exact hq ▸ hx
  haveI hIK : IsIso (HomologicalComplex.homologyMap
      (Work.Tubular.excisionMap (E := E) K) (8 + k)) :=
    Work.Tubular.isIso_excisionMap_homologyMap C hK hKc
  haveI hIx : IsIso (HomologicalComplex.homologyMap
      (Work.Tubular.excisionMap (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
      (8 + k)) :=
    Work.Tubular.isIso_excisionMap_homologyMap C hxsing isCompact_singleton
  have hpt_mem : (Work.Tubular.tubePt C x hx : Work.Tubular.Euc (8 + k)) ∈
      Work.Tubular.tubeImage (E := E) K := ⟨x, hxK, rfl⟩
  let rd := Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalDiscSub E ε))
      (Work.Tubular.discRelSub K)
      (Work.Tubular.discRelSub ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
      (fun y hy hc => hy (hsub hc))
  let ru := Work.Cohomology.relCokerMap (TopCat.of ↥(Work.Tubular.openTubeSet E ε))
      (Work.Tubular.tubeRelSub (E := E) K)
      (Work.Tubular.tubeRelSub (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
      (fun y hy hyy => hy (by rcases hyy with ⟨q, hq, hqe⟩; exact ⟨q, hsub hq, hqe⟩))
  let rx := Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.Euc (8 + k)))
      ((Work.Tubular.tubeImage (E := E) K)ᶜ)
      ((Work.Tubular.tubeImage (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))ᶜ)
      (fun y hy hc => hy (by rcases hc with ⟨q, hq, hqe⟩; exact ⟨q, hsub hq, hqe⟩))
  let rpt := Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.Euc (8 + k)))
      ((Work.Tubular.tubeImage (E := E) K)ᶜ)
      ({(Work.Tubular.tubePt C x hx : Work.Tubular.Euc (8 + k))}ᶜ)
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hpt_mem))
  let u : (Work.Cohomology.relChains (TopCat.of ↥(Work.Tubular.openTubeSet E ε))
      (Work.Tubular.tubeRelSub (E := E) K)).homology (8 + k) :=
    (CategoryTheory.inv (HomologicalComplex.homologyMap
      (Work.Tubular.excisionMap (E := E) K) (8 + k))).hom a'
  have hInvNatH : HomologicalComplex.homologyMap (Work.Tubular.invChainMap C K) (8 + k)
        ≫ HomologicalComplex.homologyMap rd (8 + k)
      = HomologicalComplex.homologyMap ru (8 + k)
        ≫ HomologicalComplex.homologyMap
            (Work.Tubular.invChainMap C ({x} : Set (Work.Tubular.NormalDiscSub E ε))) (8 + k) := by
    have h := congrArg (fun φ => HomologicalComplex.homologyMap φ (8 + k))
      (Work.Tubular.invChainMap_relCokerMap C hsub)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
    exact h
  have hExcNatH : HomologicalComplex.homologyMap (Work.Tubular.excisionMap (E := E) K) (8 + k)
        ≫ HomologicalComplex.homologyMap rx (8 + k)
      = HomologicalComplex.homologyMap ru (8 + k)
        ≫ HomologicalComplex.homologyMap
            (Work.Tubular.excisionMap (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
            (8 + k) := by
    have h := congrArg (fun φ => HomologicalComplex.homologyMap φ (8 + k))
      (Work.Tubular.excisionMap_relCokerMap (E := E) hsub)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
    exact h
  have hpiece : Work.Tubular.pieceClass C K hK hKc a'
      = (HomologicalComplex.homologyMap (Work.Tubular.invChainMap C K) (8 + k)).hom u := by
    simp only [Work.Tubular.pieceClass, u]
  have hγ : (HomologicalComplex.homologyMap rpt (8 + k)).hom a'
      = γ₀ (Work.Tubular.tubePt C x hx) :=
    ha' (Work.Tubular.tubePt C x hx) hpt_mem
  have hrx_eq : rx = rpt ≫ Work.Tubular.identMap C x hx := by
    simp only [rx, rpt, Work.Tubular.identMap]
    exact (Work.Cohomology.relCokerMap_congr _ _).trans
      (Work.Cohomology.relCokerMap_comp _ _).symm
  have hrxL : (HomologicalComplex.homologyMap (Work.Tubular.identMap C x hx) (8 + k)).hom ∘ₗ
        (HomologicalComplex.homologyMap rpt (8 + k)).hom
      = (HomologicalComplex.homologyMap rx (8 + k)).hom := by
    rw [hrx_eq, ← ModuleCat.hom_comp, HomologicalComplex.homologyMap_comp]
  have stepC : (HomologicalComplex.homologyMap rx (8 + k)).hom a'
      = Work.Tubular.tubePtClass C γ₀ x hx := by
    rw [← hrxL]
    exact (congrArg (fun z =>
        (HomologicalComplex.homologyMap (Work.Tubular.identMap C x hx) (8 + k)).hom z) hγ).trans
      (by simp only [Work.Tubular.tubePtClass])
  have hKu : (HomologicalComplex.homologyMap (Work.Tubular.excisionMap (E := E) K) (8 + k)).hom u
      = a' :=
    CategoryTheory.IsIso.inv_hom_id_apply _ a'
  have hInvL : (HomologicalComplex.homologyMap rd (8 + k)).hom ∘ₗ
        (HomologicalComplex.homologyMap (Work.Tubular.invChainMap C K) (8 + k)).hom
      = (HomologicalComplex.homologyMap
            (Work.Tubular.invChainMap C ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
            (8 + k)).hom ∘ₗ
        (HomologicalComplex.homologyMap ru (8 + k)).hom := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, hInvNatH]
  have stepA : (HomologicalComplex.homologyMap rd (8 + k)).hom
        (Work.Tubular.pieceClass C K hK hKc a')
      = (HomologicalComplex.homologyMap
            (Work.Tubular.invChainMap C ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
            (8 + k)).hom
          ((HomologicalComplex.homologyMap ru (8 + k)).hom u) := by
    rw [hpiece]
    exact LinearMap.congr_fun hInvL u
  have hExcL : (HomologicalComplex.homologyMap rx (8 + k)).hom ∘ₗ
        (HomologicalComplex.homologyMap (Work.Tubular.excisionMap (E := E) K) (8 + k)).hom
      = (HomologicalComplex.homologyMap
            (Work.Tubular.excisionMap (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
            (8 + k)).hom ∘ₗ
        (HomologicalComplex.homologyMap ru (8 + k)).hom := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, hExcNatH]
  have h1 : (HomologicalComplex.homologyMap
        (Work.Tubular.excisionMap (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
        (8 + k)).hom ((HomologicalComplex.homologyMap ru (8 + k)).hom u)
      = Work.Tubular.tubePtClass C γ₀ x hx := by
    have hExcA := LinearMap.congr_fun hExcL u
    exact hExcA.symm.trans
      ((congrArg (fun z => (HomologicalComplex.homologyMap rx (8 + k)).hom z) hKu).trans stepC)
  have stepB : (HomologicalComplex.homologyMap ru (8 + k)).hom u
      = (CategoryTheory.inv (HomologicalComplex.homologyMap
          (Work.Tubular.excisionMap (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
          (8 + k))).hom (Work.Tubular.tubePtClass C γ₀ x hx) := by
    have h2 := congrArg (fun z => (CategoryTheory.inv (HomologicalComplex.homologyMap
        (Work.Tubular.excisionMap (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
        (8 + k))).hom z) h1
    rw [CategoryTheory.IsIso.hom_inv_id_apply] at h2
    exact h2
  have ht : Work.Tubular.transferredClass C γ₀ x hx
      = (HomologicalComplex.homologyMap
            (Work.Tubular.invChainMap C ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
            (8 + k)).hom
          ((CategoryTheory.inv (HomologicalComplex.homologyMap
            (Work.Tubular.excisionMap (E := E) ({x} : Set (Work.Tubular.NormalDiscSub E ε)))
            (8 + k))).hom (Work.Tubular.tubePtClass C γ₀ x hx)) := by
    simp only [Work.Tubular.transferredClass]
  change (HomologicalComplex.homologyMap rd (8 + k)).hom
      (Work.Tubular.pieceClass C K hK hKc a')
      = Work.Tubular.transferredClass C γ₀ x hx
  exact stepA.trans ((congrArg (fun z => (HomologicalComplex.homologyMap
    (Work.Tubular.invChainMap C ({x} : Set (Work.Tubular.NormalDiscSub E ε))) (8 + k)).hom z)
    stepB).trans ht.symm)

end

end Work.Tubular
