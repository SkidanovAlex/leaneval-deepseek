/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import Submission.Work.TwistModel.BaseChange
import Submission.Work.TwistModel.irreducibleSpace_of_openCover_of_pairwise

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrality of the base change of `ℙⁿ` along a field extension

This file proves `Work.TwistModel.isIntegral_projectiveSpaceBaseChange`: given that every chart
`chartPullback 𝕜 n K i` of the base change `ℙⁿ_K = ℙⁿ_𝕜 ×_{Spec 𝕜} Spec K` is isomorphic to the
affine space `Spec K[y₁,…,yₙ]` (the hypothesis `hiso`, proved in the sibling module
`Work.TwistModel.chartPullbackIso`), the base change is integral.

The proof is the standard chart argument.

* The charts `chartPullbackOpen 𝕜 n K i = fst ⁻¹ᵁ D₊(Xᵢ)` **cover** the base change, because the
  standard charts cover `ℙⁿ` (`Work.Twist.iSup_basicOpen_X_eq_top`) and preimages of open covers
  are open covers (`Scheme.Hom.iSup_preimage_eq_top`).
* Each chart is **integral**: it is isomorphic to `Spec K[y₁,…,yₙ]`, the spectrum of a domain, and
  integrality is invariant under isomorphism (`IsIntegral.of_isIso`).
* Any two charts **meet**: `fst` is surjective (the base `Spec 𝕜` is a single point, so the base
  change `Spec K ⟶ Spec 𝕜` is surjective and hence so is its pullback), while
  `D₊(Xᵢ) ∩ D₊(Xⱼ) = D₊(XᵢXⱼ)` is nonempty, since the (relevant, homogeneous) zero ideal lies in it.
  Hence the base change is **irreducible** (`irreducibleSpace_of_openCover_of_pairwise`).
* Finally the base change is **reduced**, being covered by reduced open subschemes: every stalk of
  the base change is a stalk of a chart, and the stalks of `Spec K[y₁,…,yₙ]` are reduced.

`IsIntegral` is `IrreducibleSpace ∧ IsReduced` (`isIntegral_iff_irreducibleSpace_and_isReduced`),
which gives the claim.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Work.TwistModel

noncomputable section

theorem isIntegral_projectiveSpaceBaseChange (𝕜 : Type) [Field 𝕜] (n : ℕ) (K : Type) [Field K]
    [Algebra 𝕜 K]
    (hiso : ∀ i : Fin (n + 1), Nonempty (Work.TwistModel.chartPullback 𝕜 n K i ≅
      AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin n) K)))) :
    AlgebraicGeometry.IsIntegral (Work.TwistModel.projectiveSpaceBaseChange 𝕜 n K) := by
  -- `fst : ℙⁿ_K ⟶ ℙⁿ` is the projection of the base change.
  -- ### Each chart is integral (it is `Spec K[y₁,…,yₙ]`)
  have hInt : ∀ i : Fin (n + 1), IsIntegral (Work.TwistModel.chartPullback 𝕜 n K i) := by
    intro i
    obtain ⟨e⟩ := hiso i
    haveI : IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin n) K))) := inferInstance
    exact IsIntegral.of_isIso e.inv
  -- ### `fst` is surjective
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K))) :=
    Surjective.mk (fun y => ⟨(inferInstance : Nonempty (PrimeSpectrum K)).some, Subsingleton.elim _ _⟩)
  haveI := hsurj
  have hfst : Surjective (pullback.fst (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))) := inferInstance
  -- ### The charts cover the base change
  have hcover : (⨆ i : Fin (n + 1), Work.TwistModel.chartPullbackOpen 𝕜 n K i) = ⊤ :=
    Scheme.Hom.iSup_preimage_eq_top
      (f := pullback.fst (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K))))
      (U := fun i : Fin (n + 1) =>
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
          (MvPolynomial.X i) : (Work.PointlessIndexFive.projectiveSpace 𝕜 n).Opens))
      (Work.Twist.iSup_basicOpen_X_eq_top 𝕜 n)
  -- ### Membership in a chart is membership of the image under `fst`
  have hmem : ∀ (U : (Work.PointlessIndexFive.projectiveSpace 𝕜 n).Opens)
      (x : ↥(Work.TwistModel.projectiveSpaceBaseChange 𝕜 n K)),
      x ∈ (pullback.fst (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))) ⁻¹ᵁ U ↔
        (pullback.fst (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))) x ∈ U := fun _ _ => Iff.rfl
  -- ### Each chart is irreducible
  have hirr : ∀ i : Fin (n + 1),
      IrreducibleSpace (↥(Work.TwistModel.chartPullbackOpen 𝕜 n K i)) :=
    fun i => @irreducibleSpace_of_isIntegral (Work.TwistModel.chartPullback 𝕜 n K i) (hInt i)
  -- ### Any two charts meet: the zero ideal of `ℙⁿ` lies in both of them
  have hpair : ∀ i j : Fin (n + 1), ∃ x : ↥(Work.TwistModel.projectiveSpaceBaseChange 𝕜 n K),
      x ∈ Work.TwistModel.chartPullbackOpen 𝕜 n K i ∧
        x ∈ Work.TwistModel.chartPullbackOpen 𝕜 n K j := by
    intro i j
    -- The generic point of `ℙⁿ`, i.e. the relevant homogeneous prime `(0)`.
    let y : ↥(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)) :=
      ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot,
        Work.Twist.irrelevant_homogeneousSubmodule_ne_bot 𝕜 n⟩
    have hy : y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (MvPolynomial.X i * MvPolynomial.X j) := by
      rw [Proj.mem_basicOpen]
      show MvPolynomial.X i * MvPolynomial.X j ∉
        (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜))
      intro h
      exact absurd h (mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j))
    have hy' : y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
          (MvPolynomial.X i) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
          (MvPolynomial.X j) := by
      rw [← Proj.basicOpen_mul]
      exact hy
    obtain ⟨x, hx⟩ := hfst.surj y
    refine ⟨x, ?_, ?_⟩
    · rw [show Work.TwistModel.chartPullbackOpen 𝕜 n K i =
          (pullback.fst (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
            (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
            (MvPolynomial.X i) from rfl]
      rw [hmem, hx]
      exact hy'.1
    · rw [show Work.TwistModel.chartPullbackOpen 𝕜 n K j =
          (pullback.fst (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n)
            (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 K)))) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
            (MvPolynomial.X j) from rfl]
      rw [hmem, hx]
      exact hy'.2
  -- ### The base change is irreducible
  haveI hirrX : IrreducibleSpace (↥(Work.TwistModel.projectiveSpaceBaseChange 𝕜 n K)) :=
    Work.TwistModel.irreducibleSpace_of_openCover_of_pairwise
      (Work.TwistModel.chartPullbackOpen 𝕜 n K) hcover hirr hpair
  -- ### The base change is reduced: every stalk is a stalk of a chart
  haveI hIntInst : ∀ i : Fin (n + 1), IsIntegral (Work.TwistModel.chartPullback 𝕜 n K i) := hInt
  have hstalk : ∀ x : ↥(Work.TwistModel.projectiveSpaceBaseChange 𝕜 n K),
      _root_.IsReduced ((Work.TwistModel.projectiveSpaceBaseChange 𝕜 n K).presheaf.stalk x) := by
    intro x
    have hx : x ∈ (⨆ i : Fin (n + 1), Work.TwistModel.chartPullbackOpen 𝕜 n K i) := by
      rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    haveI hredU : IsReduced (Work.TwistModel.chartPullback 𝕜 n K i) := inferInstance
    haveI hredU' : IsReduced (Work.TwistModel.chartPullbackOpen 𝕜 n K i : Scheme) := hredU
    exact isReduced_of_injective
      (((Work.TwistModel.chartPullbackOpen 𝕜 n K i).stalkIso ⟨x, hi⟩).commRingCatIsoToRingEquiv.symm)
      (((Work.TwistModel.chartPullbackOpen 𝕜 n K i).stalkIso
        ⟨x, hi⟩).commRingCatIsoToRingEquiv.symm).injective
  haveI : IsReduced (Work.TwistModel.projectiveSpaceBaseChange 𝕜 n K) :=
    isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end Work.TwistModel
