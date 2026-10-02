import Mathlib
import Submission.Work.ThomBordism.absThomComparePhi
import Submission.Work.Thom.CapChain
import Submission.Work.Cohomology.cappedPairMapIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

/-!
# The canonical comparison `H^n(Z⁺) ≅ H^n(Z, Z∖0)` is bijective

`Work.ThomBordism.ThetaZ Z N hn` is the canonical comparison

  `ThetaZ = compPullZ ∘ relCohOfAbsZ : H^n(Z⁺;ℤ) → H^n(Z, Z∖0;ℤ)`

of `Submission/Work/ThomBordism/absThomComparePhi.lean`: it is the general-bundle copy of
`Work.Tubular`'s `compPull ∘ relCoh_of_abs`, and its inverse is written `PhiZ`.

Here we prove that it really is an isomorphism.  The two factors are:

* `relCohOfAbsZ Z N hn`, the inverse of the forgetful map `relToAbs : H^n(Z⁺, A) → H^n(Z⁺)`,
  bijective because `relToAbs` is (`absNZRelToAbsBijective`, `A` being contractible);
* `compPullZ Z N n`, the composite of the excision pullback
  `H^n(Z⁺, A) → H^n({∞}ᶜ, {∞}ᶜ ∩ A)` (bijective by cohomological excision,
  `relComplexMap_excision_isIso`) with the pullback along the homeomorphism of pairs
  `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)` (bijective by `bijective_relCohMap_of_homeomorphA`).
-/

namespace Work.ThomBordism

theorem bijectiveThetaZ {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (N : Work.ThomBordism.NormLike Z) {n : ℕ}
    (hn : 2 ≤ n) :
    Function.Bijective (Work.ThomBordism.ThetaZ Z N hn) := by
  -- bijectivity of the pullback along the homeomorphism of pairs `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)`
  have h2 : Function.Bijective (fun u =>
      (Work.Thom.relCohMap (Work.ThomBordism.someHomeoZ Z)
        (Work.Thom.zeroComplement Z) (Work.ThomBordism.excSubZ Z)
        (fun x hx => (Work.ThomBordism.some_mem_excSubZ Z x).mp hx) ℤ n).hom u) :=
    Work.Thom.bijective_relCohMap_of_homeomorphA
      (Work.Thom.zeroComplement Z) (Work.ThomBordism.excSubZ Z)
      (Work.ThomBordism.someHomeoZ Z) (Work.ThomBordism.some_mem_excSubZ Z) ℤ n
  -- bijectivity of the excision pullback `H^n(Z⁺, A) → H^n({∞}ᶜ, {∞}ᶜ ∩ A)`
  have h1 : Function.Bijective (fun β =>
      (Work.Thom.relCohMap (Work.ThomBordism.infZIncl Z) (Work.ThomBordism.excSubZ Z)
        (Work.ThomBordism.absNZ Z) (fun y hy => hy) ℤ n).hom β) := by
    have hiso : CategoryTheory.IsIso
        (Work.Thom.relCohMap (Work.ThomBordism.infZIncl Z) (Work.ThomBordism.excSubZ Z)
          (Work.ThomBordism.absNZ Z) (fun y hy => hy) ℤ n) :=
      Work.Cohomology.relComplexMap_excision_isIso ℤ (TopCat.of (OnePoint Z.TotalSpace))
        (Work.ThomBordism.infZ Z) (Work.ThomBordism.absNZ Z)
        (OnePoint.isClosed_infty.isOpen_compl) (Work.ThomBordism.isOpen_absNZ N)
        (Work.ThomBordism.infZ_union_absNZ Z) n (fun x hx => hx)
    exact CategoryTheory.ConcreteCategory.bijective_of_isIso _
  -- the composite `compPullZ Z N n`
  have hbij_cp : Function.Bijective (Work.ThomBordism.compPullZ Z N n) := h2.comp h1
  -- the inverse of the forgetful map
  have habs : Function.Bijective (Work.ThomBordism.relCohOfAbsZ Z N hn) := by
    have hf : Function.Bijective
        (fun u => (Work.Thom.relToAbs ℤ (Work.ThomBordism.absNZ Z) n).hom u) :=
      Work.ThomBordism.absNZRelToAbsBijective Z (Work.ThomBordism.absContractible Z N) hn
    refine ⟨fun u v huv => ?_, fun β => ?_⟩
    · have h := congrArg (fun w => (Work.Thom.relToAbs ℤ (Work.ThomBordism.absNZ Z) n).hom w) huv
      rwa [Work.ThomBordism.relToAbs_relCohOfAbsZ Z N hn u,
        Work.ThomBordism.relToAbs_relCohOfAbsZ Z N hn v] at h
    · refine ⟨(Work.Thom.relToAbs ℤ (Work.ThomBordism.absNZ Z) n).hom β, ?_⟩
      exact hf.1 (Work.ThomBordism.relToAbs_relCohOfAbsZ Z N hn
        ((Work.Thom.relToAbs ℤ (Work.ThomBordism.absNZ Z) n).hom β))
  exact hbij_cp.comp habs

end Work.ThomBordism
