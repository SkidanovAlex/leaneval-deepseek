import Mathlib
import Submission.Work.ThomBordism.absThomCompareIso
import Submission.Work.Tubular.ThomComparison

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The comparison transfer of the relative Kronecker pairing, for a general real bundle

`Work.Tubular.relKronH_comparison` proves that the relative Kronecker pairing of the tubular chapter
is transported by the comparison isomorphism `H_n(ν, ν∖0) ≅ H_n(ν⁺, A)` of an embedding's normal
bundle, in the sense that

  `⟨β, (compIso).cν⟩ = ⟨(compPull β), cν⟩`.

This file is the **metric-free, general-bundle copy** of that theorem: the same statement with the
normal bundle `NormalTotal E` of an embedding replaced by an arbitrary real bundle
`Z : RealBundle B F ι` over a compact Hausdorff base, and the comparison `compIso`/`compPull` of
`Submission/Work/Tubular/ThomComparison.lean` replaced by the metric-free comparison
`Work.ThomBordism.compIsoZ`/`compPullZ` of `Submission/Work/ThomBordism/absThomCompareIso.lean`.

The two geometric inputs (`Work.ThomBordism.isIso_excChainZ`, `Work.ThomBordism.isIso_homeoChainZ`)
live in `Submission/Work/ThomBordism/absExcisionHomeoIso.lean`; the naturality of the pairing is
`Work.Tubular.relKronH_natural`, which is completely general.  So the proof is a verbatim mirror of
`Work.Tubular.relKronH_comparison`, with `relKronH_excisionZ`/`relKronH_homeoZ` in place of
`relKronH_excision`/`relKronH_homeo`.
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-! ## The excision of `{∞}` -/

/-- **The excision transfer of the relative Kronecker pairing**, for a general real bundle: the
general-bundle copy of `Work.Tubular.relKronH_excision`.  If `cU` is a class with
`(excChainZ Z)_* cU = c`, then pairing `β` with `c` is the same as pairing the excised `β` with
`cU`. -/
theorem relKronH_excisionZ (Z : RealBundle B F ι) (N : NormLike Z) (n : ℕ)
    (β : Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z))
    (c : (relChains (TopCat.of (OnePoint Z.TotalSpace)) (absNZ Z)).homology n)
    (cU : (relChains (TopCat.of ↥(infZ Z)) (excSubZ Z)).homology n)
    (hcU : (HomologicalComplex.homologyMap (excChainZ Z) n).hom cU = c) :
    Work.Tubular.relKronH (TopCat.of (OnePoint Z.TotalSpace)) (absNZ Z) n β c
      = Work.Tubular.relKronH (TopCat.of ↥(infZ Z)) (excSubZ Z) n
          ((Work.Thom.relCohMap (infZIncl Z)
            (excSubZ Z) (absNZ Z) (fun y hy => hy) ℤ n).hom β) cU := by
  have h := Work.Tubular.relKronH_natural
    (X := TopCat.of ↥(infZ Z)) (Y := TopCat.of (OnePoint Z.TotalSpace))
    (A := excSubZ Z) (B := absNZ Z)
    (TopCat.ofHom (infZIncl Z))
    (inclInterA (TopCat.of (OnePoint Z.TotalSpace)) (infZ Z) (absNZ Z))
    (fun y hy => hy) (excSpecZ Z) n β cU
  rw [excChainZ] at hcU
  rw [h, hcU]

/-! ## The homeomorphism of pairs `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)` -/

/-- **The homeomorphism transfer of the relative Kronecker pairing**, for a general real bundle: the
general-bundle copy of `Work.Tubular.relKronH_homeo`.  Pulling a class `b` of `({∞}ᶜ, {∞}ᶜ ∩ A)`
back along `someHomeoZ` and pairing it with `cν` is the same as pairing `b` with the image of `cν`
under the homeomorphism. -/
theorem relKronH_homeoZ (Z : RealBundle B F ι) (n : ℕ)
    (b : Work.Thom.RelCoh ℤ n ↥(infZ Z) (excSubZ Z))
    (cν : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology n)
    (cU : (relChains (TopCat.of ↥(infZ Z)) (excSubZ Z)).homology n)
    (hcU : (HomologicalComplex.homologyMap (homeoChainZ Z) n).hom cν = cU) :
    Work.Tubular.relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) n
        ((HomologicalComplex.homologyMap (relComplexMap ℤ (Work.Thom.zeroComplement Z) (excSubZ Z)
          (TopCat.ofHom (someHomeoZ Z)) (fun x hx => (some_mem_excSubZ Z x).mp hx)) n).hom b) cν
      = Work.Tubular.relKronH (TopCat.of ↥(infZ Z)) (excSubZ Z) n b cU := by
  have h := Work.Tubular.relKronH_natural
    (X := TopCat.of Z.TotalSpace) (Y := TopCat.of ↥(infZ Z))
    (A := Work.Thom.zeroComplement Z) (B := excSubZ Z)
    (TopCat.ofHom (someHomeoZ Z)) (TopCat.ofHom ((someHomeoZ Z).subtype (some_mem_excSubZ Z)))
    (fun x hx => (some_mem_excSubZ Z x).mp hx) (homeoSubMapZ_spec Z) n b cν
  rw [homeoChainZ] at hcU
  rw [hcU] at h
  exact h

/-! ## The comparison transfer -/

/-- **The comparison transfer of the relative Kronecker pairing**, for a general real bundle: the
general-bundle copy of `Work.Tubular.relKronH_comparison`. -/
theorem relKronH_comparisonZ (Z : RealBundle B F ι) (N : NormLike Z) (n : ℕ)
    (β : Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z))
    (cν : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology n) :
    Work.Tubular.relKronH (TopCat.of (OnePoint Z.TotalSpace)) (absNZ Z) n β
        ((compIsoZ Z N n).hom cν)
      = Work.Tubular.relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) n
          (compPullZ Z N n β) cν := by
  haveI h1 := isIso_homeoChainZ Z n
  haveI h2 := isIso_excChainZ (Z := Z) N n
  set cU := (asIso (HomologicalComplex.homologyMap (homeoChainZ Z) n)).hom cν with hcUdef
  have hhom : ((compIsoZ Z N n).hom) cν
      = (HomologicalComplex.homologyMap (excChainZ Z) n).hom cU := rfl
  have hE := relKronH_excisionZ Z N n β
    ((HomologicalComplex.homologyMap (excChainZ Z) n).hom cU) cU rfl
  have hH := relKronH_homeoZ Z n
    ((Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z)
      (fun y hy => hy) ℤ n).hom β) cν cU (by rw [hcUdef]; rfl)
  rw [hhom]
  exact hE.trans (hH.symm.trans (by rfl))

theorem absRelKronHComparison {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (N : Work.ThomBordism.NormLike Z) (n : ℕ)
    (β : Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (Work.ThomBordism.absNZ Z))
    (cν : (Work.Cohomology.relChains (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z)).homology n) :
    Work.Tubular.relKronH (TopCat.of (OnePoint Z.TotalSpace)) (Work.ThomBordism.absNZ Z) n β
        ((Work.ThomBordism.compIsoZ Z N n).hom cν)
      = Work.Tubular.relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) n
          (Work.ThomBordism.compPullZ Z N n β) cν :=
  relKronH_comparisonZ Z N n β cν

end

end Work.ThomBordism
