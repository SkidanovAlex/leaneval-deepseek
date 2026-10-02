import Submission.Work.ThomBordism.absThomCompare
import Submission.Work.ThomBordism.absExcisionHomeoIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The chain-level comparison `(Z, Z∖0) ≅ (Z⁺, A)`: the isomorphism and its pullback

Companion of `Work.ThomBordism.absThomCompare`: with the excision and homeomorphism isomorphisms
proved (`Work.ThomBordism.absExcisionHomeoIso`), this file defines

* `Work.ThomBordism.compIsoZ Z N n : H_n(Z, Z∖0) ≅ H_n(Z⁺, A)` — the composite of the
  homeomorphism of pairs `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)` and the excision of `{∞}`;
* `Work.ThomBordism.compPullZ Z N n : H^n(Z⁺, A) → H^n(Z, Z∖0)` — the composite pullback.

These are the general-bundle copies of `Work.Tubular.compIso`/`compPull`.
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-- **The comparison `H_n(Z, Z∖0) ≅ H_n(Z⁺, A)`** of the relative homology of the Thom pair with the
relative homology of the pair `(Z⁺, A)`: the homeomorphism of pairs followed by the excision of
`{∞}`.  (The general-bundle copy of `Work.Tubular.compIso`.) -/
noncomputable def compIsoZ (Z : RealBundle B F ι) (N : NormLike Z) (n : ℕ) :
    (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology n ≅
      (relChains (TopCat.of (OnePoint Z.TotalSpace)) (absNZ Z)).homology n := by
  have h := absExcisionHomeoIso Z N n
  haveI : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (homeoChainZ Z) n) := h.2.2
  haveI : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (excChainZ Z) n) := h.2.1
  exact Iso.trans (asIso (HomologicalComplex.homologyMap (homeoChainZ Z) n))
    (asIso (HomologicalComplex.homologyMap (excChainZ Z) n))

/-- **The composite pullback of relative cohomology along the comparison**: the general-bundle copy
of `Work.Tubular.compPull`. -/
noncomputable def compPullZ (Z : RealBundle B F ι) (N : NormLike Z) (n : ℕ) :
    Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z) →ₗ[ℤ]
      Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z) :=
  { toFun := fun β =>
      (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
        (Work.Thom.zeroComplement Z) (excSubZ Z)
        (TopCat.ofHom (someHomeoZ Z)) (fun x hx => (some_mem_excSubZ Z x).mp hx)) n).hom
        ((Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z)
          (fun y hy => hy) ℤ n).hom β)
    map_add' := fun β γ => by simp
    map_smul' := fun c β => by simp }

end

end Work.ThomBordism
