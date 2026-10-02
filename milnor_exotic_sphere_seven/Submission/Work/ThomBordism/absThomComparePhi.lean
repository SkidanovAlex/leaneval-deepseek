import Submission.Work.ThomBordism.absThomCompareIso
import Submission.Work.ThomBordism.absRelKronHComparison
import Submission.Work.ThomBordism.absNZRelToAbsBijective
import Submission.Work.ThomBordism.absContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The canonical comparison `Phi : H^n(Z, Z∖0) ≃ₗ H^n(Z⁺)` for a general bundle

With

* `compPullZ : H^n(Z⁺, A) → H^n(Z, Z∖0)` (the excision plus the homeomorphism `Z ≅ {∞}ᶜ`), and
* `relCohOfAbsZ : H^n(Z⁺) → H^n(Z⁺, A)` (the inverse of the forgetful map, available because `A` is
  contractible),

the **canonical comparison** of the Thom pair with the Thom space is

  `ThetaZ Z N n := compPullZ Z N n ∘ relCohOfAbsZ Z N n`,   `PhiZ := ThetaZ⁻¹`,

the general-bundle copy of TUBULAR's `compPull ∘ relCoh_of_abs`.  Its defining property is the
*pairing* form of `Work.ThomBordism.absRelKronHComparison`, so that with `Phi := PhiZ` the
`FamilyTubeData` pairings are computable by the local degree; see `NOTES_round15_H4.md`.
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-- **The inverse of the forgetful map** `H^n(Z⁺) → H^n(Z⁺, A)`: the general-bundle copy of
TUBULAR's `relCoh_of_abs`. -/
noncomputable def relCohOfAbsZ (Z : RealBundle B F ι) (N : NormLike Z) {n : ℕ} (hn : 2 ≤ n) :
    Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace) →ₗ[ℤ]
      Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z) :=
  (LinearEquiv.ofBijective ((Work.Thom.relToAbs ℤ (absNZ Z) n).hom)
    (absNZRelToAbsBijective Z (absContractible Z N) hn)).symm

/-- The defining property of `relCohOfAbsZ`: forgetting the support returns the original class. -/
theorem relToAbs_relCohOfAbsZ (Z : RealBundle B F ι) (N : NormLike Z) {n : ℕ} (hn : 2 ≤ n)
    (u : Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace)) :
    (Work.Thom.relToAbs ℤ (absNZ Z) n).hom (relCohOfAbsZ Z N hn u) = u := by
  rw [relCohOfAbsZ]
  rw [← LinearEquiv.ofBijective_apply (f := (Work.Thom.relToAbs ℤ (absNZ Z) n).hom)
    (hf := absNZRelToAbsBijective Z (absContractible Z N) hn)]
  exact LinearEquiv.apply_symm_apply _ u

/-- **The canonical comparison as a map** `H^n(Z⁺) → H^n(Z, Z∖0)`: the composite of the inverse of
the forgetful map with the excision-plus-homeomorphism pullback.  Its inverse is `PhiZ`. -/
noncomputable def ThetaZ (Z : RealBundle B F ι) (N : NormLike Z) {n : ℕ} (hn : 2 ≤ n) :
    Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace) →ₗ[ℤ]
      Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z) :=
  (compPullZ Z N n).comp (relCohOfAbsZ Z N hn)

end

end Work.ThomBordism
