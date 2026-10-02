import Submission.Work.ThomBordism.absThomComparePhiZ
import Submission.Work.ThomBordism.thetaZNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The naturality of the canonical comparison, in the `Phi` form

`Phi_Z` is the canonical comparison `H^n(Z, Z∖0) ≃ₗ H^n(Z⁺)`.  Its naturality
(`Work.ThomBordism.thetaZNatural`) says that for a bundle map `g : Z' → Z` with one-point extension
`J` the square

  `H^n(Z⁺) --J^*--> H^n(Z'⁺)`
  `  |Phi_Z^{-1}                |Phi_{Z'}^{-1}`
  `H^n(Z, Z∖0) --g^*--> H^n(Z', Z'∖0)`

commutes, i.e. `Phi_{Z'} (g^* a) = J^* (Phi_Z a)`.  This is the "description of the universal
classes": with `Z = γ_{k,10}`, `Z' = ν` the normal bundle of an embedded `V` and
`a = π^*(p₁(γ)²) ⌣ U_γ`, it identifies the pullback of the universal class with the geometric
class of `ν`.  See `NOTES_round15_H4.md`.
-/

open CategoryTheory
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-- **The naturality of the canonical comparison, in the `Phi` form**: for a bundle map `g` with
one-point extension `J`, `Phi_{Z'}` of the pullback is the pullback of `Phi_Z`. -/
theorem compPullZ_relCohOfAbsZ_PhiZ {B' : Type} [TopologicalSpace B'] [CompactSpace B']
    [T2Space B'] {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [FiniteDimensional ℝ F'] {ι' : Type}
    (Z : RealBundle B F ι) (Z' : RealBundle B' F' ι')
    (NZ : NormLike Z) (NZ' : NormLike Z') {n : ℕ} (hn : 2 ≤ n)
    (g : C(Z'.TotalSpace, Z.TotalSpace))
    (hg : ∀ p : Z'.TotalSpace, p ∈ Work.Thom.zeroComplement Z' →
      g p ∈ Work.Thom.zeroComplement Z)
    (J : C(OnePoint Z'.TotalSpace, OnePoint Z.TotalSpace))
    (hJ : ∀ p : Z'.TotalSpace, J (OnePoint.some p) = OnePoint.some (g p))
    (hJinf : J OnePoint.infty = OnePoint.infty)
    (a : Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z)) :
    compPullZ Z' NZ' n
        (relCohOfAbsZ Z' NZ' hn ((Work.Thom.CohMap J ℤ n).hom (PhiZ Z NZ hn a)))
      = (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hg
          ℤ n).hom a := by
  change ThetaZ Z' NZ' hn ((Work.Thom.CohMap J ℤ n).hom (PhiZ Z NZ hn a)) = _
  rw [thetaZNatural Z Z' NZ NZ' hn g hg J hJ hJinf (PhiZ Z NZ hn a), ThetaZ_PhiZ]

end

end Work.ThomBordism
