import Submission.Work.ThomBordism.absThomCompareNatural
import Submission.Work.ThomBordism.thomMapPullbackPair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The description of the universal classes (TUBULAR README §17) in its final form

Combining the naturality of the canonical comparison `PhiZ` with the class arithmetic
`thomMapPullbackPair` gives the identity on which the two Hurewicz pairings of
`Work.Tubular.TubeThomRep` depend: for the bundle map `g : ν → γ` of the Gauss data (with one-point
extension `J`), the pullback of the universal class `thomMap γ k U_γ 8 x = π_γ^*(x) ⌣ U_γ` is the
class `π_ν^*(gauss^* x) ⌣ g^*(U_γ)` of the normal bundle.

With `Z = γ_{k,10}`, `U_γ = Grassmann.tautologicalThomClass k 10`, `x = Grassmann.p1Sq k 10`,
`Z' = ν` the normal bundle of an embedded `V`, and `Φ := PhiZ γ …` (the *canonical* comparison, a
`noncomputable def`, not a `Classical.choose`), the left-hand side is exactly the ν-side class of
`Work.Tubular.tubeThomRep_of_nuPairing`.  See `NOTES_round15_H4.md` §2–§4.
-/

open CategoryTheory
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [TopologicalSpace B'] [CompactSpace B'] [T2Space B']
variable {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] {ι ι' : Type}

/-- **The pullback of the universal class is the geometric class of the normal bundle.**

`compPullZ ∘ relCohOfAbsZ ∘ J^* ∘ PhiZ` of `thomMap Z n τ 8 x` is
`π_{Z'}^*(f^*x) ⌣ g^*(τ)`.  In the application the left-hand side is the ν-side class
`compPull E (relCoh_of_abs E (J^*(Φ a)))` of `Work.Tubular.tubeThomRep_of_nuPairing`, and the right
hand side is its geometric description. -/
theorem universalClassPullbackPair
    (Z : RealBundle B F ι) (Z' : RealBundle B' F' ι')
    (f : C(B', B)) (g : C(Z'.TotalSpace, Z.TotalSpace))
    (hg : ∀ p : Z'.TotalSpace, p ∈ Work.Thom.zeroComplement Z' →
      g p ∈ Work.Thom.zeroComplement Z)
    (hbproj : ∀ p : Z'.TotalSpace, Work.Thom.bundleProj Z (g p) = f (Work.Thom.bundleProj Z' p))
    (NZ : NormLike Z) (NZ' : NormLike Z')
    (J : C(OnePoint Z'.TotalSpace, OnePoint Z.TotalSpace))
    (hJ : ∀ p : Z'.TotalSpace, J (OnePoint.some p) = OnePoint.some (g p))
    (hJinf : J OnePoint.infty = OnePoint.infty)
    (n : ℕ) (τ : Work.Thom.OpenThom Z n) (x : Work.Thom.Coh ℤ 8 B) :
    compPullZ Z' NZ' (8 + n)
        (relCohOfAbsZ Z' NZ' (show 2 ≤ 8 + n from by omega)
          ((Work.Thom.CohMap J ℤ (8 + n)).hom
            (PhiZ Z NZ (show 2 ≤ 8 + n from by omega) (Work.Thom.thomMap Z n τ 8 x))))
      = Work.Thom.mixedCupC ℤ (Work.Thom.zeroComplement Z') 8 n
          ((Work.Thom.CohMap (Work.Thom.bundleProj Z') ℤ 8).hom
            ((Work.Thom.CohMap f ℤ 8).hom x))
          ((Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hg
            ℤ n).hom τ) := by
  rw [compPullZ_relCohOfAbsZ_PhiZ Z Z' NZ NZ' (show 2 ≤ 8 + n from by omega) g hg J hJ hJinf
    (Work.Thom.thomMap Z n τ 8 x)]
  exact thomMapPullbackPair Z Z' f g hg hbproj n 8 τ x

end

end Work.ThomBordism
