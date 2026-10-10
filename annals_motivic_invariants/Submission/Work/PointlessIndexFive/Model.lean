/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.PointlessIndexFive.finiteType_zeroComponent
import Submission.Work.PointlessIndexFive.exists_zeroComponentRingEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The projective model layer

The `TorsorExistence` chapter's `NOTES.md` §2 states that Mathlib has *no* smooth proper curve over
a field — "even `ℙ¹`, which Mathlib has as `Proj`, has `IsProper` but no `Smooth` /
`GeometricallyIntegral` instance and no `topologicalKrullDim = 1`".  This file makes the
projective route concrete and records exactly how much of that is now available.

## What is proved here (sorry-free)

* `instGradedAlgebra`: `MvPolynomial.homogeneousSubmodule` carries Mathlib's
  `MvPolynomial.gradedAlgebra` as a (low priority, global) instance, so that `Proj` can be formed
  from it directly.  Mathlib keeps this as a `local instance` because other weight functions give
  other gradings; exposing it is what makes `Proj` usable for `ℙⁿ`.
* `projectiveSpace 𝕜 n` — the projective `n`-space `Proj 𝕜[X₀,…,Xₙ]` as a scheme;
* `projectiveSpaceToSpec` — its structure morphism to `Spec 𝕜`, obtained from Mathlib's
  `Proj.toSpecZero` by transporting along the ring isomorphism between the constants and `𝕜`
  (`exists_zeroComponentRingEquiv`);
* `isProper_projectiveSpaceToSpec`, `locallyOfFiniteType_projectiveSpaceToSpec`,
  `quasiCompact_projectiveSpaceToSpec`, `isSeparated_projectiveSpaceToSpec` — properness, finite
  presentation, quasicompactness and separatedness of that morphism, all from Mathlib's
  `AlgebraicGeometry.Proj` (`ProjectiveSpectrum/Proper.lean`) together with
  `finiteType_zeroComponent`;
* `isIntegral_projectiveSpace` and `variety_projectiveSpace`: `ℙⁿ_𝕜` is a `MotivicInvariants.Variety`
  as soon as it is geometrically integral over `𝕜`.

**Consequence for the parent chapter.**  The missing piece for `IsProper` in `NOTES.md` §2 of
`TorsorExistence` does *not* exist: properness of the projective model (and of any `Proj` of a
finitely generated graded algebra) is available.  What is missing is `Smooth`,
`GeometricallyIntegral` and the dimension statement.

## What is *not* proved here

`ProjectiveModelGap 𝕜 n` names the remaining three items for the projective model itself, and
`HasPlaneCurveModel 𝕜` names the corresponding statement for a *plane curve*, which is what the
configuration `C(𝕜) = ∅` needs.  Neither is available in the pinned Mathlib:

* `Smooth`: Mathlib's `Smooth` is a `HasRingHomProperty @Smooth RingHom.Smooth`; it is Zariski-local
  on source and target, so for `ℙⁿ` it would follow from the chart computation
  `Proj.projIsoSpec` (`D₊(Xᵢ) ≅ Spec 𝕜[y₁,…,yₙ] = 𝔸ⁿ`) together with the (available)
  `Smooth (𝔸ⁿ ↘ Spec 𝕜)`.  For a hypersurface `Proj 𝕜[X,Y,Z]/(f)` one needs in addition the
  Jacobian criterion (`RingTheory/Smooth/Local.lean`, `RingTheory/RingHom/StandardSmooth.lean`).
* `GeometricallyIntegral`: needs `IsIntegral` of the base change of the model to an algebraic
  closure, i.e. irreducibility over the algebraic closure plus reducedness.
* `topologicalKrullDim = 1`: Mathlib has `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` but no
  dimension theory of `Proj` at all (`dim Proj A = dim A - 1` for a standard graded algebra).

See `NOTES.md` §4 for the roadmap.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open CategoryTheory AlgebraicGeometry

namespace Work.PointlessIndexFive

noncomputable section

/-- `MvPolynomial.homogeneousSubmodule σ 𝕜` carries Mathlib's standard degree grading.  Mathlib
keeps `MvPolynomial.gradedAlgebra` as a `local instance` (other weight functions give other
gradings); we expose it at low priority so that `Proj (homogeneousSubmodule σ 𝕜)` elaborates. -/
instance instGradedAlgebra (𝕜 : Type) [CommSemiring 𝕜] (σ : Type) :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ 𝕜) :=
  MvPolynomial.gradedAlgebra

/-! ## 1. The projective space `ℙⁿ` as a scheme over `𝕜` -/

/-- The projective `n`-space over `𝕜`, as `Proj` of the standard graded polynomial ring in `n + 1`
variables. -/
noncomputable def projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)

/-- The chosen ring isomorphism between the degree-`0` part of the standard grading and `𝕜`
(reading off the constant coefficient). -/
noncomputable def zeroComponentEquiv (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜 0) ≃+* 𝕜 :=
  (exists_zeroComponentRingEquiv 𝕜 (Fin (n + 1))).choose

/-- The structure morphism `ℙⁿ_𝕜 ⟶ Spec 𝕜`: Mathlib's `Proj.toSpecZero` composed with the
spectrum of the isomorphism between the constants and `𝕜`. -/
noncomputable def projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    projectiveSpace 𝕜 n ⟶ Spec (CommRingCat.of 𝕜) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) ≫
    Spec.map ((zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv)

instance projectiveSpaceOver (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    (projectiveSpace 𝕜 n).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨projectiveSpaceToSpec 𝕜 n⟩

/-! ## 2. The instances available in Mathlib -/

/-- `ℙⁿ_𝕜` is proper over `Spec 𝕜`: Mathlib's `IsProper (Proj.toSpecZero 𝒜)`
(`ProjectiveSpectrum/Proper.lean`) transported along the isomorphism between the constants and
`𝕜`.  This is the fact `TorsorExistence/NOTES.md` §2 records as available, made explicit here. -/
theorem isProper_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsProper (projectiveSpaceToSpec 𝕜 n) := by
  haveI := finiteType_zeroComponent 𝕜 (Fin (n + 1))
  haveI : IsProper
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)) := inferInstance
  haveI : IsProper (Spec.map ((zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv)) := inferInstance
  show IsProper (Proj.toSpecZero _ ≫ Spec.map _)
  infer_instance

/-- `ℙⁿ_𝕜` is locally of finite presentation (indeed of finite type) over `Spec 𝕜`. -/
theorem locallyOfFiniteType_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    LocallyOfFiniteType (projectiveSpaceToSpec 𝕜 n) := by
  haveI := finiteType_zeroComponent 𝕜 (Fin (n + 1))
  haveI : LocallyOfFiniteType
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)) := inferInstance
  haveI : LocallyOfFiniteType (Spec.map ((zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv)) :=
    inferInstance
  show LocallyOfFiniteType (Proj.toSpecZero _ ≫ Spec.map _)
  infer_instance

/-- `ℙⁿ_𝕜` is quasicompact over `Spec 𝕜`. -/
theorem quasiCompact_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    QuasiCompact (projectiveSpaceToSpec 𝕜 n) := by
  haveI := finiteType_zeroComponent 𝕜 (Fin (n + 1))
  haveI : QuasiCompact
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)) := inferInstance
  haveI : QuasiCompact (Spec.map ((zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv)) := inferInstance
  show QuasiCompact (Proj.toSpecZero _ ≫ Spec.map _)
  infer_instance

/-- `ℙⁿ_𝕜` is separated over `Spec 𝕜`. -/
theorem isSeparated_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsSeparated (projectiveSpaceToSpec 𝕜 n) := by
  haveI : IsSeparated (Spec.map ((zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv)) := inferInstance
  show IsSeparated (Proj.toSpecZero _ ≫ Spec.map _)
  infer_instance

/-- `ℙⁿ_𝕜` is integral as soon as it is geometrically integral over `Spec 𝕜` (a field base). -/
theorem isIntegral_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (h : GeometricallyIntegral (projectiveSpaceToSpec 𝕜 n)) : IsIntegral (projectiveSpace 𝕜 n) :=
  GeometricallyIntegral.isIntegral_of_subsingleton (projectiveSpaceToSpec 𝕜 n)


/-- **`ℙⁿ_𝕜` is a variety over `𝕜`** as soon as the (still missing) geometric integrality is
supplied.  All the other fields of `MotivicInvariants.Variety` are available from Mathlib. -/
noncomputable def variety_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (h : GeometricallyIntegral (projectiveSpaceToSpec 𝕜 n)) :
    MotivicInvariants.Variety 𝕜 (projectiveSpace 𝕜 n) := by
  haveI : IsIntegral (projectiveSpace 𝕜 n) := isIntegral_projectiveSpace 𝕜 n h
  haveI : IsSeparated (projectiveSpace 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) :=
    isSeparated_projectiveSpaceToSpec 𝕜 n
  haveI : LocallyOfFiniteType (projectiveSpace 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) :=
    locallyOfFiniteType_projectiveSpaceToSpec 𝕜 n
  haveI : QuasiCompact (projectiveSpace 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) :=
    quasiCompact_projectiveSpaceToSpec 𝕜 n
  exact ⟨⟩

/-! ## 3. The named gaps of the model layer -/

/-- **The open items of the projective model layer.**  `ℙⁿ_𝕜` is proper, separated, locally of
finite presentation and quasicompact over `Spec 𝕜` (see above), but the pinned Mathlib has no
`smooth`, no `geometrically integral` and no dimension theory for `Proj`.  This `Prop` names
exactly the three missing facts.

For `n = 1` these are precisely what `TorsorExistence/NOTES.md` §2 reports as missing for `ℙ¹`, and
they are the reason no smooth proper curve exists in Mathlib. -/
def ProjectiveModelGap (𝕜 : Type) [Field 𝕜] (n : ℕ) : Prop :=
  Smooth (projectiveSpaceToSpec 𝕜 n) ∧ GeometricallyIntegral (projectiveSpaceToSpec 𝕜 n) ∧
    topologicalKrullDim (projectiveSpace 𝕜 n) = n

/-- The model object that a future stretch must produce in order to build the configuration
`C(𝕜) = ∅` used by `PointlessIndexFiveCurve`: a smooth projective *curve* over `𝕜`.  This is
`ProjectiveModelGap 𝕜 1`. -/
def SmoothProjectiveCurveModel (𝕜 : Type) [Field 𝕜] : Prop :=
  ProjectiveModelGap 𝕜 1

end

end Work.PointlessIndexFive
