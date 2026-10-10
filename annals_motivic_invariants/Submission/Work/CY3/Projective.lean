import Mathlib
import ChallengeDeps
import Submission.Work.PointlessIndexFive.Model
import Submission.Work.Twist.isIntegral_projectiveSpace
import Submission.Work.CY3.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Projective` — projective space, the projective line, and `ℙⁿ`-fibrations

Mathlib has `Proj` of a graded ring (`AlgebraicGeometry.Proj`) but does not *instantiate* it: there
is no projective space `ℙⁿ` and in particular no projective line `ℙ¹` as a scheme *in Mathlib*.
This workspace does have it, in the sibling area `Submission/Work/PointlessIndexFive`
(`Work.PointlessIndexFive.projectiveSpace`, `= Proj 𝕜[X₀,…,Xₙ]`), with the structure morphism
`projectiveSpaceToSpec`, the instances `IsProper`, `LocallyOfFiniteType`, `QuasiCompact`,
`IsSeparated` (`Work.PointlessIndexFive.Model`), and — from
`Submission/Work/Twist/isIntegral_projectiveSpace` — `IsIntegral`.  This file **re-exports that
object** under the names used by the CY3 area:

* `Work.CY3.ProjectiveSpace 𝕜 n` — `ℙⁿ_𝕜`;
* `Work.CY3.ProjectiveLine 𝕜` — `ℙ¹_𝕜`, the fibre of the two `G₂`-projections `G/B → G/P`,
  `G/B → G/P'` of `thm:CY3`;
* `Work.CY3.variety_ProjectiveSpace` — `ℙⁿ_𝕜` is a `Variety` over `𝕜` (assembled from the lemmas
  above), so that `ℙ¹` can be used wherever the paper uses it;

and it records the **`ℙ¹`-fibration structure** of the CY3 projections in a form Mathlib *can*
state: `f : X ⟶ Y` is a `ℙⁿ`-fibration when every scheme-theoretic fibre `f.fiber y`
(`Mathlib.AlgebraicGeometry.Fiber`) is isomorphic to `ℙⁿ` over the residue field of `y`.  The
*fact* that `G/B → G/P` and `G/B → G/P'` are `ℙ¹`-fibrations is one of the named inputs of Layer 1
(`Work.CY3.G2Grassmannian`); what is recorded here is the notion itself and its
(unconditional, field-independent) API, so that the input is not an opaque `Prop`.

This is the "provable parts" half of the honest split of Layer 1 of the CY3 area: the existence of
a `ℙ¹`-fibration structure over the `G₂`-Grassmannians is an input (there is no `G₂` in Mathlib),
while the notion of a `ℙⁿ`-fibration and everything below is defined and proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Projective `n`-space over a field `𝕜`**: `Proj 𝕜[X₀,…,Xₙ]` (standard degree grading),
re-exported from the sibling area `Submission/Work/PointlessIndexFive`, where it is
`Work.PointlessIndexFive.projectiveSpace`.  Using the project's ℙⁿ rather than a second copy keeps
one object of that name in the workspace. -/
noncomputable abbrev ProjectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) : Scheme :=
  Work.PointlessIndexFive.projectiveSpace 𝕜 n

/-- **The projective line over `𝕜`**: `Proj 𝕜[X₀,X₁]`, the fibre of the `ℙ¹`-fibrations
`G/B → G/P`, `G/B → G/P'` of `thm:CY3`. -/
noncomputable abbrev ProjectiveLine (𝕜 : Type) [Field 𝕜] : Scheme := ProjectiveSpace 𝕜 1

/-- The structure morphism `ℙⁿ_𝕜 ⟶ Spec 𝕜` (`Proj.toSpecZero` composed with the identification of
the degree-zero part with `𝕜`). -/
noncomputable abbrev projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    ProjectiveSpace 𝕜 n ⟶ Spec (.of 𝕜) :=
  Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n

instance projectiveSpaceOver (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    (ProjectiveSpace 𝕜 n).Over (Spec (.of 𝕜)) :=
  ⟨projectiveSpaceToSpec 𝕜 n⟩

/-- `ℙⁿ_𝕜` is proper over `Spec 𝕜`. -/
theorem isProper_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsProper (projectiveSpaceToSpec 𝕜 n) :=
  Work.PointlessIndexFive.isProper_projectiveSpaceToSpec 𝕜 n

/-- `ℙⁿ_𝕜` is locally of finite type over `Spec 𝕜`. -/
theorem locallyOfFiniteType_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    LocallyOfFiniteType (projectiveSpaceToSpec 𝕜 n) :=
  Work.PointlessIndexFive.locallyOfFiniteType_projectiveSpaceToSpec 𝕜 n

/-- `ℙⁿ_𝕜` is quasicompact over `Spec 𝕜`. -/
theorem quasiCompact_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    QuasiCompact (projectiveSpaceToSpec 𝕜 n) :=
  Work.PointlessIndexFive.quasiCompact_projectiveSpaceToSpec 𝕜 n

/-- `ℙⁿ_𝕜` is separated over `Spec 𝕜`. -/
theorem isSeparated_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsSeparated (projectiveSpaceToSpec 𝕜 n) :=
  Work.PointlessIndexFive.isSeparated_projectiveSpaceToSpec 𝕜 n

/-- `ℙⁿ_𝕜` is integral (irreducible and reduced), from
`Work.Twist.isIntegral_projectiveSpace`. -/
theorem isIntegral_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsIntegral (ProjectiveSpace 𝕜 n) :=
  Work.Twist.isIntegral_projectiveSpace 𝕜 n

/-- **`ℙⁿ_𝕜` is a `𝕜`-variety** in the sense of the challenge (`MotivicInvariants.Variety`:
integral, separated, locally of finite type and quasicompact over `Spec 𝕜`), assembled from the
lemmas above.  The same content is available in the sibling area as the *definition*
`Work.Twist.variety_projectiveSpace_uncond` (`Submission/Work/Twist/ProjModel.lean`); it is
declared as an *instance* here so that `ℙⁿ` and `ℙ¹` are usable as varieties by instance search
(e.g. `ℙ¹` in `Work.CY3.IsPnFibration`). -/
instance variety_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) : Variety 𝕜 (ProjectiveSpace 𝕜 n) := by
  haveI : IsIntegral (ProjectiveSpace 𝕜 n) := isIntegral_projectiveSpace 𝕜 n
  haveI : IsSeparated (ProjectiveSpace 𝕜 n ↘ Spec (.of 𝕜)) :=
    isSeparated_projectiveSpaceToSpec 𝕜 n
  haveI : LocallyOfFiniteType (ProjectiveSpace 𝕜 n ↘ Spec (.of 𝕜)) :=
    locallyOfFiniteType_projectiveSpaceToSpec 𝕜 n
  haveI : QuasiCompact (ProjectiveSpace 𝕜 n ↘ Spec (.of 𝕜)) :=
    quasiCompact_projectiveSpaceToSpec 𝕜 n
  exact ⟨⟩

/-- `f : X ⟶ Y` is a **`ℙⁿ`-fibration**: every scheme-theoretic fibre `f.fiber y` is isomorphic to
`ℙⁿ` over the residue field `κ(y)`.

(We do not require the isomorphism to be an isomorphism over `Spec κ(y)`; requiring only an
isomorphism of schemes makes the notion slightly weaker — hence more permissive — than
"`ℙⁿ`-bundle over `Y`", which is what the paper uses for `G/B → G/P` and `G/B → G/P'`.  All the
inputs of the CY3 area are stated in this permissive form.) -/
def IsPnFibration {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ y : Y, Nonempty (f.fiber y ≅ ProjectiveSpace (Y.residueField y) n)

/-- `f : X ⟶ Y` is a **`ℙ¹`-fibration**: the case `n = 1` of `IsPnFibration`, which is the
structure of the two projections `G/B → G/P`, `G/B → G/P'` of `thm:CY3` (paper: "Since
`p_ℚ : G_ℚ/B_ℚ → G_ℚ/P_ℚ` is a `ℙ¹`-fibration, so is `p : G/B → G/P`"). -/
abbrev IsP1Fibration {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop := IsPnFibration f 1

namespace IsPnFibration

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {n : ℕ}

/-- The fibre of a `ℙⁿ`-fibration at a point. -/
theorem fiber (h : IsPnFibration f n) (y : Y) :
    Nonempty (f.fiber y ≅ ProjectiveSpace (Y.residueField y) n) := h y

/-- The definition, as an `iff`, for rewriting. -/
theorem iff (n : ℕ) :
    IsPnFibration f n ↔ ∀ y : Y, Nonempty (f.fiber y ≅ ProjectiveSpace (Y.residueField y) n) :=
  Iff.rfl

/-- **The generic fibre.**  For an irreducible base `Y`, the fibre over the generic point is a
`ℙⁿ` over the function field `κ(η)`.  In the CY3 construction this is the fibre `F_𝕜 ≃ ℙ¹_𝕜` on
which the paper computes `deg(L_𝕜)|_{F_𝕜} = 1`. -/
theorem genericFiber [IrreducibleSpace Y] (h : IsPnFibration f n) :
    Nonempty (f.fiber (genericPoint Y) ≅ ProjectiveSpace (Y.residueField (genericPoint Y)) n) :=
  h _

end IsPnFibration

namespace IsP1Fibration

variable {X Y : Scheme.{0}} {f : X ⟶ Y}

/-- The fibre of a `ℙ¹`-fibration at a point is a projective line. -/
theorem fiber (h : IsP1Fibration f) (y : Y) :
    Nonempty (f.fiber y ≅ ProjectiveLine (Y.residueField y)) :=
  h y

/-- The generic fibre of a `ℙ¹`-fibration over an irreducible base: a `ℙ¹` over the function field
of the base. -/
theorem genericFiber [IrreducibleSpace Y] (h : IsP1Fibration f) :
    Nonempty (f.fiber (genericPoint Y) ≅ ProjectiveLine (Y.residueField (genericPoint Y))) :=
  h _

/-- A `ℙ¹`-fibration is a `ℙⁿ`-fibration with `n = 1` — recorded so that the `n`-indexed API can
be used. -/
theorem isPnFibration (h : IsP1Fibration f) : IsPnFibration f 1 := h

end IsP1Fibration

end

end Work.CY3
