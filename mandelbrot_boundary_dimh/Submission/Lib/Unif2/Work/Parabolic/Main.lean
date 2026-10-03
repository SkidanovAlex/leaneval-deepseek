import Submission.Lib.Unif2.Work.Parabolic.Deps
import Submission.Lib.Unif2.Work.Parabolic.Reduction
import Submission.Lib.Unif2.Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact
import Submission.Lib.Unif2.Work.Parabolic.isParabolic_complex
import Submission.Lib.Unif2.Work.Parabolic.uniformization_of_greenFunctionAt

/-!
# The parabolic case of the uniformization theorem

This is the main module of `Submission/Work/Parabolic/`.  It states the parabolic branch of the
uniformization theorem — "no Green function ⟹ `X ≅ ℂ`" — in the form in which it is true and
provable, and it records (in `not_exists_hasGreenFunctionWeak_of_not_compact`, and in the
certificate at the end of this file) why the *raw* form of the hypothesis that was originally
requested cannot be used.

## The two notions of Green function

A Green function on a Riemann surface `X` with pole `z₀` is a positive harmonic function on
`X \ {z₀}`, with a logarithmic singularity at `z₀`, which tends to `0` at the ideal boundary.  The
correct formalisation of "tends to `0` at the ideal boundary" is that the superlevel sets
`{x | ε ≤ E x}` are **relatively compact** (`Work.Parabolic.IsGreenFunctionAt`, `Basic.lean`).

The stronger-looking condition that the superlevel sets themselves be **compact** — which is what
`Submission.HasGreenFunctionWeak` (`Submission/GreenInterface.lean`) and hence the hypothesis `h`
of the originally requested statement ask for — is *unsatisfiable* as soon as `X` is non-compact
and connected, because `E : X → ℝ` must be finite at the pole:
`Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact`.  Consequently the originally
requested statement (`h` ⟹ `X ≅ ℂ`) is **false**: at `X = ℍ` the hypothesis `h` holds (indeed it
holds at *every* non-compact connected `X`), the fundamental-group hypothesis holds (`ℍ` is simply
connected), and `ℍ ≇ ℂ`.

## What is proved here

* `plane_of_no_greenFunction` — the parabolic branch, with the corrected hypothesis, from the two
  classical inputs (the topological/`Work.Spine` input `SimplyConnectedSpace X` and the
  ABS/`Work.SimplyConnected` input "there is a non-constant injective holomorphic map `X → ℂ`").
* `plane_of_no_greenFunction_of_dichotomy` — the same, with the simply connected case of
  uniformization (`X ≅ ℂ ∨ X ≅ ℍ`) as the second input.
* `raw_shape_fails_at_upperHalfPlane` — the certificate that the raw shape of the requested
  statement is false.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical
open Submission

namespace Work.Parabolic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The parabolic case of the uniformization theorem.**  A non-compact connected second countable
Riemann surface with no Green function (in the relative-compactness sense), whose fundamental group
has no non-trivial homomorphism to `ℝ`, and which admits a non-constant injective holomorphic map
into `ℂ`, is biholomorphic to `ℂ`.

The two "classical inputs" are explicit hypotheses:
* `SimplyConnectedSpace X` — the output of `Work.Spine`
  (`Submission.simplyConnectedSpace_of_subsingleton_hom_toReal`), obtained from the challenge
  hypothesis `Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)`;
* `φ` — the output of the ABS/`Work.SimplyConnected` route (Theorem "inj" of Anghel–Bruin–Stan:
  every non-compact simply connected Riemann surface is biholomorphic to a domain in `ℂ`), so that
  a non-constant injective holomorphic `φ : X → ℂ` exists. -/
theorem plane_of_no_greenFunction [SimplyConnectedSpace X] (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), IsGreenFunctionAt z₀ E)
    {φ : X → ℂ} (hφ : HolomorphicOnX φ univ) (hinj : Function.Injective φ) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  nonempty_diffeomorph_plane_of_isParabolic_of_injective_holomorphic (x₀ := x) h hφ hinj

/-- **The parabolic branch from the simply connected case of uniformization.**  If `X` is parabolic
and the dichotomy `X ≅ ℂ ∨ X ≅ ℍ` is available (`Work.SimplyConnected`), then `X ≅ ℂ`. -/
theorem plane_of_no_greenFunction_of_dichotomy (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), IsGreenFunctionAt z₀ E)
    (hdich : Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  nonempty_diffeomorph_plane_of_isParabolic_of_dichotomy h hdich

/-- **The fundamental-group hypothesis of the challenge holds for the upper half plane**, which is
why the upper half plane is a counterexample to the raw shape of the parabolic branch. -/
theorem upperHalfPlane_subsingleton_hom (x : UpperHalfPlane) :
    Subsingleton (Additive (FundamentalGroup UpperHalfPlane x) →+ ℝ) := by
  haveI : SimplyConnectedSpace UpperHalfPlane :=
    SimplyConnectedSpace.ofContractible UpperHalfPlane
  infer_instance

/-- **The raw (compact-superlevel) hypothesis of the requested statement is automatic at `ℍ`.** -/
theorem raw_hypothesis_at_upperHalfPlane (z₀ : UpperHalfPlane) :
    ¬ ∃ E : UpperHalfPlane → ℝ, Submission.HasGreenFunctionWeak z₀ E :=
  not_exists_hasGreenFunctionWeak_of_not_compact
    (X := UpperHalfPlane) Submission.Helpers.not_compactSpace_upperHalfPlane z₀

/-! ## The (repaired) Green-function route to the uniformization theorem -/

/-- **The Green-function route of the uniformization theorem, with the corrected notion of Green
function.**  This is the shape of `Submission.uniformization_via_green` after replacing the raw
(unsatisfiable) predicate `Submission.HasGreenFunctionWeak` by `IsGreenFunctionAt`, and with the
three parallel inputs explicit:

* `hG0` — `SimplyConnectedSpace X`, from the challenge hypothesis (`Work.Spine`);
* `hABS` — a non-constant injective holomorphic map `X → ℂ` (`Work.SimplyConnected`/ABS);
* `hmod` — the holomorphic modulus of a Green function (`Work.Modulus`).

In the hyperbolic case the (corrected) endgame `uniformization_of_greenFunctionAt` applies; in the
parabolic case the branch proved here (`plane_of_no_greenFunction`) applies. -/
theorem uniformization_via_green_corrected (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (hG0 : SimplyConnectedSpace X)
    (hABS : ∃ φ : X → ℂ, HolomorphicOnX φ univ ∧ Function.Injective φ)
    (hmod : ∀ (z₀ : X) (E : X → ℝ), IsGreenFunctionAt z₀ E →
      ∃ Φ : X → ℂ, HolomorphicOnX Φ univ ∧ HasLogPoleAt z₀ Φ ∧
        ∀ y : X, y ≠ z₀ → ‖Φ y‖ = Real.exp (-(E y))) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  by_cases h : ∃ (z₀ : X) (E : X → ℝ), IsGreenFunctionAt z₀ E
  · obtain ⟨z₀, E, hE⟩ := h
    obtain ⟨Φ, hΦ, hpole, hmod'⟩ := hmod z₀ E hE
    exact uniformization_of_greenFunctionAt (X := X) hX hE hΦ hmod' hpole
  · obtain ⟨φ, hφ, hinj⟩ := hABS
    haveI := hG0
    exact Or.inl (plane_of_no_greenFunction (X := X) hX x h hφ hinj)

/-! ## The raw shape of the requested statement is false -/

/-- **`ℍ` is not biholomorphic to `ℂ`**, derived from the parabolicity of `ℂ`
(`isParabolic_complex`) and the exclusion of the hyperbolic branch
(`isParabolic.not_nonempty_diffeomorph_upperHalfPlane` at `X = ℂ`). -/
theorem not_nonempty_diffeomorphism_upperHalfPlane_plane_of_isParabolic (h : IsParabolic ℂ) :
    ¬ Nonempty (UpperHalfPlane ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  fun ⟨Φ⟩ => isParabolic.not_nonempty_diffeomorph_upperHalfPlane (X := ℂ) h ⟨Φ.symm⟩

/-- **`ℍ` is not biholomorphic to `ℂ`.** -/
theorem upperHalfPlane_not_biholomorphic_plane :
    ¬ Nonempty (UpperHalfPlane ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  not_nonempty_diffeomorphism_upperHalfPlane_plane_of_isParabolic isParabolic_complex

/-- **The hypothesis `h` of the requested statement holds at `ℍ` and the conclusion fails there**:
the raw (compact superlevel set) condition is unsatisfiable on every non-compact connected complex
one-manifold, whereas `ℍ ≄ ℂ`.  Hence the statement "`h` ⟹ `X ≅ ℂ`" is *false*, not merely
unproved: the raw condition is not a formalisation of "no Green function" (it is equivalent, on
non-compact `X`, to `False`). -/
theorem raw_shape_hypothesis_holds_and_conclusion_fails :
    (∀ (z₀ : UpperHalfPlane) (E : UpperHalfPlane → ℝ), ¬ Submission.HasGreenFunctionWeak z₀ E) ∧
      ¬ Nonempty (UpperHalfPlane ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  ⟨fun z₀ E hw => raw_hypothesis_at_upperHalfPlane z₀ ⟨E, hw⟩,
    upperHalfPlane_not_biholomorphic_plane⟩

/-- **The requested implication is false.**  With the raw (compact superlevel set) hypothesis, the
conclusion `X ≅ ℂ` fails at `X = ℍ`, even though every other hypothesis of the requested statement
holds there (`ℍ` is non-compact, connected, second countable, and simply connected, so
`Subsingleton (Additive (FundamentalGroup ℍ x) →+ ℝ)`). -/
theorem not_plane_of_no_greenFunction_raw :
    ¬ ((∀ (z₀ : UpperHalfPlane) (E : UpperHalfPlane → ℝ),
          ¬ Submission.HasGreenFunctionWeak z₀ E) →
        Nonempty (UpperHalfPlane ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)) :=
  fun h => upperHalfPlane_not_biholomorphic_plane
    (h (fun z₀ E hw => raw_hypothesis_at_upperHalfPlane z₀ ⟨E, hw⟩))

end Work.Parabolic
