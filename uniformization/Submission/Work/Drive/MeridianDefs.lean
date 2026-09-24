import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.SimplyConnected.ABS.periods_of_circleCharacter_trivial
import Submission.Work.Modulus.PeriodSetup

/-!
# The meridian of a point in a punctured Riemann surface

For a Riemann surface `X`, a point `z₀ : X` and an open set `D ∋ z₀` (a "disc" around `z₀`,
typically a simply connected chart ball), this module records the two elementary maps relating the
punctured complement `X ∖ {z₀}` (`Work.Modulus.puncturedOpens z₀`) to `D ∖ {z₀}`:

* `Work.Drive.toPunctured z₀ q hq` — a point `q ≠ z₀` of `X` read as a point of the punctured
  surface;
* `Work.Drive.inclSub z₀ D` — the inclusion `D ∖ {z₀} ↪ X ∖ {z₀}`, as a continuous map.

These are the two maps in terms of which the *meridian* of `z₀` — the homotopy class of a small
loop around `z₀` inside the disc `D` — enters the theory: the meridian is the image of the
fundamental group of `D ∖ {z₀}` under `FundamentalGroup.map (inclSub z₀ D)`.

The two target statements of the "meridian pair" are

* `Work.Drive.exists_int_hom_extends_meridian` (the *primitivity* of the meridian): every
  integer-valued homomorphism of `π₁(D ∖ {z₀})` extends to `π₁(X ∖ {z₀})`, for `X` non-compact —
  equivalently, the meridian is primitive in `H₁(π₁(X ∖ {z₀}))`;
* `Work.Drive.ker_inclMapP_le_normalClosure_meridian` (the van Kampen *kernel* statement): the
  kernel of `π₁(X ∖ {z₀}) → π₁(X)` is the normal closure of the image of `π₁(D ∖ {z₀})`.

Together with the invariance of the conjugate period homomorphism under conjugation (which holds
because the period homomorphism takes values in the abelian group `ℝ`), they imply that the periods
of the loops null-homotopic in `X` are the values of a *single* integer-valued homomorphism of
`π₁(X ∖ {z₀})` — the target of this module's parent file.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A point `q ≠ z₀` of `X`, read as a point of the punctured surface
`Work.Modulus.puncturedOpens z₀ = X ∖ {z₀}`. -/
def toPunctured (z₀ : X) (q : X) (h : q ∉ ({z₀} : Set X)) :
    ↥(Work.Modulus.puncturedOpens z₀) :=
  ⟨q, h⟩

/-- The inclusion `D ∖ {z₀} ↪ X ∖ {z₀}` as a continuous map, for `D : Set X`. -/
def inclSub (z₀ : X) (D : Set X) : C(↥(D \ {z₀}), ↥(Work.Modulus.puncturedOpens z₀)) :=
  ⟨fun x => toPunctured z₀ x.1 (by simpa using x.2.2), by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

end Work.Drive
