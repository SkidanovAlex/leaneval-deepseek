import Submission.UnifDeps
import Submission.RiemannSurface
import Submission.GreenInterface

/-!
# The parabolic (`no Green function`) case: definitions

Subproject `Work.Parabolic`: the branch of the uniformization theorem in which `X` carries *no*
Green function, i.e. the branch in which a simply connected non-compact `X` is biholomorphic to `ℂ`.

## Green functions: the correct (relatively compact) notion

A Green function on `X` with pole `z₀` is a positive harmonic function on `X \ {z₀}` with a
logarithmic singularity at `z₀` which tends to `0` at the ideal boundary of `X`.  The last
condition has to be formalised as **relative compactness of the superlevel sets**:
`{x | ε ≤ E x}` must be *contained in* a compact set, for every `ε > 0` — equivalently the
*closure* of `{x | ε ≤ E x}` is compact.  This is *not* the same as requiring `{x | ε ≤ E x}`
itself to be compact: the superlevel set of a genuine Green function is a *punctured* neighbourhood
of the pole (for `ε` above the value assigned to the pole), and punctured discs are not closed, so
they are not compact.

That distinction is load-bearing, and it is the reason for the definitions below:

* `IsGreenFunctionAt z₀ E` — `E > 0` off `z₀`, harmonic off `z₀`, and `closure {x | ε ≤ E x}`
  compact for every `ε > 0`.  This is the *correct* notion; it is satisfied by the Green function
  of the upper half plane (`hasGreenFunctionAt_iUHP`) and is a conformal invariant
  (`Transport.lean`).

* `HasGreenFunctionAt z₀`, `HasGreenFunction X`, `IsParabolic X`, `IsHyperbolic X` — the pointwise
  and global versions, and the dichotomy.  `IsParabolic X` is the hypothesis of the parabolic case
  of uniformization.

* The interface `Submission.HasGreenFunctionWeak z₀ E` (`Submission/GreenInterface.lean`) asks for
  `IsCompact {x | ε ≤ E x}` — *without* the closure, i.e. it demands that `E` be finite at the
  pole in the strong sense.  **That predicate is unsatisfiable** on every non-compact connected
  complex one-manifold: `not_exists_hasGreenFunctionWeak_of_not_compact` proves
  `¬ ∃ E, Submission.HasGreenFunctionWeak z₀ E`.  The relative-compactness formulation used here
  is the repair; `Submission.HasGreenFunctionWeak z₀ E → IsGreenFunctionAt z₀ E` is the easy
  bridge between the two.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical
open Submission

namespace Work.Parabolic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **`E` is a Green function on `X` with pole `z₀`** (relative-compactness formulation): `E` is
strictly positive at every point other than `z₀`, harmonic on `X \ {z₀}`, and for every `ε > 0` the
closure of the superlevel set `{x | ε ≤ E x}` is compact — equivalently, `E < ε` outside a compact
set. -/
def IsGreenFunctionAt (z₀ : X) (E : X → ℝ) : Prop :=
  (∀ x, x ≠ z₀ → 0 < E x) ∧ HarmonicOnX E (Set.univ \ {z₀}) ∧
    (∀ ε : ℝ, 0 < ε → IsCompact (closure {x : X | ε ≤ E x}))

/-- **`X` carries a Green function with pole `z₀`.** -/
def HasGreenFunctionAt (z₀ : X) : Prop := ∃ E : X → ℝ, IsGreenFunctionAt z₀ E

/-- **`X` carries a Green function** (with some pole). -/
def HasGreenFunction (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ z₀ : X, HasGreenFunctionAt z₀

/-- **`X` is parabolic**: it carries no Green function.  This is the "no Green function" case of
the uniformization theorem. -/
def IsParabolic (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ¬ HasGreenFunction X

/-- **`X` is hyperbolic**: it carries a Green function. -/
def IsHyperbolic (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  HasGreenFunction X

section Projections

variable {z₀ : X} {E : X → ℝ}

theorem IsGreenFunctionAt.pos (h : IsGreenFunctionAt (X := X) z₀ E) {x : X} (hx : x ≠ z₀) :
    0 < E x := h.1 x hx

theorem IsGreenFunctionAt.harmonic (h : IsGreenFunctionAt (X := X) z₀ E) :
    HarmonicOnX E (Set.univ \ {z₀}) := h.2.1

theorem IsGreenFunctionAt.isCompact_closure_level (h : IsGreenFunctionAt (X := X) z₀ E)
    {ε : ℝ} (hε : 0 < ε) : IsCompact (closure {x : X | ε ≤ E x}) := h.2.2 ε hε

/-- The relative-compactness condition, in the form "`E < ε` outside a compact set". -/
theorem IsGreenFunctionAt.exists_isCompact_subset (h : IsGreenFunctionAt (X := X) z₀ E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ ∀ x : X, x ∉ K → E x < ε :=
  ⟨closure {x : X | ε ≤ E x}, h.isCompact_closure_level hε,
    fun x hx => by
      by_contra hcon
      exact hx (subset_closure (by simpa using not_lt.mp hcon : ε ≤ E x))⟩

end Projections

/-- **Relative compactness, restated**: for a topologically well-behaved (locally compact)
`X`, `IsCompact (closure S)` is equivalent to `S` being contained in a compact set. -/
theorem isCompact_closure_iff_exists_isCompact_superset [T2Space X] {S : Set X} :
    IsCompact (closure S) ↔ ∃ K : Set X, IsCompact K ∧ S ⊆ K := by
  constructor
  · intro h
    exact ⟨closure S, h, subset_closure⟩
  · rintro ⟨K, hK, hSK⟩
    exact hK.of_isClosed_subset isClosed_closure (closure_minimal hSK hK.isClosed)

variable {z₀ : X} {E : X → ℝ} in
/-- **The bridge from the library interface** (for a `T2` space, so that closures of compact sets
are compact): `Submission.HasGreenFunctionWeak z₀ E` asks for
compact *superlevel sets* (not just compact closures), which is the stronger condition; it implies
`IsGreenFunctionAt z₀ E`. -/
theorem IsGreenFunctionAt.of_hasGreenFunctionWeak [T2Space X]
    (h : Submission.HasGreenFunctionWeak z₀ E) :
    IsGreenFunctionAt (X := X) z₀ E :=
  ⟨h.1, h.2.1, fun ε hε => (h.2.2 ε hε).closure⟩

end Work.Parabolic

/-! ## Global API -/

namespace Work.Parabolic

open Submission

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

theorem hasGreenFunctionAt_def {y₀ : Y} :
    HasGreenFunctionAt (X := Y) y₀ ↔ ∃ E : Y → ℝ, IsGreenFunctionAt y₀ E := Iff.rfl

theorem hasGreenFunction_def {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    HasGreenFunction Y ↔ ∃ y₀ : Y, HasGreenFunctionAt y₀ := Iff.rfl

theorem isParabolic_iff :
    IsParabolic Y ↔
      ¬ ∃ (y₀ : Y) (E : Y → ℝ), (∀ x, x ≠ y₀ → 0 < E x) ∧
        HarmonicOnX E (Set.univ \ {y₀}) ∧
        (∀ ε : ℝ, 0 < ε → IsCompact (closure {x : Y | ε ≤ E x})) := Iff.rfl

theorem isParabolic_iff_forall_not (h : IsParabolic Y) (y : Y) :
    ¬ HasGreenFunctionAt (X := Y) y := fun hy => h ⟨y, hy⟩

theorem hasGreenFunction_of_hasGreenFunctionAt {y₀ : Y}
    (h : HasGreenFunctionAt (X := Y) y₀) : HasGreenFunction Y := ⟨y₀, h⟩

theorem IsHyperbolic.not_isParabolic (h : IsHyperbolic Y) : ¬ IsParabolic Y := fun hp => hp h

theorem not_isParabolic_iff : ¬ IsParabolic Y ↔ HasGreenFunction Y := not_not

end Work.Parabolic
