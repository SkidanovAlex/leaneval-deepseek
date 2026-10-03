/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The N5 ↔ N6 vocabulary converter

The analytic node N5 (`Work.ORVonNeumann`, the envelope `U(G)`) and the algebraic engine node N6
(`Work.ORHughesFree`, JZLA20 §2–§6) use *different but parallel* vocabularies for the same
notions.  This file records the translations, so that the analytic properties of `U(G)` can be
fed to the engine and the engine's conclusions can be read back.

| N5 (`Work.ORVonNeumann`)            | N6 (`Work.ORHughesFree`)                    |
|-------------------------------------|---------------------------------------------|
| `IsStarRegularRing R`               | `IsStarRegular R`                           |
| `VonNeumannRegular R`               | `VonNeumannRegularRing R`                   |
| `IsProperStar R` (right-handed)     | `IsProperStar R` (left-handed)              |
| `IsPositiveDefinite R`              | `IsPositiveDefiniteStarRegular R`           |
| `SylvesterRankFunction R`           | `SylvesterRank R`                           |
| `Group.LocallyIndicable G`          | `LocallyIndicable G`                        |

The name clash on `IsProperStar` and `IsVonNeumannRegular` is why every statement below is
qualified: the two definitions differ (right- vs. left-handed properness), and the equivalence
`Work.ORVonNeumann.isProperStar_iff_isProperStarLeft` is the (ring-theoretic) bridge.
-/
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORBridgeLinnell.Basic
import Submission.Work.ORBridgeLinnell.Countable
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.HughesFree
import Submission.Work.ORHughesFree.Instances
import Submission.Work.ORHughesFree.NaturalExtension.starRegular_subring_positiveDefinite
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORLocInd.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORDivLoc

open Work.ORHughesFree

/-! ## `∗`-regularity, von Neumann regularity, positive definiteness -/

/-- **N5 → N6**: `Work.ORVonNeumann.IsStarRegularRing` (von Neumann regular and a proper
involution, JZLA20's definition, right-handed properness) implies
`Work.ORHughesFree.IsStarRegular` (the same, left-handed properness).

The only content is the handedness: from `x * x⋆ = 0 → x = 0` derive `x⋆ * x = 0 → x = 0` by
applying the former to `x⋆`. -/
theorem isStarRegular_of_isStarRegularRing {R : Type*} [Ring R] [StarRing R]
    (h : Work.ORVonNeumann.IsStarRegularRing R) : IsStarRegular R where
  vonNeumannRegular := ⟨fun x => h.1 x⟩
  proper := fun x hx => by
    have hy : star x = 0 := h.2 (star x) (by simpa only [star_star] using hx)
    calc x = star (star x) := (star_star x).symm
      _ = star 0 := by rw [hy]
      _ = 0 := by simp

/-- **N5 → N6** for the structure map of the envelope: `U(G)` is `∗`-regular in the sense of the
JZLA20 engine.  Registered as an instance, so that the N6-vocabulary statements about `U(G)` can
be written without an explicit instance argument. -/
instance isStarRegular_envelope {G : Type v} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) : IsStarRegular E.U :=
  isStarRegular_of_isStarRegularRing E.starRegular

/-- **N5 → N6**: positive definiteness.  `Work.ORVonNeumann.IsPositiveDefinite R` is
`IsStarRegularRing R ∧ ∀ n, IsStarRegularRing (Mat n R)`, which is exactly
`Work.ORHughesFree.IsPositiveDefiniteStarRegular R` after the conversion
`isStarRegular_of_isStarRegularRing`. -/
theorem isPositiveDefiniteStarRegular_of_isPositiveDefinite {R : Type*} [Ring R] [StarRing R]
    (h : Work.ORVonNeumann.IsPositiveDefinite R) : IsPositiveDefiniteStarRegular R :=
  fun n => isStarRegular_of_isStarRegularRing (h.2 n)

/-- **N5 → N6** for the envelope: `U(G)` is positive definite in the sense of the JZLA20
engine. -/
theorem isPositiveDefiniteStarRegular_envelope {G : Type v} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) : IsPositiveDefiniteStarRegular E.U :=
  isPositiveDefiniteStarRegular_of_isPositiveDefinite E.posDef

/-- **N5 → N6**: `U(G)` is nontrivial (the faithful rank function separates `1` from `0`). -/
instance nontrivial_envelope {G : Type v} [Group G] (E : Work.ORVonNeumann.StarRegularEnvelope G) :
    Nontrivial E.U :=
  Work.ORBridgeLinnell.nontrivial_U E

/-- **The `∗`-regular closure `V = R(K[H], U(G))` is `∗`-regular**, being a `∗`-regular closure.
Registered as an instance so that the N6-vocabulary statements about `V` (in particular
`Work.ORHughesFree.IsHughesFreeEnv` and the induction environment `Work.ORHughesFree.Thm61Step`)
can be written without an explicit instance argument. -/
instance instIsStarRegularStarClosureOfSubgroup {G : Type v} [Group G] {K : Type u} [Field K]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) : IsStarRegular ↥(starClosureOfSubgroup E φK H) :=
  Work.ORHughesFree.instIsStarRegularStarRegularClosure
    (starSubringClosure (Set.range (Work.ORBridgeLinnell.toUK E φK H)))

/-- **N5 → N6** at the `∗`-regular closure: `V_H = R(K[H], U(G))` is positive definite, because
it is a `∗`-regular `∗`-subring of the positive definite ring `U(G)`
(`Work.ORHughesFree.NaturalExtension.starRegular_subring_positiveDefinite`).

This is the hypothesis `hpos` of the construction `thm61Step_nonempty` of the induction
environment. -/
theorem isPositiveDefiniteStarRegular_starClosure {G : Type} [Group G] {K : Type} [Field K]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) : IsPositiveDefiniteStarRegular ↥(starClosureOfSubgroup E φK H) := by
  haveI : IsStarRegular E.U := isStarRegular_envelope E
  exact Work.ORHughesFree.NaturalExtension.starRegular_subring_positiveDefinite
    (Subring.subtype (starClosureOfSubgroup E φK H).toSubring) Subtype.coe_injective
    (fun v => rfl) (isPositiveDefiniteStarRegular_envelope E)

/-! ## Local indicability -/

/-- **N5 → N6**: `Work.ORLocInd.Group.LocallyIndicable` (the form used by `DivLoc`) is
`Work.ORHughesFree.LocallyIndicable` (the form used by the JZLA20 engine) — the two definitions
are literally the same. -/
theorem locallyIndicable_of_orLocInd {G : Type v} [Group G]
    (h : Work.ORLocInd.Group.LocallyIndicable G) : LocallyIndicable G :=
  ⟨fun H hfg hne => h H hfg hne⟩

/-- N6 → N5 for local indicability (the same statement, read the other way). -/
theorem orLocInd_of_locallyIndicable {G : Type v} [Group G]
    (h : LocallyIndicable G) : Work.ORLocInd.Group.LocallyIndicable G :=
  fun H hfg hne => h.surj_z H hfg hne

end Work.ORDivLoc
