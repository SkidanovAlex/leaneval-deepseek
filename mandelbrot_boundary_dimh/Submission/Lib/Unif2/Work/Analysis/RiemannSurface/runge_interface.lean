import Mathlib
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.runge_exhaustion
import Submission.Lib.Unif2.Holomorphic

/-!
# The interfaces isolating the Behnke--Stein approximation input for the divisor chapter

The divisor statement `Work.Analysis.RiemannSurface.single_simple_zero_at` is the Weierstrass/Cousin
theorem for an open Riemann surface: *every divisor on a non-compact connected Riemann surface is
principal*.  Classically it is proved from the approximation theory of Behnke--Stein (Forster,
*Lectures on Riemann Surfaces*, chapters 26--30):

1. **Behnke--Stein approximation** (the "Runge theorem" on a surface): a function holomorphic on a
   neighbourhood of a compact set `D` is uniformly approximable on `D` by functions holomorphic on a
   prescribed (larger) domain `E`, *provided* `D` has no "relatively compact hole" in `E`;
2. the Mittag--Leffler/bookkeeping step that turns the approximation into the divisor datum
   (`singleSimpleZero_of_singleSimplePole`, `singleSimpleZero_of_poleData`, in `DivisorBasics.lean`).

This file only *states* the approximation inputs as `Prop`s, so that they can be used as explicit
hypotheses while the approximation theorem itself is developed (see
`runge_meromorphic.lean` for the reduction of the target to the input stated here).

## The two traps this file is designed to avoid

Both cost a session to find; see `NOTES_divisor_chapter_plan.md` sections 19.1, 19.2, 22 and 24.

* **Vacuity.**  If the datum `f` is required to be holomorphic on the *same* domain on which the
  approximant `F` is required to be holomorphic (or on all of `X`), the statement is *trivially*
  true with `F := f`.  The datum must therefore be assumed holomorphic only on an open set `W ⊇ D`,
  with `F` holomorphic on the *strictly larger* domain `E` (`RungePairApproximation`).
* **The wrong no-hole clause (corrected in this file).**  The correct Runge condition on the pair
  `(D, E)` is that the components of `E ∖ D` are *not relatively compact in `E`* (Rudin, *Real and
  Complex Analysis*, Thm. 13.11: every component of `E* ∖ D` contains a point of `E* ∖ E`).  It is
  *not* the statement that their closures in `X` are non-compact.  The two differ already in the
  plane: for `X = ℂ`, `E = {|z| < 2}`, `D = {|z| ≤ 1}` the annulus `E ∖ D` has *compact* closure in
  `X = ℂ`, so the naive condition fails, while the approximation it is meant to license is of course
  true (Taylor expansion at the centre).  The naive condition is strictly stronger than the truth,
  which is why it cannot be instantiated on the pieces of a Runge exhaustion (there `E = D (n+1)`
  and `D = closure (D n)` always have `E ∖ D` with compact closure in `X`).  The correct clause,
  `NotRelCompactComponents E D` below, is what the exhaustion actually satisfies.

Both interfaces below are stated with the *corrected* hole clause.  They are *not* the form in which
the target is consumed: that is `MeromorphicRunge` in `runge_meromorphic.lean`, whose conclusion is
zero-free, which is what makes the Mittag--Leffler induction preserve zero-freeness (see
`NOTES_divisor_chapter_plan.md` §24).
-/

open Set
open scoped Topology Manifold

noncomputable section

open Classical

namespace Work.Analysis.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The Runge hole condition.**  No connected component of the open set `E ∖ D` is contained in a
compact subset of `E`; equivalently (Rudin 13.11) every component of `E* ∖ D` meets `E* ∖ E`.

This is the *correct* form of the condition.  The obvious alternative — that the closure in `X` of
each component is non-compact — is *stronger* than the truth and is not satisfiable on the pieces of
a Runge exhaustion. -/
def NotRelCompactComponents (E D : Set X) : Prop :=
  ∀ x ∈ E \ D, ¬ ∃ K : Set X, IsCompact K ∧ K ⊆ E ∧ connectedComponentIn (E \ D) x ⊆ K

/-- **The Behnke--Stein (Runge) approximation property of a Riemann surface**, in the form in which
the divisor chapter consumes it.

`D` is a compact set, `E ⊇ W ⊇ D` are open, `f` is holomorphic on `W`, and the conclusion is a
function `F` holomorphic on `E` with `‖F - f‖ < ε` on `D`.  The side condition says that `D` has no
relatively compact hole inside `E` (`NotRelCompactComponents`); with an *empty* side condition the
statement is false (`X = ℂ`, `D = S¹`, `f = 1/z`: `1/z` is holomorphic on the annulus
`{1/2 < |z| < 2} ⊇ S¹` but is not approximable on `S¹` by entire functions). -/
def RungePairApproximation (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (D E W : Set X), IsCompact D → IsOpen E → IsOpen W → D ⊆ W → W ⊆ E →
    NotRelCompactComponents E D →
    ∀ f : X → ℂ, (∀ x ∈ W, Submission.HolomorphicOnXAt f x) → ∀ ε : ℝ, 0 < ε →
      ∃ F : X → ℂ, (∀ x ∈ E, Submission.HolomorphicOnXAt F x) ∧
        ∀ x ∈ D, ‖F x - f x‖ < ε

/-- **The approximation property on the punctured surface** `V := X ∖ {x₀}`, a corollary of the
pair version with `E := V`.  Kept for reference: the subdivision of `D` into a *near* piece (an
annulus around `x₀`) and a *far* piece is *not* approximable on the union (`NOTES_…` §22.5), so the
induction does **not** run through this statement.

`D ⊆ V` is compact, `W ⊇ D` is open with `W ⊆ V`, `f` is holomorphic on `W`, and the conclusion is
`F` holomorphic on all of `V` with `‖F - f‖ < ε` on `D`.  The side condition is the hull condition
in `V`: no component of `V ∖ D` is relatively compact in `V`. -/
def PuncturedGlobalApproximation {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x₀ : X) : Prop :=
  ∀ (D W : Set X), IsCompact D → IsOpen W → x₀ ∉ D → D ⊆ W → W ⊆ Set.univ \ {x₀} →
    NotRelCompactComponents (Set.univ \ {x₀}) D →
    ∀ f : X → ℂ, (∀ x ∈ W, Submission.HolomorphicOnXAt f x) → ∀ ε : ℝ, 0 < ε →
      ∃ F : X → ℂ, Submission.HolomorphicOnX F (Set.univ \ {x₀}) ∧
        ∀ x ∈ D, ‖F x - f x‖ < ε

end Work.Analysis.RiemannSurface
