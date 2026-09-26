import Mathlib
import Submission.OChartAssemblyMonotone

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — finite-chain gluing: the two-step
composite of aligned monotone patches (second subgoal of the
interval-chain exhaustion)

`OChartFiniteGluing.lean` (S109) packaged the single-patch gluing
identification (`oChart_piece_embedding`: `MonotoneOnPiece`, injective,
continuous, coordinate-agreement).  This module adds the atomic *two-step*
composite that a finite chain of overlapping patches iterates:

1. **`MonotoneDirectionOn`** — a real-valued function on a domain with a
   real coordinate is monotone in one direction with respect to the
   coordinate (strictly increasing or strictly decreasing); with an
   injective coordinate it is injective (`MonotoneDirectionOn.injective`);
2. **`transportStepDomain_coord_injective`** — the real coordinate of a
   step-domain element (its first-piece parameter) is injective;
3. **`oChartTwoStepMap`** — the composite transport over two aligned
   monotone pieces, defined on the step domain (first-piece parameters
   whose transport lands in the second piece);
4. **`oChart_two_step_composite`** — the two-step composite is monotone in
   one direction and injective on its step domain (the S104 composition
   engine `composite_monotone_direction` on the two `MonotoneOnPiece`
   maps, plus `MonotoneDirectionOn.injective`).

The `Fin`-indexed chain iteration of this two-step composite (with
`OChartMonotoneNbhd` data along an S99 path chain) is the next subgoal of
the interval-chain exhaustion.  Everything here is elementary and verified
(no axioms, no `sorry`).
-/

/-- A real-valued function on a domain with a real coordinate is
**monotone in one direction with respect to the coordinate** (strictly
increasing or strictly decreasing). -/
def MonotoneDirectionOn {D : Type*} (c : D → ℝ) (f : D → ℝ) : Prop :=
  (∀ a b : D, c a < c b → f a < f b) ∨ (∀ a b : D, c a < c b → f b < f a)

/-- A monotone-in-one-direction function with an injective coordinate is
injective. -/
lemma MonotoneDirectionOn.injective {D : Type*} {c : D → ℝ} {f : D → ℝ}
    (hf : MonotoneDirectionOn c f) (hc : Function.Injective c) : Function.Injective f := by
  rcases hf with hfi | hfd
  · intro a b hab
    by_contra hne
    have hcne : c a ≠ c b := by intro h; exact hne (hc h)
    have hlt : c a < c b ∨ c b < c a := lt_or_gt_of_ne hcne
    rcases hlt with hlt1 | hlt2
    · have : f a < f b := hfi a b hlt1
      exact (ne_of_lt this) hab
    · have : f b < f a := hfi b a hlt2
      exact (ne_of_lt this) hab.symm
  · intro a b hab
    by_contra hne
    have hcne : c a ≠ c b := by intro h; exact hne (hc h)
    have hlt : c a < c b ∨ c b < c a := lt_or_gt_of_ne hcne
    rcases hlt with hlt1 | hlt2
    · have : f b < f a := hfd a b hlt1
      exact (ne_of_lt this) hab.symm
    · have : f a < f b := hfd b a hlt2
      exact (ne_of_lt this) hab

/-- The real coordinate of a step-domain element (its first-piece
parameter) is injective. -/
lemma transportStepDomain_coord_injective {a b : ℝ} (φ : ChartInterval a b → ℝ) (c d : ℝ) :
    Function.Injective (fun u : TransportStepDomain φ c d => (u.1 : ℝ)) := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- The composite transport map over two aligned monotone pieces (defined
on the step domain: first-piece parameters whose transport lands in the
second piece). -/
noncomputable def oChartTwoStepMap {r : ℝ → Space} {c₀ c₁ c₂ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) (ch₃ : OSub1Chart r c₂)
    (x₁ : OChartTransitionDomain ch₁ ch₂) (x₂ : OChartTransitionDomain ch₂ ch₃)
    (nb₁ : OChartMonotoneNbhd ch₁ ch₂ x₁) (nb₂ : OChartMonotoneNbhd ch₂ ch₃ x₂) :
    TransportStepDomain (oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom)
      nb₂.lo nb₂.hi → ℝ := fun u =>
  oChartTransitionOnInterval ch₂ ch₃ nb₂.subset nb₂.dom
    ⟨oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom u.1, u.2⟩

/-- **The two-step composite is monotone in one direction and injective on
its step domain.**  With monotone neighbourhoods at two overlapping
transitions (`ch₁ → ch₂`, `ch₂ → ch₃`, S102) and the second patch applied
to the parameters whose first transport lands in its piece, the composite
transport of the coordinate (`oChartTwoStepMap`) is monotone in one
direction with respect to the starting coordinate (the S104 composition
engine `composite_monotone_direction` on the two `MonotoneOnPiece` maps)
and injective (`MonotoneDirectionOn.injective`; the starting coordinate
is injective on the step domain).  This is the atomic two-step lemma of
the finite-chain iterated transport. -/
theorem oChart_two_step_composite {r : ℝ → Space} {c₀ c₁ c₂ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) (ch₃ : OSub1Chart r c₂)
    (x₁ : OChartTransitionDomain ch₁ ch₂) (x₂ : OChartTransitionDomain ch₂ ch₃)
    (nb₁ : OChartMonotoneNbhd ch₁ ch₂ x₁) (nb₂ : OChartMonotoneNbhd ch₂ ch₃ x₂) :
    MonotoneDirectionOn
      (fun u : TransportStepDomain (oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom)
          nb₂.lo nb₂.hi => (u.1 : ℝ))
      (oChartTwoStepMap ch₁ ch₂ ch₃ x₁ x₂ nb₁ nb₂) ∧
    Function.Injective (oChartTwoStepMap ch₁ ch₂ ch₃ x₁ x₂ nb₁ nb₂) := by
  constructor
  · exact composite_monotone_direction
      (oChartMonotoneNbhd_piece_monotone ch₁ ch₂ x₁ nb₁)
      (oChartMonotoneNbhd_piece_monotone ch₂ ch₃ x₂ nb₂)
  · have hdir : MonotoneDirectionOn
      (fun u : TransportStepDomain (oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom)
          nb₂.lo nb₂.hi => (u.1 : ℝ))
      (oChartTwoStepMap ch₁ ch₂ ch₃ x₁ x₂ nb₁ nb₂) := by
      exact composite_monotone_direction
        (oChartMonotoneNbhd_piece_monotone ch₁ ch₂ x₁ nb₁)
        (oChartMonotoneNbhd_piece_monotone ch₂ ch₃ x₂ nb₂)
    exact MonotoneDirectionOn.injective hdir
      (transportStepDomain_coord_injective
        (oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom) nb₂.lo nb₂.hi)

end LeanEval.KnotTheory.Quadrisecant
