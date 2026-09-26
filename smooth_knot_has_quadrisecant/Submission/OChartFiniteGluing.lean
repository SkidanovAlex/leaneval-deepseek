import Mathlib
import Submission.OChartChainJunction
import Submission.OChartExhaustion
import Submission.OChartAssemblyMonotone

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — finite-family gluing: the local
embedding of interval pieces (first subgoal of the interval-chain
exhaustion)

The interval-chain exhaustion draft (ROADMAP S107) builds from each
exhaustion step `Eₙ = (⋃_{m<n} trace(cl m)) ∩ C` an interval-charted open
set `Uₙ ⊇ Eₙ` by gluing chart traces with the transition homeomorphisms
(S98) and orientation data (S104).  The honest S106/S107 scoping notes
record that such gluing is only well-posed for *chains of genuinely
overlapping* interval pieces with orientation/alignment data — an
arbitrary enumeration `cl` need not give consecutive overlaps, and
disconnected overlaps (circle-like wrapping) change the glued shape.  This
module starts the gluing slice with the true local core that every
interval-chain gluing step uses:

1. **`MonotoneOnPiece.injective`** — a map monotone in one direction on an
   open interval piece is injective (strictly increasing or strictly
   decreasing; by contradiction from the trichotomy of real order);
2. **`oChart_piece_embedding`** — the local gluing identification: on the
   interval piece of an S102 monotone neighbourhood, the coordinate
   transport from `ch₁` to `ch₂` is `MonotoneOnPiece`, injective,
   continuous, and its values are the `ch₂`-coordinates of the same
   classes as the `ch₁`-parameters (S102 `OChartMonotoneNbhd`, S103
   `oChartNbhd_piece_coordinate`, S104 engine, packaged as one lemma).

**The finite-family gluing statement of the draft** (to be assembled from
`oChart_piece_embedding` once the chain/ordering data are fixed; recorded
in the ROADMAP session log S109): given a finite chain of interval pieces
`(φᵢ : pieceᵢ → ℝ)` over consecutive overlaps with alignment
(`φᵢ(pieceᵢ) ⊆ pieceᵢ₊₁` on the step domain, obtained by the S106 shrink)
and orientation data, the iterated transport is a well-defined monotone
injective coordinate over the chain; gluing all pieces of a chain into one
interval requires additionally that the overlaps are connected (no
circle-like wrapping), which is where the compact/non-compact dichotomy of
the component enters.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- A map that is monotone in one direction on an open interval piece is
injective (strictly increasing or strictly decreasing). -/
lemma MonotoneOnPiece.injective {lo hi : ℝ} {f : ChartInterval lo hi → ℝ}
    (hf : MonotoneOnPiece f) : Function.Injective f := by
  rcases hf with hfi | hfd
  · intro x y hxy
    by_contra hne
    have hlt : (x : ℝ) < (y : ℝ) ∨ (y : ℝ) < (x : ℝ) :=
      lt_or_gt_of_ne (by intro h; exact hne (Subtype.ext h))
    rcases hlt with hxylt | hyxlt
    · have : f x < f y := hfi x y hxylt
      exact (ne_of_lt this) hxy
    · have : f y < f x := hfi y x hyxlt
      exact (ne_of_lt this) hxy.symm
  · intro x y hxy
    by_contra hne
    have hlt : (x : ℝ) < (y : ℝ) ∨ (y : ℝ) < (x : ℝ) :=
      lt_or_gt_of_ne (by intro h; exact hne (Subtype.ext h))
    rcases hlt with hxylt | hyxlt
    · have : f y < f x := hfd x y hxylt
      exact (ne_of_lt this) hxy.symm
    · have : f x < f y := hfd y x hyxlt
      exact (ne_of_lt this) hxy

/-- **The S102 patch is a local embedding of interval pieces.**  On the
interval piece of a monotone neighbourhood of a transition, the coordinate
transport from `ch₁` to `ch₂` is injective (strict monotone), continuous,
and its values are the `ch₂`-coordinates of the same classes as the
`ch₁`-parameters — the local gluing identification of the two chart
traces, packaged from S102 (`OChartMonotoneNbhd`), S103 (class
coordinates) and S104 (`MonotoneOnPiece`). -/
lemma oChart_piece_embedding {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₁ ch₂) (nb : OChartMonotoneNbhd ch₁ ch₂ x₀) :
    let φ : ChartInterval nb.lo nb.hi → ℝ := oChartTransitionOnInterval ch₁ ch₂ nb.subset nb.dom
    MonotoneOnPiece φ ∧ Function.Injective φ ∧ Continuous φ ∧
      (∀ a : ChartInterval nb.lo nb.hi,
        ∃ y : OChartTransitionDomain ch₂ ch₁,
          oChartLift ch₂ (((y : OChartTransitionDomain ch₂ ch₁) :
              ChartInterval ch₂.lo ch₂.hi)) =
            oChartLift ch₁ (⟨(a : ℝ), nb.subset a.2⟩ : ChartInterval ch₁.lo ch₁.hi) ∧
          (((y : OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi) : ℝ) = φ a) := by
  intro φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nb.monotone
  · exact MonotoneOnPiece.injective nb.monotone
  · exact continuous_oChartTransitionOnInterval ch₁ ch₂ nb.subset nb.dom
  · intro a
    exact oChartNbhd_piece_coordinate ch₁ ch₂ x₀ nb a

end LeanEval.KnotTheory.Quadrisecant
