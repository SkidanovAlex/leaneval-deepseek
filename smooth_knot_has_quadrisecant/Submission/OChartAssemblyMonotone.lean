import Mathlib
import Submission.OChartGlue
import Submission.OChartAssembly
import Submission.OChartMonotone

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — the chain assembly: monotone
transport (composition of the local patches)

`OChartAssembly.lean` (S103) made the class-coordinate transport along a
chain well-defined (unique coordinate per class, transitions relabel
coordinates, cocycle, junction coherence over the S99 chains of
`OChartChain.lean`); `OChartGlue.lean` (S102) proved that every transition
parameter carries an open interval neighbourhood on which the coordinate
relabelling is strictly monotone (`OChartMonotoneNbhd`,
`exists_oChartMonotoneNbhd`).  This module starts the *monotonicity* half
of the chain assembly: it packages the monotone patches and their
composition, so that the transported coordinate along a chain is monotone
in the starting coordinate.

1. **the monotone-patch predicate** — `MonotoneOnPiece` (a real map on an
   open interval piece is strictly increasing or strictly decreasing) and
   its two suppliers: `monotoneOnPiece_of_inj_continuous` (the
   monotone-coordinate engine of S101 in predicate form) and
   `oChartMonotoneNbhd_piece_monotone` (the interval-piece transition map
   of an S102 monotone neighbourhood is `MonotoneOnPiece`);
2. **the composition engine** — `TransportStepDomain` (the parameters of
   the first piece whose transported coordinate lands in the second piece)
   and **`composite_monotone_direction`**: if two transport steps are each
   monotone in one direction, the composite is monotone in one direction
   on the step domain (four cases: the overall direction is the product of
   the two step directions) — the engine whose iteration along a chain
   gives the monotone transported coordinate;
3. **the S99-chain instances** —
   `oChart_chain_single_junction_transport_monotone` (at one junction of
   an S99 chain, a monotone neighbourhood makes the coordinate transport
   from `ch i` to `ch (i+1)` monotone on the piece) and
   `oChart_chain_two_junction_transport_monotone` (with monotone
   neighbourhoods at two consecutive junctions, the composite transport
   from `ch i` to `ch (i+2)` is monotone in one direction — the first
   induction step of the assembly).

The next slice (recorded in the ROADMAP session log) instantiates these
patches at the junctions of an `OChartChain.exists_oChart_chain_along_path`
chain, shrinks consecutive pieces so each transport lands in the next
patch (via the openness/continuity of the transitions), and iterates the
composition engine over the `Fin (N-1)` junctions — giving the monotone
transported coordinate from the first to the last chart of the chain, and
then the arc/circle classification of the components (brick (b) remainder).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- A real map on an open interval piece is **monotone in one direction**
(strictly increasing or strictly decreasing, in the sense of the real
coordinate order). -/
def MonotoneOnPiece {lo hi : ℝ} (f : ChartInterval lo hi → ℝ) : Prop :=
  (∀ x y : ChartInterval lo hi, (x : ℝ) < (y : ℝ) → f x < f y) ∨
  (∀ x y : ChartInterval lo hi, (x : ℝ) < (y : ℝ) → f y < f x)

/-- An injective continuous real map on an open interval is monotone in one
direction (the monotone-coordinate engine of S101 in this predicate form). -/
lemma monotoneOnPiece_of_inj_continuous {lo hi : ℝ} (f : ChartInterval lo hi → ℝ)
    (hfcont : Continuous f) (hfinj : Function.Injective f) : MonotoneOnPiece f :=
  interval_inj_continuous_monotone f hfcont hfinj

/-- The interval-piece transition map of a monotone neighbourhood (S102) is
monotone in one direction on its piece. -/
lemma oChartMonotoneNbhd_piece_monotone {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₁ ch₂) (nb : OChartMonotoneNbhd ch₁ ch₂ x₀) :
    MonotoneOnPiece (oChartTransitionOnInterval ch₁ ch₂ nb.subset nb.dom) := nb.monotone

/-- The domain of a composite transport step: parameters of the first piece
whose transported coordinate lies in the second piece. -/
def TransportStepDomain {a b : ℝ} (φ : ChartInterval a b → ℝ) (c d : ℝ) : Type :=
  {x : ChartInterval a b // φ x ∈ Set.Ioo c d}

/-- **Composition of two monotone pieces is monotone in one direction.**
If the transport step `φ` (into the second chart's coordinates) and the
next patch `ψ` are each monotone in one direction, then the composite
`ψ`-of-`φ` (defined on the parameters whose `φ`-value lies in the second
patch) is monotone in one direction: the transported coordinate at the end
of a two-step chain is monotone in the starting coordinate, with the
overall direction the product of the two step directions. -/
lemma composite_monotone_direction {a b c d : ℝ} {φ : ChartInterval a b → ℝ}
    (hφ : MonotoneOnPiece φ) {ψ : ChartInterval c d → ℝ} (hψ : MonotoneOnPiece ψ) :
    (∀ x₁ x₂ : TransportStepDomain φ c d, (x₁.1 : ℝ) < (x₂.1 : ℝ) →
        ψ ⟨φ x₁.1, x₁.2⟩ < ψ ⟨φ x₂.1, x₂.2⟩) ∨
    (∀ x₁ x₂ : TransportStepDomain φ c d, (x₁.1 : ℝ) < (x₂.1 : ℝ) →
        ψ ⟨φ x₂.1, x₂.2⟩ < ψ ⟨φ x₁.1, x₁.2⟩) := by
  rcases hφ with hφi | hφd <;> rcases hψ with hψi | hψd
  · left
    intro x₁ x₂ hxy
    have hφv : φ x₁.1 < φ x₂.1 := hφi x₁.1 x₂.1 hxy
    exact hψi ⟨φ x₁.1, x₁.2⟩ ⟨φ x₂.1, x₂.2⟩ hφv
  · right
    intro x₁ x₂ hxy
    have hφv : φ x₁.1 < φ x₂.1 := hφi x₁.1 x₂.1 hxy
    exact hψd ⟨φ x₁.1, x₁.2⟩ ⟨φ x₂.1, x₂.2⟩ hφv
  · right
    intro x₁ x₂ hxy
    have hφv : φ x₂.1 < φ x₁.1 := hφd x₁.1 x₂.1 hxy
    exact hψi ⟨φ x₂.1, x₂.2⟩ ⟨φ x₁.1, x₁.2⟩ hφv
  · left
    intro x₁ x₂ hxy
    have hφv : φ x₂.1 < φ x₁.1 := hφd x₁.1 x₂.1 hxy
    exact hψd ⟨φ x₂.1, x₂.2⟩ ⟨φ x₁.1, x₁.2⟩ hφv


/-- **The single-junction transport of an S99 chain is monotone.**  At a
junction of an `OChartChain.exists_oChart_chain_along_path` chain (charts
`ch i`, `ch (i+1)` sharing the boundary class), any monotone neighbourhood
of the transition at that junction (S102) makes the coordinate transport
from chart `i` to chart `i+1` monotone in one direction on the piece —
the local patch of the chain assembly applied to the S99 data. -/
lemma oChart_chain_single_junction_transport_monotone {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (_hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i))) (i : Fin N) (hi : i.1 + 1 < N)
    (x₀ : OChartTransitionDomain (ch i) (ch ⟨i.1 + 1, hi⟩))
    (nb : OChartMonotoneNbhd (ch i) (ch ⟨i.1 + 1, hi⟩) x₀) :
    MonotoneOnPiece
      (oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hi⟩) nb.subset nb.dom) :=
  oChartMonotoneNbhd_piece_monotone (ch i) (ch ⟨i.1 + 1, hi⟩) x₀ nb

/-- **Two-junction transport of an S99 chain is monotone.**  If monotone
neighbourhoods are fixed at two consecutive junctions (charts `ch i →
ch (i+1) → ch (i+2)`), and the second patch is applied to the parameters
whose first-patch transport lands in its piece, then the composite
transport from chart `i` to chart `i+2` is monotone in one direction — the
first induction step of the chain assembly (iteration of
`composite_monotone_direction`). -/
lemma oChart_chain_two_junction_transport_monotone {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (_hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i))) (i : Fin N)
    (hij : i.1 + 1 < N) (hjk : i.1 + 2 < N)
    (x₁ : OChartTransitionDomain (ch i) (ch ⟨i.1 + 1, hij⟩))
    (nb₁ : OChartMonotoneNbhd (ch i) (ch ⟨i.1 + 1, hij⟩) x₁)
    (x₂ : OChartTransitionDomain (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩))
    (nb₂ : OChartMonotoneNbhd (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩) x₂) :
    (∀ u v : TransportStepDomain
        (oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hij⟩) nb₁.subset nb₁.dom)
        nb₂.lo nb₂.hi,
      (u.1 : ℝ) < (v.1 : ℝ) →
        (oChartTransitionOnInterval (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩) nb₂.subset nb₂.dom)
            ⟨(oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hij⟩) nb₁.subset nb₁.dom) u.1, u.2⟩ <
          (oChartTransitionOnInterval (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩) nb₂.subset nb₂.dom)
            ⟨(oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hij⟩) nb₁.subset nb₁.dom) v.1, v.2⟩) ∨
    (∀ u v : TransportStepDomain
        (oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hij⟩) nb₁.subset nb₁.dom)
        nb₂.lo nb₂.hi,
      (u.1 : ℝ) < (v.1 : ℝ) →
        (oChartTransitionOnInterval (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩) nb₂.subset nb₂.dom)
            ⟨(oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hij⟩) nb₁.subset nb₁.dom) v.1, v.2⟩ <
          (oChartTransitionOnInterval (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩) nb₂.subset nb₂.dom)
            ⟨(oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hij⟩) nb₁.subset nb₁.dom) u.1, u.2⟩) := by
  exact composite_monotone_direction
    (oChartMonotoneNbhd_piece_monotone (ch i) (ch ⟨i.1 + 1, hij⟩) x₁ nb₁)
    (oChartMonotoneNbhd_piece_monotone (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩) x₂ nb₂)

end LeanEval.KnotTheory.Quadrisecant
