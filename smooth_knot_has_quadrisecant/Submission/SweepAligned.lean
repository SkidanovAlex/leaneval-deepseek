import Mathlib
import Submission.IntervalCoverU
import Submission.ChainAlignment

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S188 — the walk-aligned sub-pieces (the O-side interlock instantiated
in the ChainTransport representation; module Submission/SweepAligned.lean)

The S187 correction fixed where the sweep's interlock lives: NOT in the
raw S185 cells (image of `C m` under the cell transport need not lie in
`C (m+1)` — distinct junction classes), but in the ALIGNED SUB-PIECE
construction `ChainAlignment.exists_aligned_subpieces` (S133): given a
chain of junction `MonoPiece`s and a start parameter with a forward
orbit, backward shrinking produces sub-pieces over which EVERY parameter
transports forward (`AlignedTotality`).  This module INSTANTIATES that
construction on the WALK junction-piece chain in the ChainTransport
representation (the one the sweep's transport machinery actually uses):

1. `chainTail_mem_index` — membership in a `chainTail p k n` tail is an
   index `k < m ≤ k+n` with `q = p m` (pure list arithmetic over the
   `chainTail` recursion);
2. `continuous_walkJunctionPiece_τ` — every walk junction piece has a
   continuous coordinate map (its `τ` is the interval-piece transition of
   the walk junction neighbourhood, continuous by S98
   `continuous_oChartTransitionOnInterval`);
3. **`walk_aligned_subpieces`** — the instantiation: with walk data `h
   hqf hgp cl e hoverlap`, chain `p 0 :: chainTail p 0 n`
   (`p m := walkJunctionPiece … m`), and a start parameter `x₀` of the
   first piece with a forward orbit (`htr : transports p 0 (chainTail p
   0 n) x₀` — the walk-geometric orbit input supplied by the S135
   orbit/`htr` machinery), there exist aligned sub-pieces `sp :: qs`
   (`sp` a sub-piece of `p 0` containing `x₀`; the `qs` sub-pieces of
   the successive walk pieces) with `AlignedTotality (sp :: qs)`: every
   parameter of `sp` transports through the whole chain — the true
   junction-level interlock.

With `AlignedTotality (sp :: qs)` in hand, the sweep's next steps are
bookkeeping in the ChainTransport representation: the domain
`ChainDomain (sp :: qs) = {x : ChartInterval sp.lo sp.hi // transports sp
qs x}` is ALL of `sp` (every parameter transports), so
`chain_prefix_transport_summary` (S119) applies to every start parameter
of `sp`, giving the monotone injective coordinate whose value is the
`ch (n+1)`-coordinate of the same class; assembling these into the
interval-charted `Uₙ` (the S147-T target) is the next slice.  The `htr`
orbit hypothesis is the single remaining geometric input (S135 machinery
constructs such orbits for the configurations the exhaustion uses).
Everything here is verified (no axioms, no `sorry`).
-/
/-- Membership in a `chainTail p k n` tail: an element is the piece
`p m` for a walk index `k < m ≤ k+n`. -/
lemma chainTail_mem_index (p : ℕ → MonoPiece) (k n : ℕ) {q : MonoPiece} :
    q ∈ chainTail p k n → ∃ m : ℕ, k < m ∧ m ≤ k + n ∧ q = p m := by
  intro hq
  induction n generalizing k with
  | zero =>
      -- chainTail p k 0 = []
      have hmem' : q ∈ ([] : List MonoPiece) := by simpa [chainTail] using hq
      exact False.elim ((List.not_mem_nil (a := q)) hmem')
  | succ n ih =>
      have hmem : q ∈ p (k + 1) :: chainTail p (k + 1) n := by
        simpa [chainTail] using hq
      rcases List.mem_cons.mp hmem with h | h
      · refine ⟨k + 1, by omega, by omega, h⟩
      · rcases ih (k + 1) h with ⟨m, hm1, hm2, hm3⟩
        refine ⟨m, by omega, by omega, hm3⟩

/-- The coordinate map of every walk junction piece is continuous (the
`τ` of `walkJunctionPiece i` is the interval-piece transition of the
walk junction neighbourhood, continuous by S98). -/
lemma continuous_walkJunctionPiece_τ {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (i : ℕ) : Continuous (walkJunctionPiece h hqf hgp cl e hoverlap i).τ := by
  change Continuous (oChartTransitionOnInterval
      (walkChart h hqf hgp cl e i) (walkChart h hqf hgp cl e (i + 1))
      (walkJunctionNbhd h hqf hgp cl e hoverlap i).subset
      (walkJunctionNbhd h hqf hgp cl e hoverlap i).dom)
  exact continuous_oChartTransitionOnInterval _ _ _ _



/-- **S188 — the walk-aligned sub-pieces (the O-side interlock in the
correct representation).**  Instantiation of the backward-aligned
sub-piece theorem (`ChainAlignment.exists_aligned_subpieces`, S133) on
the WALK junction-piece chain: the pieces
`p m := walkJunctionPiece … m` (`ch m → ch (m+1)` monotone cell
transports, continuous by `continuous_walkJunctionPiece_τ`), chain
`p 0 :: chainTail p 0 n`.  Given a start parameter `x₀` of the first
piece with a forward orbit through the chain (`htr :
transports p 0 (chainTail p 0 n) x₀` — the walk-geometric orbit input,
supplied by the S135 orbit/htr machinery), there are aligned sub-pieces
`sp :: qs` (`sp` a sub-piece of `p 0` containing `x₀`, the `qs`
sub-pieces of the successive walk pieces) over which EVERY parameter
transports forward (`AlignedTotality`): the true junction-level interlock
of the sweep (the raw S185 cells do NOT interlock — S187 correction). -/
theorem walk_aligned_subpieces {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
        (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
        (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ sp : MonoPiece, ∃ qs : List MonoPiece,
      IsSubPiece sp (walkJunctionPiece h hqf hgp cl e hoverlap 0) ∧
      ((x₀ : ℝ) ∈ Set.Ioo sp.lo sp.hi) ∧
      AlignedTotality (sp :: qs) ∧
      List.Forall₂ IsSubPiece qs (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) := by
  let p : ℕ → MonoPiece := walkJunctionPiece h hqf hgp cl e hoverlap
  have hcont : ∀ q : MonoPiece, q ∈ (p 0 :: chainTail p 0 n) → Continuous q.τ := by
    intro q hq
    rcases List.mem_cons.mp hq with hq0 | hqt
    · rw [hq0]
      exact continuous_walkJunctionPiece_τ h hqf hgp cl e hoverlap 0
    · rcases chainTail_mem_index p 0 n hqt with ⟨m, hm1, hm2, hm3⟩
      rw [hm3]
      exact continuous_walkJunctionPiece_τ h hqf hgp cl e hoverlap m
  rcases (exists_aligned_subpieces (chainTail p 0 n) (p 0) hcont x₀ htr) with
    ⟨sp, qs, hsubp, hx₀, htot, hfor₂⟩
  refine ⟨sp, qs, ?_, ?_, htot, hfor₂⟩
  · -- IsSubPiece sp (p 0): from hsubp's ∃hsub form
    rcases hsubp with ⟨hsub, hsp⟩
    exact ⟨hsub, hsp⟩
  · exact hx₀
end LeanEval.KnotTheory.Quadrisecant
