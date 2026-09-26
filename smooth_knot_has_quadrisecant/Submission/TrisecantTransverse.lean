import Mathlib
import ChallengeDeps
import Submission.CollinearityMap
import Submission.TrisecantCurve
import Submission.TorusCollinearity

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology RealInnerProductSpace

/-!
# Milestone-2 step (iii) — transverse general position for the trisecant
locus over `O` (dependency: the chart-local open-map lemma)

**The chart-local open-map lemma (statement).**  Let `c` be a 1-chart
(`ZeroSet1Chart`) at a point of the zero set whose base parameter `x₀` is
*strict* (the chart is centred at a strict data point `z₀`, i.e. at a point
of `O`), and let `J` be the strict open parameter neighbourhood of `x₀`
supplied by `zeroChordClass_injective_near_base` (`StrictZero.lean`), on
which the chord-class map `zeroChordClass` is injective.  The open-map half
of the local 1-manifold structure of `O` is the statement that the direct
image

    zeroChordClass h '' (chartLift c '' J)

is open in the trisecant set `trisecantSet r` (subspace of `OpenMobius`) —
equivalently, that `zeroChordClass` restricted to the strict data of the
chart is a local homeomorphism onto its image in `O`, so that the
1-manifold charts of `O` can be assembled from the `ZeroSet1Chart`s.

**Why the rank-two general position alone is insufficient (S83 analysis).**
The rank-two hypothesis `TrisecantGeneralPosition` (`PartialRankTwo` of the
collinearity map) does *not* exclude the following degeneration: a sequence
of strict data points `(aₙ, bₙ, mₙ)` whose chord classes tend to the class
`c₀ = {a₀, b₀}` while the middle parameters `mₙ` tend to the *endpoint*
`a₀`.  Such a sequence would make the classes `cₙ` lie outside the local
sheet image `zeroChordClass '' (chartLift c '' J)` (whose middles stay near
`m₀`), so that image would not be open in `O`.  A direct normalised-limit
argument shows that `mₙ → a₀` forces the chord direction `K(a₀) − K(b₀)` to
be parallel to the tangent `velocity a₀` at the endpoint — a configuration
*consistent* with rank two (only the `∂a` partial vanishes there), hence
present in some smooth knots.  Kuperberg's general position (the `π_L`
conditions) excludes exactly such tangencies; formally they are added here
as the *transverse* strengthening:

* **`EndpointTangentsOffChord`** — at the collinear triple `(a,b,m)`, no
  chord direction (through any two of the three points) is parallel to the
  tangent at either of its two endpoints (six cross products nonzero);
* **`TrisecantGeneralPositionTransverse`** — `TrisecantGeneralPosition` plus
  `EndpointTangentsOffChord`;
* **`TorusGeneralPositionTransverse`** — the torus-level form (every
  collinear off-diagonal torus triple has fundamental-domain
  representatives in transverse general position), exactly mirroring
  `TorusGeneralPosition`; monotone in it (`torusTransverse_monotone`).

With this strengthening, the endpoint-escape lemma (no strict-class
sequence with middles running to a chord endpoint — the geometric content
of the open map) is the next dependency, and then the open-map lemma above
is proved by the canonical-section argument: near a transverse strict class
`c₀ ∈ O`, every class of `O` in a neighbourhood has a unique strict
representative with chord near `(a₀,b₀)` and a continuous middle (so the
local inverse of the class map exists and the image is open).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-! ## 1. Endpoint-tangent transversality at a real collinear triple -/

/-- **No chord direction is tangent at one of its own endpoints.**  At the
real triple `(a, b, m)` (the knot values `r a, r b, r m`), each of the three
chord directions (through two of the points) is not parallel to the velocity
at either of its two endpoints: the six cross products
`(r x − r y) × velocity x` are nonzero.  This is the transversality that
prevents strict-data middles from running to a chord endpoint (which would
break the local open-map structure of `O`). -/
def EndpointTangentsOffChord (r : ℝ → Space) (a b m : ℝ) : Prop :=
  cross3 (r a - r b) (velocity r a) ≠ 0 ∧
  cross3 (r a - r b) (velocity r b) ≠ 0 ∧
  cross3 (r a - r m) (velocity r a) ≠ 0 ∧
  cross3 (r a - r m) (velocity r m) ≠ 0 ∧
  cross3 (r b - r m) (velocity r b) ≠ 0 ∧
  cross3 (r b - r m) (velocity r m) ≠ 0

/-- Endpoint tangents off the chord for the pair `(a,b)` with middle `m`:
the chord direction `r a − r b` is parallel to neither tangent.  (The two
conditions that matter for the class of the chord `{a,b}`.) -/
def ChordOffEndpointTangents (r : ℝ → Space) (a b : ℝ) : Prop :=
  cross3 (r a - r b) (velocity r a) ≠ 0 ∧ cross3 (r a - r b) (velocity r b) ≠ 0

/-- The chord-tangent condition for the pair `(a,b)` follows from the full
endpoint-tangent condition at the triple. -/
lemma EndpointTangentsOffChord.chord_off {r : ℝ → Space} {a b m : ℝ}
    (h : EndpointTangentsOffChord r a b m) : ChordOffEndpointTangents r a b := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2⟩

/-- The endpoint-tangent condition is invariant under translating the first
parameter by a period (the knot and its velocity are periodic). -/
lemma EndpointTangentsOffChord.period_shift_left {r : ℝ → Space} (h : IsSmoothKnot r)
    {a b m : ℝ} (ht : EndpointTangentsOffChord r a b m) :
    EndpointTangentsOffChord r (a + period) b m := by
  rcases ht with ⟨h1, h2, h3, h4, h5, h6⟩
  have hra : r (a + period) = r a := h.periodic a
  have hva : velocity r (a + period) = velocity r a := h.velocity_periodic a
  exact ⟨by simpa [hra, hva] using h1, by simpa [hra] using h2,
    by simpa [hra, hva] using h3, by simpa [hra] using h4, h5, h6⟩

/-- Invariance under translating the second parameter by a period. -/
lemma EndpointTangentsOffChord.period_shift_right {r : ℝ → Space} (h : IsSmoothKnot r)
    {a b m : ℝ} (ht : EndpointTangentsOffChord r a b m) :
    EndpointTangentsOffChord r a (b + period) m := by
  rcases ht with ⟨h1, h2, h3, h4, h5, h6⟩
  have hrb : r (b + period) = r b := h.periodic b
  have hvb : velocity r (b + period) = velocity r b := h.velocity_periodic b
  exact ⟨by simpa [hrb] using h1, by simpa [hrb, hvb] using h2,
    h3, h4, by simpa [hrb, hvb] using h5, by simpa [hrb] using h6⟩

/-- Invariance under translating the middle parameter by a period. -/
lemma EndpointTangentsOffChord.period_shift_middle {r : ℝ → Space} (h : IsSmoothKnot r)
    {a b m : ℝ} (ht : EndpointTangentsOffChord r a b m) :
    EndpointTangentsOffChord r a b (m + period) := by
  rcases ht with ⟨h1, h2, h3, h4, h5, h6⟩
  have hrm : r (m + period) = r m := h.periodic m
  have hvm : velocity r (m + period) = velocity r m := h.velocity_periodic m
  exact ⟨h1, h2, by simpa [hrm] using h3, by simpa [hrm, hvm] using h4,
    by simpa [hrm] using h5, by simpa [hrm, hvm] using h6⟩

/-! ## 2. Transverse general position at a triple and on the torus -/

/-- **Transverse general position at a collinear triple**: the rank-two
condition of `TrisecantGeneralPosition` plus the endpoint-tangent
transversality `EndpointTangentsOffChord`.  This is the strengthened
genericity under which the strict trisecant locus `O` is a genuine embedded
1-manifold (no middle-to-endpoint degeneration near a class of `O`). -/
def TrisecantGeneralPositionTransverse (r : ℝ → Space) (a b m : ℝ) : Prop :=
  TrisecantGeneralPosition r a b m ∧ EndpointTangentsOffChord r a b m

/-- Transverse general position implies the (rank-two) general position. -/
lemma TrisecantGeneralPositionTransverse.imp_generalPosition {r : ℝ → Space}
    {a b m : ℝ} (h : TrisecantGeneralPositionTransverse r a b m) :
    TrisecantGeneralPosition r a b m := h.1

/-- **Torus-level transverse general position**: every collinear
off-diagonal torus triple has fundamental-domain representatives in
transverse general position (mirrors `TorusGeneralPosition`, adding
`EndpointTangentsOffChord`). -/
def TorusGeneralPositionTransverse (r : ℝ → Space) : Prop :=
  ∀ p : KnotParamTriple, torusCollinearity r p = 0 → p ∈ TorusOffDiag r →
    ∃ a b m : ℝ, a ∈ Set.Ico 0 period ∧ b ∈ Set.Ico 0 period ∧ m ∈ Set.Ico 0 period ∧
      (a : KnotParam) = p.1 ∧ (b : KnotParam) = p.2.1 ∧ (m : KnotParam) = p.2.2 ∧
      TrisecantGeneralPositionTransverse r a b m

/-- Torus transverse general position implies the (rank-two) torus general
position — every chart/atlas/local-curve theorem proved under
`TorusGeneralPosition` applies under the strengthened hypothesis. -/
theorem torusTransverse_monotone {r : ℝ → Space} (h : TorusGeneralPositionTransverse r) :
    TorusGeneralPosition r := by
  intro p hpZ hpOff
  rcases h p hpZ hpOff with ⟨a, b, m, ha, hb, hm, hpa, hpb, hpm, hGP⟩
  exact ⟨a, b, m, ha, hb, hm, hpa, hpb, hpm, hGP.1⟩

end LeanEval.KnotTheory.Quadrisecant
