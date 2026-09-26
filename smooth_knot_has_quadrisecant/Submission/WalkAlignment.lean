import Mathlib
import Submission.ChainAlignment
import Submission.IntervalCoverU

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

/-!
# Milestone-2 (iv) step 6, brick (b) — walk-prefix alignment: the
shrinking slice instantiated on the S115 component walk (lemmas 1–3 of
the alignment construction, at the walk level)

`ChainAlignment.lean` (S121) proved the pure piece-level shrinking
machinery: `exists_subpiece_landing` (single-step: a continuous piece map
that sends a parameter into the next piece's interval sends a whole
sub-piece around it there) and `exists_aligned_subpieces` (backward
alignment: an orbit through a piece chain extends to sub-pieces with
`AlignedTotality` — every transport lands forward).  This module is the
WALK INSTANTIATION of that machinery: the S115/S120 walk data (charts
`walkChart` at the walk classes, junction pieces `walkJunctionPiece` with
the `walkJunction_subset`/`walkJunction_semantics` bridge of S120) supply
the hypotheses of the alignment theorems:

1. **`walkJunctionPiece_continuous`** — the coordinate map of a walk
   junction piece is continuous (the S102 continuity of the
   interval-piece transition map, read at the piece level): this is the
   `hcont` hypothesis of the alignment machinery (MonoPiece does not
   carry continuity, so it is supplied here from the chart transition);
2. **`chainTail_mem_iff`** / **`chainTail_continuous`** — membership in a
   tail chain (`chainTail p k n`, the elements `p (k+j+1)`, `j < n`) and
   the continuity of every piece of a tail chain from the pointwise
   family — the list/ℕ bookkeeping needed to state alignment over the
   walk prefixes;
3. **`walk_prefix_alignment`** — the packaging theorem: if a start
   parameter `x₀` of the first walk junction piece (piece `0`) has a full
   forward orbit through the next `n` junction pieces (`htr`), then there
   are sub-pieces — `sp` a sub-piece of piece `0` containing `x₀`, `qs`
   the sub-pieces of the corresponding chain pieces in order — along
   which every transport lands forward (`AlignedTotality (sp :: qs)`).

This is the piece-level content of the exhaustion's next stage: whenever
the exhaustion supplies an orbit (a class sequence whose successive
coordinates transport into the subsequent junction pieces), the alignment
theorems extend the transport from the single orbit to whole interval
sub-pieces with forward totality — the neighbourhood content the
covering lemma reads off.  The remaining bridging (converting the aligned
list back to the ℕ-family of `chain_transport_class_coordinate`, and the
covering lemma `Eₙ`/partial-union ⊆ interval-charted `Uₙ`) is recorded
in the ROADMAP as the next slice.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- The coordinate map of a walk junction piece is continuous (the S102
continuity of the interval-piece transition, read at the piece level —
this supplies the `hcont` hypothesis of the alignment theorem). -/
lemma walkJunctionPiece_continuous {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) :
    Continuous (walkJunctionPiece h hqf hgp cl e hoverlap i).τ := by
  change Continuous (oChartTransitionOnInterval (walkChart h hqf hgp cl e i)
      (walkChart h hqf hgp cl e (i + 1))
      (walkJunctionNbhd h hqf hgp cl e hoverlap i).subset
      (walkJunctionNbhd h hqf hgp cl e hoverlap i).dom)
  exact continuous_oChartTransitionOnInterval (walkChart h hqf hgp cl e i)
    (walkChart h hqf hgp cl e (i + 1))
    (walkJunctionNbhd h hqf hgp cl e hoverlap i).subset
    (walkJunctionNbhd h hqf hgp cl e hoverlap i).dom

/-- Membership in a tail chain is exactly membership in the indexed family
(the elements of `chainTail p k n` are `p (k+j+1)`, `j < n`). -/
lemma chainTail_mem_iff (p : ℕ → MonoPiece) (q : MonoPiece) (k n : ℕ) :
    q ∈ chainTail p k n ↔ ∃ j : ℕ, j < n ∧ q = p (k + j + 1) := by
  revert k
  induction n with
  | zero =>
      intro k
      constructor
      · intro hq
        simp [chainTail] at hq
      · rintro ⟨j, hj, hq⟩
        omega
  | succ n ih =>
      intro k
      constructor
      · intro hq
        simp [chainTail] at hq
        rcases hq with hq | hq
        · refine ⟨0, by omega, ?_⟩
          simpa using hq
        · rcases (ih (k + 1)).mp hq with ⟨j, hj, hqj⟩
          refine ⟨j + 1, by omega, ?_⟩
          exact hqj.trans (congrArg p (by omega))
      · rintro ⟨j, hj, hqj⟩
        rcases j with _ | j
        · simp [chainTail]
          left
          simpa using hqj
        · simp [chainTail]
          right
          have hj' : j < n := by omega
          apply (ih (k + 1)).mpr
          refine ⟨j, hj', ?_⟩
          exact hqj.trans (congrArg p (by omega))

/-- Continuity of every piece of a tail chain, from the pointwise
family. -/
lemma chainTail_continuous {p : ℕ → MonoPiece} (hcont : ∀ i, Continuous (p i).τ)
    (k : ℕ) (n : ℕ) : ∀ q : MonoPiece, q ∈ chainTail p k n → Continuous q.τ := by
  intro q hq
  rcases (chainTail_mem_iff p q k n).mp hq with ⟨j, hj, hq⟩
  rw [hq]
  exact hcont (k + j + 1)

/-- **Walk-prefix alignment (the packaging of the shrinking for walk
prefixes).**  If a start parameter of the first walk junction piece has a
full forward orbit through the next `n` junction pieces (`htr`), then
there are sub-pieces — `sp` of piece `0` containing `x₀`, and `qs`
sub-pieces of the corresponding chain pieces — along which every
transport lands forward (`AlignedTotality (sp :: qs)`): the alignment
machinery instantiated at the walk data (continuity by
`walkJunctionPiece_continuous`). -/
theorem walk_prefix_alignment {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ sp : MonoPiece, ∃ qs : List MonoPiece,
      (∃ hsub : Set.Ioo sp.lo sp.hi ⊆ Set.Ioo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi,
          sp = subMonoPiece (walkJunctionPiece h hqf hgp cl e hoverlap 0) hsub) ∧
      ((x₀ : ℝ) ∈ Set.Ioo sp.lo sp.hi) ∧
      AlignedTotality (sp :: qs) ∧
      List.Forall₂ IsSubPiece qs
        (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) := by
  refine exists_aligned_subpieces
    (rest := chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n)
    (p := walkJunctionPiece h hqf hgp cl e hoverlap 0) ?_ x₀ htr
  intro q hq
  simp at hq
  rcases hq with hq | hq
  · rw [hq]
    exact walkJunctionPiece_continuous h hqf hgp cl e hoverlap 0
  · exact chainTail_continuous (fun i => walkJunctionPiece_continuous h hqf hgp cl e hoverlap i)
      0 n q hq

end LeanEval.KnotTheory.Quadrisecant
