import Mathlib
import Submission.ChainAlignment
import Submission.IntervalCoverU
import Submission.WalkAlignment
import Submission.AlignedFamily

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

/-!
# Milestone-2 (iv) step 6, brick (b) — the covering slice, stage 1: the
aligned family with explicit data and the `hsub` transfer (S124)

`AlignedFamily.lean` (S123) bridged the list-based alignment output to a
ℕ-family (`familyFromAligned`, `chainTail_familyFromAligned`), and
`WalkAlignment.lean` (S122) instantiated the alignment at the S115 walk.
This module opens the COVERING stage: it exposes the aligned walk family
as an explicit ℕ-family with its head/tail data, and transfers the S120
`hsub` (chart-embedding) hypothesis to it — the first half of feeding
`chain_transport_class_coordinate` (S119) with the aligned family.

Content (namespace LeanEval.KnotTheory.Quadrisecant):
1. **data exposure** — `forall₂_subPiece_chainTail` (the positional
   `IsSubPiece` at index `j` of a `Forall₂` against a chain tail, via
   Mathlib's `List.Forall₂.get`), and **`exists_alignedWalk_data`**: from
   the walk overlap data and an orbit `htr` of a start parameter through
   the first `n` junction pieces, `∃ q sp qs`, `q = familyFromAligned w sp
   qs` (so `q` falls back to the walk pieces past the prefix), with
   `q 0` a sub-piece of walk piece `0` containing `x₀`, `AlignedTotality
   (q 0 :: chainTail q 0 n)`, the `Forall₂ IsSubPiece` correspondence of
   `chainTail q 0 n` against `chainTail w 0 n`, and `qs.length = n`.
   The chosen objects `alignedWalkQ`/`alignedWalkSp`/`alignedWalkQs` and
   the spec lemmas (`alignedWalkQ_full_spec` and its projections:
   `alignedWalkQ_eq_family`, `alignedWalkQ_sub0`, `alignedWalkQ_mem0`,
   `alignedWalkQ_totality`, `alignedWalkQ_corr`, `alignedWalkQs_length`).
2. **the sub-piece structure** — `subPiece_self` (every piece is a
   sub-piece of itself) and **`alignedWalkQ_subPiece_all`**: for ALL
   indices `i`, `IsSubPiece (q i) (p i)` — inside the prefix via the
   correspondence (`alignedWalkQ_sub0` at `0`, `Forall₂` position at
   `i = j+1 ≤ n` with `chainTail_get_eq`), beyond the prefix via the
   `familyFromAligned` fall-back (`alignedWalkQ_eq_family` +
   `familyFromAligned_beyond`) and `subPiece_self`.
3. **the `hsub` transfer (done)** — **`alignedWalkQ_chart_subset`**: for
   all `i`, `Ioo (q i).lo (q i).hi ⊆ Ioo (ch i).lo (ch i).hi` — the
   S119 `hsub` hypothesis for the aligned family (sub-piece subset
   composed with the S120 `walkJunction_subset`).

Honest status (recorded in the ROADMAP as S125): the `hsem` transfer —
the second half of the S119 hypotheses — needs a small REFACTOR before
it can be proved: `MonoPiece.τ` has a dependent domain
(`ChartInterval m.lo m.hi → ℝ`), so extracting the pointwise τ-restriction
from an ∃-witness equality `q i = subMonoPiece (p i) hsubᵢ` (with the
chosen `q` opaque, being `Classical.choice`-based) is not Lean-accessible
(`rw`/`erw`/`cases` all fail on the dependent motive).  The fix: carry
the alignment sub-pieces as EXPLICIT per-index data `(aᵢ, bᵢ, hᵢ)` with
`hᵢ : Ioo aᵢ bᵢ ⊆ Ioo (p i).lo (p i).hi`, and define `q i :=
subMonoPiece (p i) hᵢ` — then `(q i).τ` is DEFINITIONALLY the
restriction of `(p i).τ` and the value equality `(q i).τ u = (p i).τ u0`
is `rfl`, making the `hsem` transfer routine.  (This refactor is
contained: `ChainAlignment.exists_aligned_subpieces` gains an explicit
data form; the consumers S122/S123 and this module's data-exposure layer
then rebuild `q` from the explicit data.)  Once `hsem` transfers, the
S119 application (`alignedWalkQ_chain_identification`) and the reach-the-
end covering statement assemble by composition (statements drafted in the
ROADMAP).

Everything here is elementary and verified (no axioms, no `sorry`).
-/


noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

/-- Per-position sub-piece structure of a `Forall₂ IsSubPiece` against a
chainTail: the aligned element at position `j` is a sub-piece of the
chain element `p (k+j+1)`. -/
lemma forall₂_subPiece_chainTail {p q : ℕ → MonoPiece} (k n : ℕ)
    (hcorr : List.Forall₂ IsSubPiece (chainTail q k n) (chainTail p k n))
    (j : ℕ) (hj : j < n) :
    IsSubPiece ((chainTail q k n).get ⟨j, by rw [chainTail_length]; omega⟩)
      ((chainTail p k n).get ⟨j, by rw [chainTail_length]; omega⟩) := by
  exact List.Forall₂.get hcorr (by rw [chainTail_length]; omega) (by rw [chainTail_length]; omega)

/-- **Full walk-aligned data.**  From the S115 walk overlap data and an
orbit `htr` of a start parameter through the first `n` walk junction
pieces, there are the aligned family `q`, its head `sp` and tail list
`qs`, with `q = familyFromAligned w sp qs` (so `q` falls back to the walk
pieces past the prefix), `q 0` a sub-piece of walk piece `0` containing
`x₀`, forward totality `AlignedTotality (q 0 :: chainTail q 0 n)`, the
correspondence of `chainTail q 0 n` against `chainTail w 0 n`, and
`qs.length = n`. -/
theorem exists_alignedWalk_data {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ q : ℕ → MonoPiece, ∃ sp : MonoPiece, ∃ qs : List MonoPiece,
      q = familyFromAligned (walkJunctionPiece h hqf hgp cl e hoverlap) sp qs ∧
      (∃ hsub : Set.Ioo (q 0).lo (q 0).hi ⊆ Set.Ioo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi,
          q 0 = subMonoPiece (walkJunctionPiece h hqf hgp cl e hoverlap 0) hsub) ∧
      ((x₀ : ℝ) ∈ Set.Ioo (q 0).lo (q 0).hi) ∧
      AlignedTotality (q 0 :: chainTail q 0 n) ∧
      List.Forall₂ IsSubPiece (chainTail q 0 n)
        (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ∧
      qs.length = n := by
  rcases walk_prefix_alignment h hqf hgp cl e hoverlap n x₀ htr with ⟨sp, qs, hsp, hx₀sp, htot, hcorr⟩
  let q : ℕ → MonoPiece := familyFromAligned (walkJunctionPiece h hqf hgp cl e hoverlap) sp qs
  have hqsl : qs.length = n := by
    rw [forall₂_length_eq hcorr, chainTail_length]
  have htail : chainTail q 0 n = qs := by
    exact chainTail_familyFromAligned (walkJunctionPiece h hqf hgp cl e hoverlap) sp qs n hqsl
  refine ⟨q, sp, qs, rfl, ?_, ?_, ?_, ?_, hqsl⟩
  · rcases hsp with ⟨hsub, heq⟩
    refine ⟨hsub, ?_⟩
    exact heq
  · exact hx₀sp
  · rw [htail]
    exact htot
  · rw [htail]
    exact hcorr

/-- The aligned walk family (chosen). -/
noncomputable def alignedWalkQ {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) : ℕ → MonoPiece :=
  Classical.choose (exists_alignedWalk_data h hqf hgp cl e hoverlap n x₀ htr)

/-- The aligned head (chosen). -/
noncomputable def alignedWalkSp {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) : MonoPiece :=
  Classical.choose (Classical.choose_spec
    (exists_alignedWalk_data h hqf hgp cl e hoverlap n x₀ htr))

/-- The aligned tail list (chosen). -/
noncomputable def alignedWalkQs {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) : List MonoPiece :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_alignedWalk_data h hqf hgp cl e hoverlap n x₀ htr)))

/-- **Full spec of the aligned walk family.**  The aligned family `q` is
the `familyFromAligned` rebuild of its head and tail list (so past the
prefix it falls back to the walk pieces), and carries the
sub-piece/totality/correspondence/length data of the walk alignment. -/
lemma alignedWalkQ_full_spec {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr =
        familyFromAligned (walkJunctionPiece h hqf hgp cl e hoverlap)
          (alignedWalkSp h hqf hgp cl e hoverlap n x₀ htr)
          (alignedWalkQs h hqf hgp cl e hoverlap n x₀ htr) ∧
      (∃ hsub : Set.Ioo (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).lo
          (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).hi ⊆ Set.Ioo
            (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
            (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi,
          alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0 =
            subMonoPiece (walkJunctionPiece h hqf hgp cl e hoverlap 0) hsub) ∧
      ((x₀ : ℝ) ∈ Set.Ioo (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).lo
        (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).hi) ∧
      AlignedTotality (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0 ::
        chainTail (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr) 0 n) ∧
      List.Forall₂ IsSubPiece (chainTail (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr) 0 n)
        (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ∧
      (alignedWalkQs h hqf hgp cl e hoverlap n x₀ htr).length = n := by
  simpa [alignedWalkQ, alignedWalkSp, alignedWalkQs] using
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (exists_alignedWalk_data h hqf hgp cl e hoverlap n x₀ htr))))

/-- The aligned family is the `familyFromAligned` rebuild of its head and
tail list. -/
lemma alignedWalkQ_eq_family {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr =
      familyFromAligned (walkJunctionPiece h hqf hgp cl e hoverlap)
        (alignedWalkSp h hqf hgp cl e hoverlap n x₀ htr)
        (alignedWalkQs h hqf hgp cl e hoverlap n x₀ htr) :=
  (alignedWalkQ_full_spec h hqf hgp cl e hoverlap n x₀ htr).1

/-- The aligned head is a sub-piece of walk piece `0`. -/
lemma alignedWalkQ_sub0 {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ hsub : Set.Ioo (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).lo
        (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).hi ⊆ Set.Ioo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi,
      alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0 =
        subMonoPiece (walkJunctionPiece h hqf hgp cl e hoverlap 0) hsub :=
  (alignedWalkQ_full_spec h hqf hgp cl e hoverlap n x₀ htr).2.1

/-- The aligned head's interval contains the start parameter. -/
lemma alignedWalkQ_mem0 {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    (x₀ : ℝ) ∈ Set.Ioo (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).lo
      (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0).hi :=
  (alignedWalkQ_full_spec h hqf hgp cl e hoverlap n x₀ htr).2.2.1

/-- Forward totality of the aligned prefix. -/
lemma alignedWalkQ_totality {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    AlignedTotality (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr 0 ::
      chainTail (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr) 0 n) :=
  (alignedWalkQ_full_spec h hqf hgp cl e hoverlap n x₀ htr).2.2.2.1

/-- Correspondence of the aligned tail against the walk chain tail. -/
lemma alignedWalkQ_corr {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    List.Forall₂ IsSubPiece (chainTail (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr) 0 n)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) :=
  (alignedWalkQ_full_spec h hqf hgp cl e hoverlap n x₀ htr).2.2.2.2.1

/-- The aligned tail list has length `n`. -/
lemma alignedWalkQs_length {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    (alignedWalkQs h hqf hgp cl e hoverlap n x₀ htr).length = n :=
  (alignedWalkQ_full_spec h hqf hgp cl e hoverlap n x₀ htr).2.2.2.2.2

/-- Every piece is a sub-piece of itself (the whole interval). -/
lemma subPiece_self (p : MonoPiece) : IsSubPiece p p := by
  refine ⟨(fun t ht => ht), ?_⟩
  cases p with
  | mk lo hi τ hmono => rfl

/-- **Every aligned piece is a sub-piece of the corresponding walk piece.**
For all indices `i` (including beyond the prefix, where `q` falls back to
the walk pieces), `q i` is a sub-piece of `p i`. -/
lemma alignedWalkQ_subPiece_all {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) (i : ℕ) :
    IsSubPiece (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr i)
      (walkJunctionPiece h hqf hgp cl e hoverlap i) := by
  by_cases hin : i ≤ n
  · rcases i with _ | j
    · exact alignedWalkQ_sub0 h hqf hgp cl e hoverlap n x₀ htr
    · have hj : j < n := by omega
      have hq : alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr (j + 1) =
          (chainTail (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr) 0 n).get
            ⟨j, by rw [chainTail_length]; omega⟩ := by
        rw [chainTail_get_eq (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr) 0 n j
          (by rw [chainTail_length]; omega)]
        congr 1
        omega
      have hgetp : (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n).get
          ⟨j, by rw [chainTail_length]; omega⟩ = walkJunctionPiece h hqf hgp cl e hoverlap (j + 1) := by
        rw [chainTail_get_eq (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n j
          (by rw [chainTail_length]; omega)]
        congr 1
        omega
      have hpos := forall₂_subPiece_chainTail
        (p := walkJunctionPiece h hqf hgp cl e hoverlap)
        (q := alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr) 0 n
        (alignedWalkQ_corr h hqf hgp cl e hoverlap n x₀ htr) j hj
      rwa [← hq, hgetp] at hpos
  · have hgt : n < i := by omega
    have hb : alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr i =
        walkJunctionPiece h hqf hgp cl e hoverlap i := by
      rw [alignedWalkQ_eq_family h hqf hgp cl e hoverlap n x₀ htr]
      exact familyFromAligned_beyond (walkJunctionPiece h hqf hgp cl e hoverlap)
        (alignedWalkSp h hqf hgp cl e hoverlap n x₀ htr)
        (alignedWalkQs h hqf hgp cl e hoverlap n x₀ htr) n i hgt
        (alignedWalkQs_length h hqf hgp cl e hoverlap n x₀ htr)
    have hself := subPiece_self (walkJunctionPiece h hqf hgp cl e hoverlap i)
    rw [hb]
    exact hself

/-- **Chart-embedding of the aligned family** (the S119 `hsub` hypothesis
for the aligned `q`): every aligned piece interval embeds into the
corresponding chart interval (sub-piece ⊆ walk piece ⊆ chart). -/
lemma alignedWalkQ_chart_subset {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) (i : ℕ) :
    Set.Ioo (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr i).lo
      (alignedWalkQ h hqf hgp cl e hoverlap n x₀ htr i).hi ⊆
    Set.Ioo (walkChart h hqf hgp cl e i).lo (walkChart h hqf hgp cl e i).hi := by
  rcases alignedWalkQ_subPiece_all h hqf hgp cl e hoverlap n x₀ htr i with ⟨hqp, heq⟩
  intro t ht
  exact walkJunction_subset h hqf hgp cl e hoverlap i (hqp ht)


/-! ## S126 step (2) — the walk-prefix aligned sub-data (the ℕ-indexed
form with explicit per-index data)

`ChainAlignment` (S126) added the pure explicit-data alignment
(`SubDatum`, `exists_aligned_subdata`); this section instantiates it at
the walk in the form the `hsem` transfer needs: per-index datum data
indexed by the CONCRETE walk pieces (so `datumPiece (sub i)` restricts
`w i` definitionally), with the head datum and the function datum data
carried explicitly.  Supporting content: `subDatum_refl` (the
whole-interval datum), `datumPiece_refl`, `transports_congr_piece` (the
`cases`-based transport of the transport predicate across a piece
equality — the tool that avoids any `MonoPiece.τ` dependent rewrite),
`chainTail_congr_right` (chain tails of function families agreeing past
`k` are equal), and the headline **`exists_walk_aligned_subdata`**: from
walk overlap data and an orbit of a start parameter of piece `k` through
the next `n` junction pieces, `∃ d0 : SubDatum (w k), ∃ sub : (i : ℕ) →
SubDatum (w i)`, `sub k = d0`, `x₀ ∈ Ioo d0.lo d0.hi`, and forward
totality from `datumPiece d0` through `chainTail (fun i => datumPiece
(sub i)) k n`.  (The proof is the S119-style backward induction on `n`:
base = whole-interval datum; step = land into the IH's head datum
(`exists_subdata_landing`), extend `sub` at `k`, and close the totality
with the landing membership + the IH totality transported through
`hpiece := datumPiece (sub (k+1)) = datumPiece d0'` by
`transports_congr_piece`.)  The next step (S127) reopens the `hsem`
transfer: the value conjunct is `datumPiece_τ` (rfl) and the
membership/lift conjuncts transfer by the equal-real-value element
equality.  Everything here is elementary and verified (no axioms, no
`sorry`).
-/

/-- The whole-interval datum of a piece (the identity sub-piece). -/
def subDatum_refl (p : MonoPiece) : SubDatum p :=
  { lo := p.lo, hi := p.hi, sub := fun _ ht => ht }

/-- The whole-interval datum's piece is the piece itself (definitional). -/
lemma datumPiece_refl (p : MonoPiece) : datumPiece (subDatum_refl p) = p := by
  rfl

/-- Transport of the transport predicate across a piece equality
(`cases`-based: free pieces, so no `MonoPiece.τ` rewrite is needed). -/
lemma transports_congr_piece {p p' : MonoPiece} {rest : List MonoPiece}
    (hpp : p = p') (x : ChartInterval p.lo p.hi) :
    transports p rest x ↔
      transports p' rest ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) hpp) ▸ x) := by
  cases hpp
  simp

/-- Chain tails of two function families agree when the functions agree
on all indices past `k`. -/
lemma chainTail_congr_right {p q : ℕ → MonoPiece} : ∀ (k n : ℕ),
    (∀ i : ℕ, k + 1 ≤ i → p i = q i) → chainTail p k n = chainTail q k n := by
  intro k n
  revert k
  induction n with
  | zero => intro k h; simp [chainTail]
  | succ n ih =>
      intro k h
      simp [chainTail]
      constructor
      · exact h (k + 1) (by omega)
      · exact ih (k + 1) (fun i hi => h i (by omega))

/-- **Walk-prefix aligned sub-data (the ℕ-indexed form).**  From the S115
walk data and an orbit `htr` of a start parameter of piece `k` through
the next `n` junction pieces, there is a head datum `d0 : SubDatum (w k)`
containing `x₀`, together with per-index datum data
`sub : (i : ℕ) → SubDatum (w i)` agreeing with `d0` at `k` and giving
forward totality from the head datum through the whole aligned tail —
with `q i := datumPiece (sub i)` the aligned pieces restrict the walk
pieces definitionally. -/
theorem exists_walk_aligned_subdata {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) :
    ∀ k n : ℕ,
    ∀ (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap k).lo
        (walkJunctionPiece h hqf hgp cl e hoverlap k).hi),
      transports (walkJunctionPiece h hqf hgp cl e hoverlap k)
        (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) k n) x₀ →
      ∃ d0 : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap k),
      ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
        sub k = d0 ∧ ((x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi) ∧
        (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
          transports (datumPiece d0)
            (chainTail (fun i => datumPiece (sub i)) k n) y) := by
  classical
  let w : ℕ → MonoPiece := walkJunctionPiece h hqf hgp cl e hoverlap
  have hcont : ∀ i, Continuous (w i).τ := fun i =>
    walkJunctionPiece_continuous h hqf hgp cl e hoverlap i
  intro k n
  revert k
  induction n with
  | zero =>
      intro k x₀ htr
      let d0 : SubDatum (w k) := subDatum_refl (w k)
      refine ⟨d0, (fun i => subDatum_refl (w i)), ?_, ?_, ?_⟩
      · rfl
      · change (x₀ : ℝ) ∈ Set.Ioo (w k).lo (w k).hi
        exact x₀.2
      · intro y
        change transports (datumPiece (subDatum_refl (w k))) [] y
        simp [transports]
  | succ n ih =>
      intro k x₀ htr
      have hsplit : chainTail w k (n + 1) = w (k + 1) :: chainTail w (k + 1) n := by
        simp [chainTail]
      rw [hsplit] at htr
      rcases htr with ⟨h, htr'⟩
      let x₁ : ChartInterval (w (k + 1)).lo (w (k + 1)).hi := ⟨(w k).τ x₀, h⟩
      rcases ih (k + 1) x₁ htr' with ⟨d0', sub', hsub'k1, hx₁mem, htot'⟩
      have hx1 : (w k).τ x₀ ∈ Set.Ioo (datumPiece d0').lo (datumPiece d0').hi := by
        change (w k).τ x₀ ∈ Set.Ioo d0'.lo d0'.hi
        simpa [x₁] using hx₁mem
      rcases exists_subdata_landing (w k) (datumPiece d0')
          (hcont k) x₀ hx1 with ⟨d0, hx₀mem, hland⟩
      let sub : (i : ℕ) → SubDatum (w i) := fun i =>
        if hik : i = k then
          Eq.mpr (congrArg (fun m : MonoPiece => SubDatum m) (congrArg w hik)) d0
        else sub' i
      have hsubk : sub k = d0 := by
        simp [sub]
      have hsubk1 : sub (k + 1) = sub' (k + 1) := by
        dsimp [sub]
        rw [dif_neg (by omega)]
      refine ⟨d0, sub, hsubk, hx₀mem, ?_⟩
      intro y
      change transports (datumPiece d0) (datumPiece (sub (k + 1)) ::
          chainTail (fun i => datumPiece (sub i)) (k + 1) n) y
      have hmem : (datumPiece d0).τ y ∈ Set.Ioo (datumPiece (sub (k + 1))).lo
          (datumPiece (sub (k + 1))).hi := by
        rw [hsubk1, hsub'k1]
        exact hland y
      refine ⟨hmem, ?_⟩
      have hrest : chainTail (fun i => datumPiece (sub i)) (k + 1) n =
          chainTail (fun i => datumPiece (sub' i)) (k + 1) n := by
        apply chainTail_congr_right (k := k + 1) (n := n)
        intro i hi
        congr 1
        dsimp [sub]
        rw [dif_neg (by omega)]
      rw [hrest]
      have hpiece : datumPiece (sub (k + 1)) = datumPiece d0' := by
        rw [hsubk1, hsub'k1]
      have htrs : transports (datumPiece d0')
          (chainTail (fun i => datumPiece (sub' i)) (k + 1) n)
          ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) hpiece) ▸
            ⟨(datumPiece d0).τ y, hmem⟩) :=
        htot' ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) hpiece) ▸
          ⟨(datumPiece d0).τ y, hmem⟩)
      exact (transports_congr_piece (p := datumPiece (sub (k + 1))) (p' := datumPiece d0')
        (rest := chainTail (fun i => datumPiece (sub' i)) (k + 1) n) hpiece
          ⟨(datumPiece d0).τ y, hmem⟩).mpr htrs
/-! ## S128 — the `hsem` transfer reopened: datum-level semantics (the
value conjunct by `datumPiece_τ`)

With the walk data in explicit `SubDatum` form (`exists_walk_aligned_subdata`,
S127), the class-coordinate semantics transfer per datum is now routine:
for a datum `d : SubDatum (w i)` and a parameter `u` of `datumPiece d`,
`datumPiece_chartSubset` composes the datum's own interval embedding with
the S120 `walkJunction_subset` (the S119 `hsub` at the datum), and
`datumPiece_semantics` gives the full S119-`hsem` statement for the datum
piece: the class of the `ch i`-parameter `⟨(u : ℝ), hsub u.2⟩` lies in
the next trace, and there is a transition element whose lift equals that
class and whose real value is `(datumPiece d).τ u` — the VALUE conjunct
closes by `datumPiece_τ` (definitional restriction, `rfl`-level) plus the
equal-real-value element equality for the membership/lift conjuncts.
Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- The chart embedding of a datum sub-piece (the S119 `hsub` for the
piece `datumPiece d`): the datum interval embeds into the walk piece's
interval (`d.sub`) and then into the chart interval
(`walkJunction_subset`). -/
lemma datumPiece_chartSubset {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ)
    (d : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i)) :
    Set.Ioo (datumPiece d).lo (datumPiece d).hi ⊆
    Set.Ioo (walkChart h hqf hgp cl e i).lo (walkChart h hqf hgp cl e i).hi := by
  intro t ht
  exact walkJunction_subset h hqf hgp cl e hoverlap i (d.sub ht)

/-- **The S119 `hsem` statement for a datum piece.**  For a datum
`d : SubDatum (w i)` of the walk piece at index `i` and a parameter `u`
of `datumPiece d`, the class of the `ch i`-parameter
`⟨(u : ℝ), datumPiece_chartSubset … d u.2⟩` lies in the trace of the
next chart, and there is a transition element `y` whose lift is that
class and whose real value is `(datumPiece d).τ u` — transferred from
`walkJunction_semantics` (S120) through the datum (the VALUE conjunct is
`datumPiece_τ`, definitional; the membership/lift conjuncts are the
same-class equal-real-value equalities). -/
lemma datumPiece_semantics {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ)
    (d : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (u : ChartInterval (datumPiece d).lo (datumPiece d).hi) :
    oChartLift (walkChart h hqf hgp cl e i)
        ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap i d u.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e (i + 1)) ∧
    ∃ y : OChartTransitionDomain (walkChart h hqf hgp cl e (i + 1))
        (walkChart h hqf hgp cl e i),
      oChartLift (walkChart h hqf hgp cl e (i + 1)) y.1 =
        oChartLift (walkChart h hqf hgp cl e i)
          ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap i d u.2⟩ ∧
      (y.1 : ℝ) = (datumPiece d).τ u := by
  let w : ℕ → MonoPiece := walkJunctionPiece h hqf hgp cl e hoverlap
  let u0 : ChartInterval (w i).lo (w i).hi := ⟨(u : ℝ), d.sub u.2⟩
  rcases walkJunction_semantics h hqf hgp cl e hoverlap i u0 with ⟨hin, y, hylift, hyval⟩
  have hE : (⟨(u0 : ℝ), walkJunction_subset h hqf hgp cl e hoverlap i u0.2⟩ :
        ChartInterval (walkChart h hqf hgp cl e i).lo (walkChart h hqf hgp cl e i).hi) =
      ⟨(u : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap i d u.2⟩ := by
    apply Subtype.ext
    change (u0 : ℝ) = (u : ℝ)
    rfl
  constructor
  · rw [hE] at hin
    exact hin
  · refine ⟨y, ?_, ?_⟩
    · rw [hE] at hylift
      exact hylift
    · rw [datumPiece_τ d u]
      exact hyval

/-! ## S129 — the S119 application on the datum family: the aligned start
interval reaches the end chart

The S125 wall is gone (datum-level `hsub`/`hsem` in hand), so the
assembly is composition: choose the walk-aligned sub-data
(`exists_walk_aligned_subdata` at `k = 0`), set the aligned family
`q i := datumPiece (sub i)` with the datum-level `hsub`/`hsem`
(`datumPiece_chartSubset`, `datumPiece_semantics`), convert the
alignment totality to a transport at the head piece (which is
`datumPiece (sub 0)`, equal to `datumPiece d0` by `sub 0 = d0`, via
`transports_congr_piece`), and apply
`chain_transport_class_coordinate` at `(0, n)` — every class of the
aligned start interval is reached in the `(n+1)`-th chart. -/

/-- **The aligned start interval reaches the end chart.**  From the walk
overlap data and an orbit `htr` of a start parameter through the first
`n` junction pieces, there is datum data (`d0` at the head, `sub` at
every index, `sub 0 = d0`) containing `x₀` in the aligned head interval,
and every class parametrised by the aligned start interval lies in the
trace of the `(n+1)`-th walk chart: the class-coordinate identification
of S119 applied to the datum family (`q i := datumPiece (sub i)`, with
the datum-level `hsub`/`hsem`), the totality supplied by the alignment
(`AlignedTotality`-content of `exists_walk_aligned_subdata`) transported
to the head piece by `transports_congr_piece`. -/
theorem walkAligned_reaches_end {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ d0 : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap 0),
    ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      sub 0 = d0 ∧
      ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        ∃ y : OChartTransitionDomain (walkChart h hqf hgp cl e (0 + n + 1))
            (walkChart h hqf hgp cl e 0),
          oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1 =
            oChartLift (walkChart h hqf hgp cl e 0)
              ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩) := by
  rcases exists_walk_aligned_subdata h hqf hgp cl e hoverlap 0 n x₀ htr with ⟨d0, sub, hsub0, hx₀mem, htot⟩
  refine ⟨d0, sub, hsub0, ?_, ?_⟩
  · rw [hsub0]
    exact hx₀mem
  · intro x
    have hpp : datumPiece (sub 0) = datumPiece d0 := by
      rw [hsub0]
    have htrx : transports (datumPiece (sub 0))
        (chainTail (fun i => datumPiece (sub i)) 0 n) x :=
      (transports_congr_piece (p := datumPiece (sub 0)) (p' := datumPiece d0) hpp x).mpr
        (htot ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) hpp) ▸ x))
    rcases chain_transport_class_coordinate (ch := walkChart h hqf hgp cl e)
        (p := fun i => datumPiece (sub i))
        (hsub := fun i => datumPiece_chartSubset h hqf hgp cl e hoverlap i (sub i))
        (hsem := fun i u => datumPiece_semantics h hqf hgp cl e hoverlap i (sub i) u)
        0 n ⟨x, htrx⟩ with ⟨y, hy⟩
    exact ⟨y, hy.1⟩

/-! ## S130 — the interval-charted arc from the aligned start interval

`walkAligned_reaches_end` (S129) is repackaged into the interval-chart
form: the aligned start interval parametrises an arc of trisecant classes
(`walkAlignedArcMap`, the `ch 0`-lift through the datum chart embedding)
that (a) contains the class of the start parameter `x₀`, (b) is
INJECTIVE (`oChartLift_injective`, S100 — two equal classes have equal
parameters, so equal arc points have equal interval parameters), and (c)
reaches the `(n+1)`-th chart: every arc class lies in the trace of
`ch (0+n+1)`.  This is the per-prefix interval-charted arc the covering
statement consumes. -/

/-- The class of a parameter of the aligned start interval (the `ch 0`-
lift through the datum chart embedding). -/
def walkAlignedArcMap {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i)) :
    ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi → OSub r := fun x =>
  oChartLift (walkChart h hqf hgp cl e 0)
    ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩

/-- **The interval-charted arc reaches the end chart and contains the
start class.**  From walk overlap data and an orbit `htr` of a start
parameter through the first `n` junction pieces, there is per-index datum
data `sub` whose aligned start interval contains `x₀` and parametrises
(injectively) classes all lying in the trace of the `(n+1)`-th walk
chart — the arc form of `walkAligned_reaches_end`. -/
theorem walkAligned_arc_reaches_end {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          chartTrace (walkChart h hqf hgp cl e (0 + n + 1))) := by
  rcases walkAligned_reaches_end h hqf hgp cl e hoverlap n x₀ htr with ⟨d0, sub, hsub0, hx₀mem, hcover⟩
  refine ⟨sub, ?_, ?_⟩
  · exact hx₀mem
  · intro x
    rcases hcover x with ⟨y, hy⟩
    have hm : oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1 ∈
        chartTrace (walkChart h hqf hgp cl e (0 + n + 1)) := by
      exact (mem_chartTrace (walkChart h hqf hgp cl e (0 + n + 1))
        (oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1)).mpr
        (oChartLift_mem_W (walkChart h hqf hgp cl e (0 + n + 1)) y.1)
    change oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e (0 + n + 1))
    rw [← hy]
    exact hm

/-- The arc map is injective: equal classes have equal parameters
(`oChartLift_injective`), so the aligned start interval parametrises an
arc without self-intersections. -/
lemma walkAlignedArcMap_injective {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i)) :
    Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) := by
  intro x y hxy
  have hl := oChartLift_injective (walkChart h hqf hgp cl e 0)
  have harg : (⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩ :
        ChartInterval (walkChart h hqf hgp cl e 0).lo (walkChart h hqf hgp cl e 0).hi) =
      ⟨(y : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) y.2⟩ := by
    apply hl
    simpa [walkAlignedArcMap] using hxy
  have hv := congrArg (fun z : ChartInterval (walkChart h hqf hgp cl e 0).lo
      (walkChart h hqf hgp cl e 0).hi => (z : ℝ)) harg
  apply Subtype.ext
  simpa using hv

/-! ## S131 — the orbit class lies in every prefix chart trace

The class of the orbit-start parameter (the class transported along
the chain by `htr`) is a trisecant class lying in EVERY chart trace of
the prefix `ch 0, …, ch (n+1)`: its membership in `ch (0+i+1)` (for each
`i ≤ n`) is the S119 class-coordinate identification applied to the
prefix of length `i` (whose transport exists by
`transports_chainTail_prefix`), read at the orbit point.  This is the
deep-intersection content the exhaustion uses (a class from which
interval arcs extend through the whole prefix). -/

/-- Transporting through a longer chain transports through any prefix
(chain tails are nested). -/
lemma transports_chainTail_prefix {p : ℕ → MonoPiece} (k : ℕ) :
    ∀ (n i : ℕ), i ≤ n → ∀ x : ChartInterval (p k).lo (p k).hi,
      transports (p k) (chainTail p k n) x → transports (p k) (chainTail p k i) x := by
  intro n
  revert k
  induction n with
  | zero =>
      intro k i hi x htr
      have hi0 : i = 0 := by omega
      subst i
      simp [transports, chainTail]
  | succ n ih =>
      intro k i hi x htr
      rcases i with _ | j
      · simp [transports, chainTail]
      · have hj : j ≤ n := by omega
        rcases htr with ⟨h0, hrest⟩
        refine ⟨h0, ?_⟩
        exact ih (k + 1) j hj ⟨(p k).τ x, h0⟩ hrest

/-- **The orbit class lies in every prefix chart trace.**  From walk
overlap data and an orbit `htr` of a start parameter through the first
`n` junction pieces, the class of the start parameter (the `ch 0`-lift
of the start parameter) lies in the trace of `ch m` for every
`1 ≤ m ≤ n+1` — the class-coordinate identification of S119 applied at
each prefix length. -/
theorem walkOrbitClass_mem_traces {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x0 : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x0) :
    ∀ i : ℕ, i ≤ n →
      oChartLift (walkChart h hqf hgp cl e 0)
          ⟨(x0 : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x0.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e (0 + i + 1)) := by
  let w : ℕ → MonoPiece := walkJunctionPiece h hqf hgp cl e hoverlap
  intro i hi
  have htrp : transports (w 0) (chainTail w 0 i) x0 := by
    exact transports_chainTail_prefix (p := w) 0 n i hi x0 htr
  rcases chain_transport_class_coordinate (ch := walkChart h hqf hgp cl e)
      (p := w)
      (hsub := fun i => walkJunction_subset h hqf hgp cl e hoverlap i)
      (hsem := fun i u => walkJunction_semantics h hqf hgp cl e hoverlap i u)
      0 i ⟨x0, htrp⟩ with ⟨y, hy⟩
  have hm' : oChartLift (walkChart h hqf hgp cl e (0 + i + 1)) y.1 ∈
      chartTrace (walkChart h hqf hgp cl e (0 + i + 1)) := by
    exact (mem_chartTrace (walkChart h hqf hgp cl e (0 + i + 1))
      (oChartLift (walkChart h hqf hgp cl e (0 + i + 1)) y.1)).mpr
      (oChartLift_mem_W (walkChart h hqf hgp cl e (0 + i + 1)) y.1)
  have hc0 : oChartLift (walkChart h hqf hgp cl e 0)
      ⟨(x0 : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x0.2⟩ ∈
      chartTrace (walkChart h hqf hgp cl e (0 + i + 1)) := by
    rw [hy.1] at hm'
    exact hm'
  exact hc0

/-! ## S132 — the arc as a continuous injective interval-chart at the
orbit class

The S130 arc (`walkAlignedArcMap`) is upgraded to an interval-chart at
the orbit class: it is CONTINUOUS (the `ch 0`-lift is continuous —
composition of the chart homeo with the subtype projection — and the
interval embedding is continuous), injective (S130), contains the orbit
class `c0` (the arc value at the parameter equal to `x0`'s real value is
the `ch 0`-lift of `x0`, i.e. `c0` — chart parameters with equal real
values have equal lifts), and (S130) reaches the `(0+n+1)`-th chart
trace.  This is the per-orbit interval-charted arc the exhaustion glues. -/

/-- The `ch 0`-lift is continuous on the chart interval (the chart homeo
composed with the subtype projection). -/
lemma continuous_oChartLift {r : ℝ → Space} {c0 : OSub r} (ch : OSub1Chart r c0) :
    Continuous (fun t : ChartInterval ch.lo ch.hi => oChartLift ch t) := by
  change Continuous (fun t : ChartInterval ch.lo ch.hi =>
    ((ch.homeo t : {c : OSub r // (c : OpenMobius) ∈ ch.W}) : OSub r))
  exact continuous_subtype_val.comp ch.homeo.continuous

/-- The arc map is continuous (the chart lift of the interval embedding). -/
lemma continuous_walkAlignedArcMap {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i)) :
    Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) := by
  have hc := continuous_oChartLift (walkChart h hqf hgp cl e 0)
  refine hc.comp ?_
  exact Continuous.subtype_mk continuous_subtype_val
    (fun x => datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2)

/-- **The arc value at the orbit parameter is the orbit class.**  The
arc map sends the parameter with the real value of `x0` to the `ch 0`-
lift of `x0` (the orbit class) — chart parameters with equal real values
have equal lifts, so the membership proofs do not matter. -/
lemma walkAlignedArcMap_at_orbitClass {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i))
    (x0 : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (mem : (x0 : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) :
    walkAlignedArcMap h hqf hgp cl e hoverlap sub ⟨(x0 : ℝ), mem⟩ =
      oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(x0 : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x0.2⟩ := by
  rfl

/-- **The interval-charted arc at the orbit class.**  From walk overlap
data and an orbit `htr` of a start parameter through the first `n`
junction pieces, there is per-index datum data `sub` whose aligned start
interval contains the orbit parameter and whose arc map is injective and
continuous and sends the orbit parameter to the orbit class (which by
S131 lies in every prefix chart trace).  This is the arc-chart datum the
exhaustion glues. -/
theorem walkAligned_arcChart_at_orbit {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x0 : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x0) :
    ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x0 : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      (∀ mem : (x0 : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub ⟨(x0 : ℝ), mem⟩ =
          oChartLift (walkChart h hqf hgp cl e 0)
            ⟨(x0 : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x0.2⟩) := by
  rcases walkAligned_reaches_end h hqf hgp cl e hoverlap n x0 htr with ⟨d0, sub, hsub0, hx0mem, hcover⟩
  refine ⟨sub, ?_, ?_, ?_, ?_⟩
  · exact hx0mem
  · exact walkAlignedArcMap_injective h hqf hgp cl e hoverlap sub
  · exact continuous_walkAlignedArcMap h hqf hgp cl e hoverlap sub
  · intro mem
    exact walkAlignedArcMap_at_orbitClass h hqf hgp cl e hoverlap sub x0 mem

/-! ## S133 — the exhaustion covering overlap: the arc interval-chart in
the overlap of the exhaustion region with the far chart

For a prefix of the walk with an orbit `htr`, the arc-chart datum of S132
is a continuous injective interval parametrisation of trisecant classes
whose image lies in the OVERLAP of the start chart's trace (every arc
class is a `ch 0`-lift) with the far chart's trace (`ch (0+n+1)` — S130),
and which is ANCHORED at the orbit class (the arc value at the orbit
parameter is the orbit class, which by S131 lies in every prefix chart
trace).  This is the exhaustion-covering overlap condition: the arc
provides the interval-charted bridge from the exhaustion region to the
next chart's trace around the common anchor class. -/

/-- **The exhaustion-covering overlap.**  From walk overlap data and an
orbit `htr` of a start parameter through the first `n` junction pieces,
there is per-index datum data `sub` whose aligned start interval contains
the orbit parameter and whose arc map is injective, continuous, anchored
at the orbit class, and contained in the overlap of the start chart's
trace with the far chart's trace `ch (0+n+1)`. -/
theorem walkAligned_covering_overlap {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x0 : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x0) :
    ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x0 : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      (∀ mem : (x0 : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub ⟨(x0 : ℝ), mem⟩ =
          oChartLift (walkChart h hqf hgp cl e 0)
            ⟨(x0 : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x0.2⟩) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          chartTrace (walkChart h hqf hgp cl e 0)) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          chartTrace (walkChart h hqf hgp cl e (0 + n + 1))) := by
  rcases walkAligned_reaches_end h hqf hgp cl e hoverlap n x0 htr with ⟨d0, sub, hsub0, hx0mem, hcover⟩
  refine ⟨sub, hx0mem, ?_, ?_, ?_, ?_, ?_⟩
  · exact walkAlignedArcMap_injective h hqf hgp cl e hoverlap sub
  · exact continuous_walkAlignedArcMap h hqf hgp cl e hoverlap sub
  · intro mem
    exact walkAlignedArcMap_at_orbitClass h hqf hgp cl e hoverlap sub x0 mem
  · intro x
    exact (mem_chartTrace (walkChart h hqf hgp cl e 0)
        (walkAlignedArcMap h hqf hgp cl e hoverlap sub x)).mpr (by
      change (oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩ : OpenMobius) ∈
          (walkChart h hqf hgp cl e 0).W
      exact oChartLift_mem_W (walkChart h hqf hgp cl e 0)
        ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩)
  · intro x
    rcases hcover x with ⟨y, hy⟩
    have hm : oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1 ∈
        chartTrace (walkChart h hqf hgp cl e (0 + n + 1)) := by
      exact (mem_chartTrace (walkChart h hqf hgp cl e (0 + n + 1))
        (oChartLift (walkChart h hqf hgp cl e (0 + n + 1)) y.1)).mpr
        (oChartLift_mem_W (walkChart h hqf hgp cl e (0 + n + 1)) y.1)
    change oChartLift (walkChart h hqf hgp cl e 0)
        ⟨(x : ℝ), datumPiece_chartSubset h hqf hgp cl e hoverlap 0 (sub 0) x.2⟩ ∈
        chartTrace (walkChart h hqf hgp cl e (0 + n + 1))
    rw [← hy]
    exact hm
/-! ## S135 — orbit extension at the walk level (`walkOrbit_extend`)
and the repeated-extension re-run at `n+1`

`ChainAlignment` (S134) proved the pure orbit-extension principle
`transports_extend` (an `n`-tail transport whose chain value lands in the
next piece `p (k+n+1)` extends to an `(n+1)`-tail transport).  This
section instantiates it at the S115 walk (the only new landing in the
extended chain is the chain value — the far-end coordinate after
`w 0, …, w n` — landing in the next junction piece `w (n+1)`), and
packages the re-run: the extended orbit feeds the alignment machinery at
length `n+1`, so the interval-charted arc re-runs one junction further
(the arc's classes reach the `(n+2)`-th walk chart's trace, anchored at
the same orbit parameter).  This is the one-step extension of the
interval-chain exhaustion `Uₙ`; the far-end landing itself is supplied by
the component/curve hypothesis (per the S106 scoping note). -/

/-- **Orbit extension at the walk level.**  From the walk overlap data
and an orbit `htr` of a start parameter through the first `n` junction
pieces, if the chain value (the far-end coordinate — the value after
applying the junction coordinate maps `w 0, …, w n`) lands in the next
junction piece `w (n+1)`, then the orbit extends through `n+1` junction
pieces: `transports (w 0) (chainTail w 0 (n+1)) x₀`.  (This is the pure
`transports_extend` instantiated at the walk; the far-end landing is
where the component/curve hypothesis of the exhaustion enters.) -/
theorem walkOrbit_extend {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀)
    (hland : chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
        chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi) :
    transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 (n + 1)) x₀ := by
  have hland' : chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
        chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (0 + n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (0 + n + 1)).hi := by
    simpa [show (0 + n + 1 : ℕ) = (n + 1 : ℕ) by omega] using hland
  exact transports_extend (p := walkJunctionPiece h hqf hgp cl e hoverlap) 0 n x₀ htr hland'

/-- **Repeated extension: the re-run at `n+1`.**  From the walk overlap
data, an orbit through the first `n` junction pieces, and the far-end
chain value landing in the next junction piece, the alignment machinery
re-runs at length `n+1`: there is datum data `sub` whose aligned start
interval contains the orbit parameter and whose arc of classes reaches
the trace of the `(n+2)`-th walk chart — the one-step extension of the
interval-charted exhaustion arc. -/
theorem walkOrbit_extend_reaches_end {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀)
    (hland : chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
        chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          chartTrace (walkChart h hqf hgp cl e (0 + (n + 1) + 1))) := by
  exact walkAligned_arc_reaches_end h hqf hgp cl e hoverlap (n + 1) x₀
    (walkOrbit_extend h hqf hgp cl e hoverlap n x₀ htr hland)

/-! ## S136 — all-lengths orbits under a uniform landing hypothesis
(`walkOrbit_all_lengths`) and the per-length covering overlaps

The S135 one-step extension (`walkOrbit_extend`) is iterated: if the
landing hypothesis is UNIFORM — whenever an orbit through the first `n`
junction pieces exists, its chain value lands in the next junction piece
`w (n+1)` — then orbits through every prefix length exist (induction from
the empty transport).  This is the interface where the component/curve
content plugs in (per the S106 scoping note, the exhaustion's landing
data must be supplied by the proper objects); given it, the S133
covering-overlap machinery runs at every prefix length. -/

/-- **All-lengths orbit family.**  Under a uniform landing hypothesis —
whenever an orbit through the first `n` junction pieces exists, its chain
value (the far-end coordinate) lands in the next junction piece `w (n+1)`
— orbits through EVERY prefix length exist: `∀ n, transports (w 0)
(chainTail w 0 n) x₀`.  (Induction on `n` from the empty transport,
extending at each step by `transports_extend`; the uniform hypothesis is
the interface where the component/curve content plugs in.) -/
theorem walkOrbit_all_lengths {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
          (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
          chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∀ n : ℕ, transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀ := by
  intro n
  induction n with
  | zero =>
      change transports (walkJunctionPiece h hqf hgp cl e hoverlap 0) [] x₀
      simp [transports]
  | succ n ih =>
      have hland' : chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
            chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, ih⟩ ∈
            Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (0 + n + 1)).lo
              (walkJunctionPiece h hqf hgp cl e hoverlap (0 + n + 1)).hi := by
        simpa [show (0 + n + 1 : ℕ) = (n + 1 : ℕ) by omega] using hland n ih
      exact transports_extend (p := walkJunctionPiece h hqf hgp cl e hoverlap) 0 n x₀ ih hland'

/-- **Covering overlaps at every length.**  Under the uniform landing
hypothesis, the alignment machinery runs at every prefix length: for each
`n`, datum data `sub` whose aligned start interval contains the orbit
parameter and whose arc map is injective, continuous, anchored at the
orbit class, and contained in the overlap of the start chart's trace with
the far chart's trace `ch (0+n+1)` — the per-length exhaustion-covering
data. -/
theorem walkOrbit_all_lengths_covering {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
          (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
          chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∀ n : ℕ, ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      (∀ mem : (x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub ⟨(x₀ : ℝ), mem⟩ =
          oChartLift (walkChart h hqf hgp cl e 0)
            ⟨(x₀ : ℝ), walkJunction_subset h hqf hgp cl e hoverlap 0 x₀.2⟩) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          chartTrace (walkChart h hqf hgp cl e 0)) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          chartTrace (walkChart h hqf hgp cl e (0 + n + 1))) := by
  intro n
  exact walkAligned_covering_overlap h hqf hgp cl e hoverlap n x₀
    (walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀ hland n)


/-! ## S137 — the arc lies in the component and inside the walk partial
unions (`walkAligned_arc_subset_walkUnion`)

For the exhaustion glue, the per-length arc datum of S133/S136 must be
known to live in the right sets: (1) in the COMPONENT — the whole arc is
inside `trace (ch 0)`, which lies in the connected component of its
centre class `cl (e 0)` (`OChartTrace_subset_component`, since the trace
is path-connected and contains its centre), so if the first walk class is
in `connectedComponent c₀` every arc class is; (2) in the WALK PARTIAL
UNION `⋃_{m < n+2} OChartTraceSet (cl (e m))` — the arc reaches exactly
the `(n+2)`-nd walk trace `cl (e (0+n+1))` (S133 clause (6)), and
`0+n+1 < n+2`.  These are the arc-side halves of `Eₙ ⊆ Uₙ ⊆ Uₙ₊₁`
(walk-union form). -/

/-- **The arc lies in the component and in the walk partial unions.**
From walk overlap data, an orbit `htr` through the first `n` junction
pieces, and the first walk class in the component of `c₀`, the S133 arc
datum can be chosen so that its classes all lie in the component of `c₀`
(the whole arc is inside `trace (ch 0)`, which lies in the component of
its centre `cl (e 0)`) and all lie in the walk partial union
`⋃_{m < n+2} OChartTraceSet (cl (e m))` (the arc reaches exactly the
`(n+2)`-nd walk trace). -/
theorem walkAligned_arc_subset_walkUnion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈ connectedComponent c₀) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) := by
  rcases walkAligned_covering_overlap h hqf hgp cl e hoverlap n x₀ htr with
    ⟨sub, hx₀mem, hinj, hcont, hanch, htrace0, htracefar⟩
  refine ⟨sub, hx₀mem, hinj, hcont, ?_, ?_⟩
  · intro x
    have hT : walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
        OChartTraceSet h hqf hgp (cl (e 0)) := by
      simpa [OChartTraceSet, chartTrace, walkChart] using htrace0 x
    exact OChartTrace_subset_component c₀ (cl (e 0)) hc0 hT
  · intro x
    have hT : walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
        OChartTraceSet h hqf hgp (cl (e (0 + n + 1))) := by
      simpa [OChartTraceSet, chartTrace, walkChart] using htracefar x
    exact Set.mem_iUnion₂.mpr ⟨0 + n + 1, Set.mem_Iio.mpr (by omega), hT⟩


/-! ## S138 — the per-length exhaustion arc datum
(`componentWalk_arcs_at_every_length`)

Composition of S136 + S137: given walk data whose classes all lie in the
component of `c₀` and a uniform landing hypothesis, every prefix length
carries the arc datum (injective, continuous, anchored at the orbit
class) inside the component and inside the walk partial union `P_{n+2}` —
the input package the interval-chain exhaustion builder (`Uₙ`, S107/S108)
consumes per length. -/

/-- **Per-length exhaustion arc datum.**  From walk overlap data with all
walk classes in the component of `c₀` and a uniform landing hypothesis,
every prefix length `n` carries datum data `sub` whose aligned start
interval contains the orbit parameter and whose arc map is injective,
continuous, anchored at the orbit class, contained in the component, and
contained in the walk partial union `⋃_{m < n+2} OChartTraceSet (cl (e
m))`.  (Composition of the all-lengths orbits (S136) with the
arc-in-component/partial-union theorem (S137).) -/
theorem componentWalk_arcs_at_every_length {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hcl : ∀ n : ℕ, cl n ∈ connectedComponent c₀)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
          (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
          chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∀ n : ℕ, ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
      ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
      Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap sub) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈ connectedComponent c₀) ∧
      (∀ x : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap sub x ∈
          ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) := by
  intro n
  exact walkAligned_arc_subset_walkUnion h hqf hgp cl e hoverlap c₀ (hcl (e 0)) n x₀
    (walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀ hland n)


/-! ## S140c (walk level) — aligned sub-data within a prescribed head
interval (`exists_walk_aligned_subdata_within`)

The S140b compatibility (`hI`) needs the alignment's head datum at length
`n+1` to lie INSIDE the length-`n` head datum.  The pure shrink
(`ChainAlignment.exists_subdata_landing_within`) intersects a landing
datum with the constraint interval; this theorem threads it through the
S127 backward induction: at every recursion level the head datum is
shrunk within the prescribed datum `J` (inner levels use the whole-
interval constraint `subDatum_refl`, so only the outermost head is
really constrained), yielding `Ioo d0 ⊆ Ioo J` together with the usual
`sub k = d0`, `x₀ ∈ d0`, and totality conjuncts.  The per-step nesting
"take the previous interval, shrink to the next length, record the
inclusion" is then the instantiation at `k = 0` with `J` := the previous
length's head datum (an orbit at the new length is the only additional
input). -/

/-- **Walk-prefix aligned sub-data within a prescribed head interval.**
The S127 `exists_walk_aligned_subdata` with the extra constraint that the
head datum's interval lies INSIDE a prescribed datum `J` of the start
piece (containing the orbit parameter): the backward induction threads
`J` into the final head shrink (`exists_subdata_landing_within`), and the
inner recursive calls use the whole-interval constraint
(`subDatum_refl`).  Consecutive lengths' head intervals can therefore be
nested by passing the previous length's head datum as `J`. -/
theorem exists_walk_aligned_subdata_within {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) :
    ∀ (k n : ℕ) (J : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap k)),
      ∀ (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap k).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap k).hi),
        ((x₀ : ℝ) ∈ Set.Ioo J.lo J.hi) →
        transports (walkJunctionPiece h hqf hgp cl e hoverlap k)
          (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) k n) x₀ →
        ∃ d0 : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap k),
        ∃ sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i),
          sub k = d0 ∧
          Set.Ioo d0.lo d0.hi ⊆ Set.Ioo J.lo J.hi ∧
          ((x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi) ∧
          (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
            transports (datumPiece d0)
              (chainTail (fun i => datumPiece (sub i)) k n) y) := by
  classical
  let w : ℕ → MonoPiece := walkJunctionPiece h hqf hgp cl e hoverlap
  have hcont : ∀ i, Continuous (w i).τ := fun i =>
    walkJunctionPiece_continuous h hqf hgp cl e hoverlap i
  intro k n
  revert k
  induction n with
  | zero =>
      intro k J x₀ hxJ htr
      let sub : (i : ℕ) → SubDatum (w i) := fun i =>
        if hik : i = k then
          Eq.mpr (congrArg (fun m : MonoPiece => SubDatum m) (congrArg w hik)) J
        else subDatum_refl (w i)
      refine ⟨J, sub, ?_, ?_, ?_, ?_⟩
      · simp [sub]
      · intro t ht
        exact ht
      · exact hxJ
      · intro y
        change transports (datumPiece J) ([] : List MonoPiece) y
        simp [transports]
  | succ n ih =>
      intro k J x₀ hxJ htr
      have hsplit : chainTail w k (n + 1) = w (k + 1) :: chainTail w (k + 1) n := by
        simp [chainTail]
      rw [hsplit] at htr
      rcases htr with ⟨h, htr'⟩
      let x₁ : ChartInterval (w (k + 1)).lo (w (k + 1)).hi := ⟨(w k).τ x₀, h⟩
      rcases ih (k + 1) (subDatum_refl (w (k + 1))) x₁ x₁.2 htr' with
        ⟨d0', sub', hsub'k1, hsubsetJ', hx₁mem, htot'⟩
      have hx1 : (w k).τ x₀ ∈ Set.Ioo (datumPiece d0').lo (datumPiece d0').hi := by
        change (w k).τ x₀ ∈ Set.Ioo d0'.lo d0'.hi
        simpa [x₁] using hx₁mem
      rcases exists_subdata_landing_within (w k) (datumPiece d0') (hcont k) x₀ hx1 J hxJ with
        ⟨d0, hx₀mem, hd0subJ, hland⟩
      let sub : (i : ℕ) → SubDatum (w i) := fun i =>
        if hik : i = k then
          Eq.mpr (congrArg (fun m : MonoPiece => SubDatum m) (congrArg w hik)) d0
        else sub' i
      have hsubk : sub k = d0 := by
        simp [sub]
      have hsubk1 : sub (k + 1) = sub' (k + 1) := by
        dsimp [sub]
        rw [dif_neg (by omega)]
      refine ⟨d0, sub, hsubk, hd0subJ, hx₀mem, ?_⟩
      intro y
      change transports (datumPiece d0) (datumPiece (sub (k + 1)) ::
          chainTail (fun i => datumPiece (sub i)) (k + 1) n) y
      have hmem : (datumPiece d0).τ y ∈ Set.Ioo (datumPiece (sub (k + 1))).lo
          (datumPiece (sub (k + 1))).hi := by
        rw [hsubk1, hsub'k1]
        exact hland y
      refine ⟨hmem, ?_⟩
      have hrest : chainTail (fun i => datumPiece (sub i)) (k + 1) n =
          chainTail (fun i => datumPiece (sub' i)) (k + 1) n := by
        apply chainTail_congr_right (k := k + 1) (n := n)
        intro i hi
        congr 1
        dsimp [sub]
        rw [dif_neg (by omega)]
      rw [hrest]
      have hpiece : datumPiece (sub (k + 1)) = datumPiece d0' := by
        rw [hsubk1, hsub'k1]
      have htrs : transports (datumPiece d0')
          (chainTail (fun i => datumPiece (sub' i)) (k + 1) n)
          ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) hpiece) ▸
            ⟨(datumPiece d0).τ y, hmem⟩) :=
        htot' ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) hpiece) ▸
          ⟨(datumPiece d0).τ y, hmem⟩)
      exact (transports_congr_piece (p := datumPiece (sub (k + 1))) (p' := datumPiece d0')
        (rest := chainTail (fun i => datumPiece (sub' i)) (k + 1) n) hpiece
          ⟨(datumPiece d0).τ y, hmem⟩).mpr htrs


end LeanEval.KnotTheory.Quadrisecant
