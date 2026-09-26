import Mathlib
import Submission.PerLengthCell

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S198 — the prefix-coordinate interlock of the per-length cell family
(module Submission/PrefixCoord.lean)

The S147-T chaining charts each prefix union `P'_k` by a monotone
transport coordinate started at the base chart (`ch 0`, H3) and extended
through the consecutive junctions (H1).  This module verifies the
coordinate interlock of the S195–S197 per-length cells in that base
coordinate — the H3 side in cell form:

1. **`perLengthCell_totality_prefix`** — the level-`n` forward totality
   restricted to the prefix chain of length `i ≤ n` (the reusable form
   of the prefix restriction used inside `perLengthCell_subset_trace`);
2. **`perLengthCell_prefix_coord`** — the prefix-coordinate
   IDENTIFICATION: for a head parameter `u` of the level-`n` datum and a
   prefix length `i ≤ n`, the cell class `walkAlignedArcMap …
   (subfam n) u` lies in the trace of chart `(0+i+1)` with the
   class-coordinate value conjunct kept: the real value of the
   chart-`(0+i+1)`-coordinate of the class equals the `i`-th chain value
   of the level-`n` datum chain started at `u` (the S119
   class-coordinate identification at the prefix, `i`-th value included);
3. **`perLengthCell_prefixCoord_monotone`** — the O1/O2 pivot in cell
   form: for every prefix length `i ≤ n`, the chain-value coordinate the
   level-`n` datum attaches to the `(0+i+1)`-th chart varies
   MONOTONICALLY (in one direction) in the head parameter `u`
   (the S111 `chain_transport_monotone_direction` pulled back along the
   totality embedding of the head interval into the chain domain) —
   along the level-`n` cell, the base (`ch 0`) order is preserved (or
   reversed) in every prefix trace the cell meets.

Together with S196 (`perLengthCell_subset_trace`), each level-`n` cell
is an interval-charted arc inside `⋂_{m ≤ n+1} T_m` whose base-coordinate
order matches its order in every one of those traces — the certified
coordinate refinement the S147-T traceUnion coordinate (once built by
the per-junction monotone transitions, S150 WI) must agree with on the
cells (F2-c/O1+O2).

Everything here is verified (no axioms, no `sorry`).
-/

/-- **Totality-prefix restriction of the per-length datum family.**  If
the level-`n` datum is forward-total through its `n`-tail chain
(`htot n`), then every head parameter also transports through the prefix
chain of length `i ≤ n` — the reusable form of the prefix restriction
used inside `perLengthCell_subset_trace`. -/
lemma perLengthCell_totality_prefix {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (htot : ∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
      transports (datumPiece (subfam n 0)) (chainTail (fun i => datumPiece (subfam n i)) 0 n) y)
    (n i : ℕ) (hi : i ≤ n)
    (y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) :
    transports (datumPiece (subfam n 0))
      (chainTail (fun j : ℕ => datumPiece (subfam n j)) 0 i) y := by
  exact transports_chainTail_prefix (p := fun j : ℕ => datumPiece (subfam n j)) 0 n i hi y
    (htot n y)

/-- **Prefix-coordinate identification of a cell class.**  For a head
parameter `u` of the level-`n` datum and a prefix length `i ≤ n`, the
cell class `walkAlignedArcMap … (subfam n) u` lies in the trace of
chart `(0+i+1)` with its coordinate VALUE identified: there is a
transition element `y` whose lift is the cell class and whose real value
is the `i`-th chain value of the level-`n` datum chain started at `u`
(the S119 class-coordinate identification at the prefix, `i`-th value
conjunct kept). -/
lemma perLengthCell_prefix_coord {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (htot : ∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
      transports (datumPiece (subfam n 0)) (chainTail (fun i => datumPiece (subfam n i)) 0 n) y)
    (n i : ℕ) (hi : i ≤ n)
    (u : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) :
    ∃ y : OChartTransitionDomain (walkChart h hqf hgp cl e (0 + i + 1))
        (walkChart h hqf hgp cl e 0),
      oChartLift (walkChart h hqf hgp cl e (0 + i + 1)) y.1 =
        walkAlignedArcMap h hqf hgp cl e hoverlap (subfam n) u ∧
      (y.1 : ℝ) = chainValue (datumPiece (subfam n 0) ::
          chainTail (fun j : ℕ => datumPiece (subfam n j)) 0 i)
          ⟨u, perLengthCell_totality_prefix h hqf hgp cl e hoverlap subfam htot n i hi u⟩ := by
  rcases chain_transport_class_coordinate (ch := walkChart h hqf hgp cl e)
      (p := fun j : ℕ => datumPiece (subfam n j))
      (hsub := fun j => datumPiece_chartSubset h hqf hgp cl e hoverlap j (subfam n j))
      (hsem := fun j v => datumPiece_semantics h hqf hgp cl e hoverlap j (subfam n j) v)
      0 i ⟨u, perLengthCell_totality_prefix h hqf hgp cl e hoverlap subfam htot n i hi u⟩ with
    ⟨y, hy⟩
  exact ⟨y, hy.1, hy.2⟩

/-- **The prefix chain value is monotone in the base (head) parameter
along the level-`n` cell** — the O1/O2 pivot in cell form (H3 side of
the sweep): for every prefix length `i ≤ n`, the real coordinate the
level-`n` datum chain attaches to the `(0+i+1)`-th chart varies
monotonically (in one direction) with the head parameter `u` — along the
cell, the base (`ch 0`) order is preserved (or reversed) in every prefix
trace the cell meets. -/
theorem perLengthCell_prefixCoord_monotone {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : (n : ℕ) → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (htot : ∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
      transports (datumPiece (subfam n 0)) (chainTail (fun i => datumPiece (subfam n i)) 0 n) y)
    (n i : ℕ) (hi : i ≤ n) :
    MonotoneDirectionOn
      (fun u : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi => (u : ℝ))
      (fun u : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi =>
        chainValue (datumPiece (subfam n 0) ::
            chainTail (fun j : ℕ => datumPiece (subfam n j)) 0 i)
          ⟨u, perLengthCell_totality_prefix h hqf hgp cl e hoverlap subfam htot n i hi u⟩) := by
  let p : ℕ → MonoPiece := fun j : ℕ => datumPiece (subfam n j)
  let ps : List MonoPiece := p 0 :: chainTail p 0 i
  let emb : ChartInterval (p 0).lo (p 0).hi → ChainDomain ps := fun u =>
    ⟨u, perLengthCell_totality_prefix h hqf hgp cl e hoverlap subfam htot n i hi u⟩
  have hmono : MonotoneDirectionOn (chainCoord ps) (chainValue ps) :=
    chain_transport_monotone_direction ps
  have hf : MonotoneDirectionOn
      (fun u : ChartInterval (p 0).lo (p 0).hi => (u : ℝ))
      (fun u : ChartInterval (p 0).lo (p 0).hi => chainCoord ps (emb u)) := by
    left
    intro a b hab
    change (a : ℝ) < (b : ℝ)
    exact hab
  have hgo := MonotoneDirectionOn.comp_of_coord
      (cD := fun u : ChartInterval (p 0).lo (p 0).hi => (u : ℝ))
      (cE := chainCoord ps) (f := emb) (g := chainValue ps) hf hmono
  change MonotoneDirectionOn
      (fun u : ChartInterval (p 0).lo (p 0).hi => (u : ℝ))
      (fun u : ChartInterval (p 0).lo (p 0).hi =>
        chainValue ps (emb u))
  simpa [ps, p] using hgo

end LeanEval.KnotTheory.Quadrisecant
