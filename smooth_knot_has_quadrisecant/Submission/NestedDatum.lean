import Mathlib
import Submission.PrefixArcChart
import Submission.AlignedCover

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S190 — the per-length nested datum family (assembly step (a) of the
`Uₙ` interval-chart construction; module Submission/NestedDatum.lean)

S189 pinned the consecutive-length contract: whenever two per-length
aligned datums NEST (`hI : (a′,b′) ⊆ (a,b)`), their cell charts reindex
by the real identity and are real-monotone.  This module starts the
assembly of the per-length NESTED datum family from the S140c machinery
(`exists_walk_aligned_subdata_within` — aligned sub-data within a
prescribed head interval containing the orbit parameter) and the S136
uniform-landing orbit (`walkOrbit_all_lengths`).

**The family statement (S190 target, to be assembled by recursion over
the lengths):**  under `hland`, there is a per-length family
`subfam : ℕ → (i : ℕ) → SubDatum (w i)` such that for every length `n`:
(1) `(x₀ : ℝ) ∈ Ioo (datumPiece (subfam n 0)).lo …` (each head contains
the orbit parameter); (2) the heads NEST:
`Ioo (datumPiece (subfam (n+1) 0)) ⊆ Ioo (datumPiece (subfam n 0))`
(the S189 `hI` at every consecutive pair); (3) per-length forward
totality: `∀ y ∈ datumPiece (subfam n 0)-interval, transports
(datumPiece (subfam n 0)) (chainTail (fun i => datumPiece (subfam n i))
0 n) y`.

Verified first obligations:

1. `WP` — the walk junction-piece family abbreviation
   (`walkJunctionPiece … i`);
2. **`perLength_base_datum`** — the level-0 datum: a sub-datum `d0` of
   the start piece with `x₀` in its interval — the S140c theorem at
   `(k = 0, n = 0)` with the whole-piece constraint
   `J := subDatum_refl (w 0)` (the vacuous transport at length 0);
3. **`perLength_step_datum`** — the nesting step: given the level-`n`
   head datum `J` (containing `x₀`), the uniform-landing orbit at length
   `n+1` feeds the S140c theorem at `(k = 0, n+1)` with the constraint
   `J`, producing the level-`(n+1)` datum `sub` with `sub 0 = d0`,
   `Ioo (datumPiece d0) ⊆ Ioo J` (the nesting `hI`), `x₀ ∈ d0`, and
   forward totality of every head parameter through the `(n+1)`-tail of
   `sub`.

The family `subfam` is the recursion `subfam 0 := base`, `subfam (n+1)
:= step n (subfam n 0)`; the three conjuncts follow from the base/step
specs by induction.  With the family in hand, the S189 reindexing lemmas
give the S140-T2 coordinate-compatible increasing family (`Uₙ := the
range of the length-`n` arc`, nested — hence, after the appropriate
index reading for the increasing exhaustion, interval-charted with
monotone change-of-chart).  Everything here is verified (no axioms, no
`sorry`).
-/
/-- shorthand for the walk junction pieces -/
abbrev WP {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (i : ℕ) : MonoPiece :=
  walkJunctionPiece h hqf hgp cl e hoverlap i

/-- **S190 (a) — base: the level-0 aligned datum.**  A sub-datum `d0` of
the start piece with head interval containing the orbit parameter `x₀`
and (vacuously) forward-totality at length 0 — the S140c theorem at
`(k = 0, n = 0)` with the whole-piece constraint. -/
lemma perLength_base_datum {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi) :
    ∃ d0 : SubDatum (WP h hqf hgp cl e hoverlap 0),
      (x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi := by
  let w : ℕ → MonoPiece := WP h hqf hgp cl e hoverlap
  have hxJ : (x₀ : ℝ) ∈ Set.Ioo (subDatum_refl (w 0)).lo (subDatum_refl (w 0)).hi := by
    change (x₀ : ℝ) ∈ Set.Ioo (w 0).lo (w 0).hi
    exact x₀.2
  have htr₀ : transports (w 0) (chainTail w 0 0) x₀ := by
    simp [w, transports, chainTail]
  rcases exists_walk_aligned_subdata_within h hqf hgp cl e hoverlap (k := 0) (n := 0)
      (subDatum_refl (w 0)) x₀ hxJ htr₀ with ⟨d0, sub, hsub0, hsubJ, hx₀mem, htot⟩
  exact ⟨d0, hx₀mem⟩

/-- **S190 (a) — step: from a level-`n` head datum to the level-`(n+1)`
datum with NESTED head.**  Given the level-`n` head datum `J` (a sub-
datum of the start piece containing `x₀`), the uniform landing orbit at
length `n+1` feeds the S140c theorem at `(k = 0, n+1)` with the
constraint `J`, producing a level-`(n+1)` datum `sub` whose head
`sub 0` lies INSIDE `J` (`Ioo (sub 0) ⊆ Ioo J` — the S189 nesting
`hI`), contains `x₀`, and whose every head parameter transports forward
through the `(n+1)`-tail of its own datum family. -/
lemma perLength_step_datum {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) (J : SubDatum (WP h hqf hgp cl e hoverlap 0))
    (hxJ : (x₀ : ℝ) ∈ Set.Ioo J.lo J.hi) :
    ∃ d0 : SubDatum (WP h hqf hgp cl e hoverlap 0),
    ∃ sub : (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i),
      sub 0 = d0 ∧
      Set.Ioo (datumPiece d0).lo (datumPiece d0).hi ⊆ Set.Ioo J.lo J.hi ∧
      (x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi ∧
      (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
        transports (datumPiece d0)
          (chainTail (fun i => datumPiece (sub i)) 0 (n + 1)) y) := by
  let w : ℕ → MonoPiece := WP h hqf hgp cl e hoverlap
  have htr : transports (w 0) (chainTail w 0 (n + 1)) x₀ := by
    simpa [w] using (walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀
      (by simpa [w] using hland) (n + 1))
  rcases exists_walk_aligned_subdata_within h hqf hgp cl e hoverlap (k := 0) (n := n + 1)
      J x₀ hxJ htr with ⟨d0, sub, hsub0, hsubJ, hx₀mem, htot⟩
  exact ⟨d0, sub, hsub0, hsubJ, hx₀mem, htot⟩


/-! ## S190b/S191 — the per-level datum family: bundle, recursion, and
the recursion-relation lemma

The base/step pair (`perLength_base_datum`, `perLength_step_datum`) is
the recursion backbone.  This section packages it: `PerLevelBundle` (the
per-level bundled type: sub-data function + `x₀` in its head + forward
totality through the level's tail), `datumInterval_of_pieceEq`, and the
recursion in EQUATION-COMPILER form (`perLevelBase` for level 0,
`perLevelStep` for level `(n+1)`, `perLevelData` by
`| 0 => base | n+1 => step n (perLevelData n)`) — so the
recursion-relation lemma **`perLevelData_succ`** holds by
`rw [perLevelData]`.  (S190b finding: a raw `Nat.rec` with a Type-valued
motive does NOT reduce definitionally on `Nat.succ`; the equation
compiler's generated recursion DOES — verified on a miniature dependent
def — and per level the outputs come via `Classical.choose`, since
`Exists`-elimination into `Type` is Prop-only.)  The family theorem
(`subfam n := (perLevelData n).1`, heads contain `x₀`, heads nest, per-
length totality) reads the bundle and `perLevelData_succ`; everything
here is verified (no axioms, no `sorry`).
-/

/-- the per-level datum bundle type -/
abbrev PerLevelBundle {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (x₀ : ChartInterval
        (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi) (n : ℕ) : Type :=
  { sub : (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i) //
    ((x₀ : ℝ) ∈ Set.Ioo (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi) ∧
    (∀ y : ChartInterval (datumPiece (sub 0)).lo (datumPiece (sub 0)).hi,
      transports (datumPiece (sub 0))
        (chainTail (fun i => datumPiece (sub i)) 0 n) y) }

/-- interval equality from piece equality -/
lemma datumInterval_of_pieceEq {p p' : MonoPiece} (heq : p = p') :
    Set.Ioo p.lo p.hi = Set.Ioo p'.lo p'.hi := by
  rw [heq]

/-- the level-0 per-level datum (S140c at `(k=0, n=0)`, whole-piece
constraint `J := subDatum_refl (w 0)`; level-0 totality vacuous) -/
noncomputable def perLevelBase {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi) :
    PerLevelBundle h hqf hgp cl e hoverlap x₀ 0 := by
  let w : ℕ → MonoPiece := WP h hqf hgp cl e hoverlap
  have hxJ : (x₀ : ℝ) ∈ Set.Ioo (subDatum_refl (w 0)).lo (subDatum_refl (w 0)).hi := by
    change (x₀ : ℝ) ∈ Set.Ioo (w 0).lo (w 0).hi
    exact x₀.2
  have htr₀ : transports (w 0) (chainTail w 0 0) x₀ := by
    simp [w, transports, chainTail]
  have hex := exists_walk_aligned_subdata_within h hqf hgp cl e hoverlap (k := 0) (n := 0)
      (subDatum_refl (w 0)) x₀ hxJ htr₀
  let d0 : SubDatum (WP h hqf hgp cl e hoverlap 0) := Classical.choose hex
  have hspec := Classical.choose_spec hex
  let sub : (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i) := Classical.choose hspec
  have hsubspec := Classical.choose_spec hspec
  have hsub0 : sub 0 = d0 := hsubspec.1
  have hx₀mem : (x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi := hsubspec.2.2.1
  exact ⟨sub, ⟨by
    have heq : datumPiece (sub 0) = datumPiece d0 := congrArg datumPiece hsub0
    rw [datumInterval_of_pieceEq heq]
    simpa [d0, datumPiece_lo, datumPiece_hi] using hx₀mem, by
    intro y
    simp [transports, chainTail]⟩⟩

/-- the level-(n+1) datum from a level-n datum (the nesting step) -/
noncomputable def perLevelStep {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) (ih : PerLevelBundle h hqf hgp cl e hoverlap x₀ n) :
    PerLevelBundle h hqf hgp cl e hoverlap x₀ (n + 1) := by
  let J : SubDatum (WP h hqf hgp cl e hoverlap 0) := ih.1 0
  have hxJ : (x₀ : ℝ) ∈ Set.Ioo J.lo J.hi := by
    dsimp [J]
    simpa [datumPiece_lo, datumPiece_hi] using ih.2.1
  have hex := perLength_step_datum h hqf hgp cl e hoverlap x₀ hland n J hxJ
  let d0 : SubDatum (WP h hqf hgp cl e hoverlap 0) := Classical.choose hex
  have hspec := Classical.choose_spec hex
  let sub' : (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i) := Classical.choose hspec
  have hsubspec := Classical.choose_spec hspec
  have hsub0 : sub' 0 = d0 := hsubspec.1
  have hnest : Set.Ioo (datumPiece d0).lo (datumPiece d0).hi ⊆ Set.Ioo J.lo J.hi := hsubspec.2.1
  have hx₀mem : (x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi := hsubspec.2.2.1
  have htot : ∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
      transports (datumPiece d0) (chainTail (fun i => datumPiece (sub' i)) 0 (n + 1)) y := hsubspec.2.2.2
  exact ⟨sub', ⟨by
    have heq : datumPiece (sub' 0) = datumPiece d0 := congrArg datumPiece hsub0
    rw [datumInterval_of_pieceEq heq]
    simpa [d0, datumPiece_lo, datumPiece_hi] using hx₀mem, by
    intro y
    have heq : datumPiece (sub' 0) = datumPiece d0 := congrArg datumPiece hsub0
    exact (transports_congr_piece (p := datumPiece (sub' 0)) (p' := datumPiece d0)
      (rest := chainTail (fun i => datumPiece (sub' i)) 0 (n + 1)) heq y).mpr
      (htot ((congrArg (fun m : MonoPiece => ChartInterval m.lo m.hi) heq) ▸ y))⟩⟩

/-- the per-level datum family (equation-compiler recursion) -/
noncomputable def perLevelData {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi) :
    (n : ℕ) → PerLevelBundle h hqf hgp cl e hoverlap x₀ n
  | 0 => perLevelBase h hqf hgp cl e hoverlap x₀
  | n + 1 => perLevelStep h hqf hgp cl e hoverlap x₀ hland n (perLevelData h hqf hgp cl e hoverlap x₀ hland n)

/-- **S191 — the recursion-relation lemma**: `perLevelData` at `n+1` is
the step applied to the level-`n` datum (holds by `rw [perLevelData]`,
the equation-compiler unfolding). -/
lemma perLevelData_succ {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    perLevelData h hqf hgp cl e hoverlap x₀ hland (n + 1) =
      perLevelStep h hqf hgp cl e hoverlap x₀ hland n
        (perLevelData h hqf hgp cl e hoverlap x₀ hland n) := by
  rw [perLevelData]



/-! ## S193 — the step spec and the per-length nested datum family

`perLevelStep_spec` exposes the step datum's internals as its interface
(the head `d0` with `(perLevelStep …).1 0 = d0`, the nesting
`Ioo (datumPiece d0) ⊆ Ioo (ih.1 0)` — the S189 `hI` against the
previous level's head — the head membership, and the totality through
the returned family's tail); it holds by `rw [perLevelStep]` (the
projection-extraction rework of S191 removed the stuck `And.casesOn`
from the step value, so `.1` reduces cleanly).  Then
**`perLength_nested_datum_family`** — the family theorem — reads
`subfam n := (perLevelData n).1` and proves the three conjuncts: heads
contain `x₀` (bundle projection), heads NEST across consecutive lengths
(`perLevelData_succ` moves from `subfam (n+1)` to `perLevelStep n
(subfam n)`; the spec supplies the head equality and the nesting), and
per-length forward totality (bundle projection).  Everything here is
verified (no axioms, no `sorry`).
-/
/-- **S193 — `perLevelStep_spec`**: the step datum exposes its head
`d0`, the nesting `Ioo (datumPiece d0) ⊆ Ioo (ih.1 0)` (the S189 `hI`
against the level-`n` head), the head membership, and the per-level
totality through the returned family's tail. -/
lemma perLevelStep_spec {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) (ih : PerLevelBundle h hqf hgp cl e hoverlap x₀ n) :
    let J : SubDatum (WP h hqf hgp cl e hoverlap 0) := ih.1 0
    ∃ d0 : SubDatum (WP h hqf hgp cl e hoverlap 0),
      (perLevelStep h hqf hgp cl e hoverlap x₀ hland n ih).1 0 = d0 ∧
      Set.Ioo (datumPiece d0).lo (datumPiece d0).hi ⊆ Set.Ioo J.lo J.hi ∧
      ((x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi) ∧
      (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
        transports (datumPiece d0)
          (chainTail (fun i => datumPiece ((perLevelStep h hqf hgp cl e hoverlap x₀ hland n ih).1 i))
            0 (n + 1)) y) := by
  classical
  intro J
  -- reproduce perLevelStep's internals with named terms
  have hxJ : (x₀ : ℝ) ∈ Set.Ioo J.lo J.hi := by
    dsimp [J]
    simpa [datumPiece_lo, datumPiece_hi] using ih.2.1
  let hex := perLength_step_datum h hqf hgp cl e hoverlap x₀ hland n J hxJ
  let d0 : SubDatum (WP h hqf hgp cl e hoverlap 0) := Classical.choose hex
  have hspec := Classical.choose_spec hex
  let sub' : (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i) := Classical.choose hspec
  have hsubspec := Classical.choose_spec hspec
  have hsub0 : sub' 0 = d0 := hsubspec.1
  have hnest : Set.Ioo (datumPiece d0).lo (datumPiece d0).hi ⊆ Set.Ioo J.lo J.hi := hsubspec.2.1
  have hx₀mem : (x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi := hsubspec.2.2.1
  have htot : ∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
      transports (datumPiece d0) (chainTail (fun i => datumPiece (sub' i)) 0 (n + 1)) y := hsubspec.2.2.2
  refine ⟨d0, ?_, hnest, hx₀mem, ?_⟩
  · -- (perLevelStep …).1 0 = d0
    rw [perLevelStep]
    exact hsub0
  · -- totality with the returned family's tail = tail of sub':
    intro y
    have htail : chainTail (fun i => datumPiece ((perLevelStep h hqf hgp cl e hoverlap x₀ hland n ih).1 i)) 0 (n + 1) =
        chainTail (fun i => datumPiece (sub' i)) 0 (n + 1) := by
      apply chainTail_congr_right
      intro i hi
      have hf : (perLevelStep h hqf hgp cl e hoverlap x₀ hland n ih).1 = sub' := by
        rw [perLevelStep]
      simp [hf]
    rw [htail]
    exact htot y

/-- **S193 — the per-length nested datum family** (all three conjuncts,
nesting via `perLevelData_succ` + `perLevelStep_spec`). -/
theorem perLength_nested_datum_family {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (WP h hqf hgp cl e hoverlap 0).lo (WP h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (WP h hqf hgp cl e hoverlap 0)
          (chainTail (WP h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (WP h hqf hgp cl e hoverlap 0 ::
          chainTail (WP h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (WP h hqf hgp cl e hoverlap (n + 1)).lo (WP h hqf hgp cl e hoverlap (n + 1)).hi) :
    ∃ subfam : ℕ → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i),
      (∀ n : ℕ,
        (x₀ : ℝ) ∈ Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) ∧
      (∀ n : ℕ,
        Set.Ioo (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi ⊆
          Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) ∧
      (∀ n : ℕ, ∀ y : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi,
        transports (datumPiece (subfam n 0))
          (chainTail (fun i => datumPiece (subfam n i)) 0 n) y) := by
  classical
  let subfam : ℕ → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i) :=
    fun n => (perLevelData h hqf hgp cl e hoverlap x₀ hland n).1
  refine ⟨subfam, ?_, ?_, ?_⟩
  · intro n
    exact (perLevelData h hqf hgp cl e hoverlap x₀ hland n).2.1
  · intro n
    rcases (perLevelStep_spec h hqf hgp cl e hoverlap x₀ hland n
        (perLevelData h hqf hgp cl e hoverlap x₀ hland n)) with ⟨d0, hd0, hnest, hx₀mem, htot⟩
    intro t ht
    have heq : datumPiece (subfam (n + 1) 0) = datumPiece d0 := by
      dsimp [subfam]
      rw [perLevelData_succ h hqf hgp cl e hoverlap x₀ hland n]
      exact congrArg datumPiece hd0
    have ht' : t ∈ Set.Ioo (datumPiece d0).lo (datumPiece d0).hi := by
      rw [← heq]
      exact ht
    have ht'' : t ∈ Set.Ioo (subfam n 0).lo (subfam n 0).hi := by
      -- hnest : Ioo (datumPiece d0) ⊆ Ioo ((perLevelData n).1 0).lo … (J := ih.1 0)
      exact hnest ht'
    simpa [subfam, datumPiece_lo, datumPiece_hi] using ht''
  · intro n y
    exact (perLevelData h hqf hgp cl e hoverlap x₀ hland n).2.2 y


/-! ## S194 — the per-length reindexing applied at each consecutive pair

With the per-length nested datum family in hand (S193), the S189
reindexing contract is instantiated at EVERY consecutive pair
`(subfam n, subfam (n+1))` using the nesting conjunct as the `hI`:
`perLength_reindex_identity` (the level-`(n+1)` arc chart reindexes into
the level-`n` chart by the real identity) and
`perLength_reindex_monotone` (`MonotoneDirectionOn` of the change of
chart with the inner coordinate).  These are the per-pair
coordinate-compatibility conjuncts of the S140-T2 increasing family, now
available for every `n` from `perLength_nested_datum_family`.  Everything
here is verified (no axioms, no `sorry`).
-/
/-- **S194 — per-length reindexing identity at a consecutive pair.**  For
a per-length datum family with nested heads (`hI n`), the change of chart
between the level-`(n+1)` arc chart and the level-`n` arc chart at an
inner-range class is the real identity reindexing — the S189
`walkAligned_changeChart_reindex_val` instantiated at the pair
`(subfam n, subfam (n+1))` with the nesting `hI n` (supplied by the
nesting conjunct (2) of `perLength_nested_datum_family`). -/
lemma perLength_reindex_identity {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : ℕ → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (hI : ∀ n : ℕ,
      Set.Ioo (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi ⊆
        Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi)
    (n : ℕ)
    (u : ChartInterval (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi) :
    (((walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap (subfam n)).symm
        ⟨walkAlignedArcMap h hqf hgp cl e hoverlap (subfam (n + 1)) u,
          walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap
            (subfam n) (subfam (n + 1)) (hI n) u⟩
        : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) : ℝ)
      = (u : ℝ) := by
  exact walkAligned_changeChart_reindex_val h hqf hgp cl e hoverlap
    (subfam n) (subfam (n + 1)) (hI n) u

/-- **S194 — per-length change of chart is real-monotone at a
consecutive pair** (the S189 `walkAligned_changeChart_monotone`
instantiated at `(subfam n, subfam (n+1))` with `hI n`): the two per-
length cell coordinates order the same classes identically on the nested
overlap. -/
lemma perLength_reindex_monotone {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (subfam : ℕ → (i : ℕ) → SubDatum (WP h hqf hgp cl e hoverlap i))
    (hI : ∀ n : ℕ,
      Set.Ioo (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi ⊆
        Set.Ioo (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi)
    (n : ℕ) :
    MonotoneDirectionOn
      (fun u : ChartInterval (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi => (u : ℝ))
      (fun u : ChartInterval (datumPiece (subfam (n + 1) 0)).lo (datumPiece (subfam (n + 1) 0)).hi =>
        (((walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap (subfam n)).symm
          ⟨walkAlignedArcMap h hqf hgp cl e hoverlap (subfam (n + 1)) u,
            walkAlignedArcMap_nested_range_mem h hqf hgp cl e hoverlap
              (subfam n) (subfam (n + 1)) (hI n) u⟩
          : ChartInterval (datumPiece (subfam n 0)).lo (datumPiece (subfam n 0)).hi) : ℝ)) := by
  exact walkAligned_changeChart_monotone h hqf hgp cl e hoverlap
    (subfam n) (subfam (n + 1)) (hI n)
end LeanEval.KnotTheory.Quadrisecant
