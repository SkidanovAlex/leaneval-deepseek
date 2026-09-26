import Mathlib
import Submission.PrefixArcChart
import Submission.Commons.Analysis.Order.ConnectedReal.injOn_continuousOn_monotoneOrAntitone

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

/-!
# Milestone-2 (iv) step 6, brick (b) — the nested per-length datum
family (S140e)

The S140d single-level arc package consumes datum data of the S140c
`exists_walk_aligned_subdata_within` shape; this module builds the
NESTED FAMILY of such data over all lengths — the concrete formal object
the T2 increasing-family assembly reads off.

Content (namespace LeanEval.KnotTheory.Quadrisecant):
1. **`NestedArcLevel`** — one level: the head datum `J` of the start
   piece containing the orbit parameter `x₀`, the full aligned datum
   `sub` (`sub 0 = J`) with forward totality through the `n`-tail chain
   of the datum family;
2. `nestedArcLevel_zero` — the length-`0` level (empty chain; the whole-
   interval head datum `subDatum_refl`; totality over `[]` is `True`);
3. **`nestedArcLevel_step`** — the recursion step: from a level of
   length `n` and an orbit at length `n+1`, the next level whose head
   datum lies INSIDE the previous head (`Ioo L'.J ⊆ Ioo L.J` — exactly
   the `hI` of the S140b change-of-chart), packaged as a subtype of
   levels together with the inclusion proof; built by
   `exists_walk_aligned_subdata_within` at `k = 0` with `J := L.J`
   (`Classical.choose` on the existential, the conjuncts re-read from
   the nested `choose_spec`);
4. **`nestedArcLevel_family`** — the per-length levels, by `Nat.rec`
   (`nestedArcLevel_zero` at `0`; at `m+1` the step with the S136
   all-lengths orbit at `m+1` from the uniform landing hypothesis);
5. **`nestedArcLevel_family_nested`** — the heads of consecutive levels
   nest: `Ioo (J (n+1)) ⊆ Ioo (J n)` for all `n` (unfold the recursion
   by `change` and read off the step's inclusion proof).

Each level `L n` then feeds the S140d `alignedData_arc_openSet` and
S140a `walkAlignedArcMap_homeo_range` (its head datum `J n` inside the
previous by `nestedArcLevel_family_nested` gives the `hI` of the S140b
`walkAligned_changeChart_of_nested` between consecutive levels) — the
per-length cells of the exhaustion, compatibly nested.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- One level of the nested per-length family: a head datum `J` of the
start piece containing the orbit parameter, the full aligned datum `sub`
(`sub 0 = J`) with forward totality through the `n`-tail chain of the
datum family (the `exists_walk_aligned_subdata_within` output shape). -/
structure NestedArcLevel {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi) (n : ℕ) where
  J : SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap 0)
  mem : (x₀ : ℝ) ∈ Set.Ioo J.lo J.hi
  sub : (i : ℕ) → SubDatum (walkJunctionPiece h hqf hgp cl e hoverlap i)
  head : sub 0 = J
  tot : ∀ y : ChartInterval (datumPiece J).lo (datumPiece J).hi,
    transports (datumPiece J)
      (chainTail (fun i => datumPiece (sub i)) 0 n) y

/-- The level of length `0` (empty chain; whole-interval head datum). -/
def nestedArcLevel_zero {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi) :
    NestedArcLevel h hqf hgp cl e hoverlap x₀ 0 := by
  refine ⟨subDatum_refl (walkJunctionPiece h hqf hgp cl e hoverlap 0), x₀.2,
    fun i => subDatum_refl (walkJunctionPiece h hqf hgp cl e hoverlap i), rfl, ?_⟩
  intro y
  change transports (datumPiece (subDatum_refl (walkJunctionPiece h hqf hgp cl e hoverlap 0)))
      ([] : List MonoPiece) y
  simp [transports]

/-- **The recursion step.**  From a level of length `n` and an orbit at
length `n+1`, the next level whose head datum lies INSIDE the previous
head (`Ioo L'.J ⊆ Ioo L.J` — the `hI` of S140b), built by
`exists_walk_aligned_subdata_within` at `k = 0` with `J := L.J`. -/
noncomputable def nestedArcLevel_step {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi) (n : ℕ)
    (L : NestedArcLevel h hqf hgp cl e hoverlap x₀ n)
    (or : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 (n + 1)) x₀) :
    {L' : NestedArcLevel h hqf hgp cl e hoverlap x₀ (n + 1) //
      Set.Ioo L'.J.lo L'.J.hi ⊆ Set.Ioo L.J.lo L.J.hi} := by
  classical
  let w : ℕ → MonoPiece := walkJunctionPiece h hqf hgp cl e hoverlap
  have hMain : ∃ d0 : SubDatum (w 0), ∃ sub : (i : ℕ) → SubDatum (w i),
      sub 0 = d0 ∧ Set.Ioo d0.lo d0.hi ⊆ Set.Ioo L.J.lo L.J.hi ∧
      ((x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi) ∧
      (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
        transports (datumPiece d0)
          (chainTail (fun i => datumPiece (sub i)) 0 (n + 1)) y) :=
    exists_walk_aligned_subdata_within h hqf hgp cl e hoverlap 0 (n + 1) L.J x₀ L.mem or
  let d0 : SubDatum (w 0) := Classical.choose hMain
  have hsub' : ∃ sub : (i : ℕ) → SubDatum (w i),
      sub 0 = d0 ∧ Set.Ioo d0.lo d0.hi ⊆ Set.Ioo L.J.lo L.J.hi ∧
      ((x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi) ∧
      (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
        transports (datumPiece d0)
          (chainTail (fun i => datumPiece (sub i)) 0 (n + 1)) y) :=
    Classical.choose_spec hMain
  let sub : (i : ℕ) → SubDatum (w i) := Classical.choose hsub'
  have hspec : sub 0 = d0 ∧ Set.Ioo d0.lo d0.hi ⊆ Set.Ioo L.J.lo L.J.hi ∧
      ((x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi) ∧
      (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
        transports (datumPiece d0)
          (chainTail (fun i => datumPiece (sub i)) 0 (n + 1)) y) :=
    Classical.choose_spec hsub'
  exact ⟨⟨d0, hspec.2.2.1, sub, hspec.1, hspec.2.2.2⟩, hspec.2.1⟩

/-- **The nested per-length family.**  Levels of every length with
consecutively nested head datums, built by recursion: level `0` is the
whole-interval head, level `n+1` shrinks level `n`'s head to the next
length using the all-lengths orbit at `n+1` (S136). -/
noncomputable def nestedArcLevel_family {r : ℝ → Space} (h : IsSmoothKnot r)
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
    (n : ℕ) → NestedArcLevel h hqf hgp cl e hoverlap x₀ n := fun n =>
  Nat.rec (nestedArcLevel_zero h hqf hgp cl e hoverlap x₀)
    (fun m (L : NestedArcLevel h hqf hgp cl e hoverlap x₀ m) =>
      (nestedArcLevel_step h hqf hgp cl e hoverlap x₀ m L
        (walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀ hland (m + 1))).1) n

/-- **The heads of consecutive levels nest.**  `Ioo (J (n+1)) ⊆ Ioo (J
n)` — the `hI` of the S140b compatibility for every consecutive pair. -/
lemma nestedArcLevel_family_nested {r : ℝ → Space} (h : IsSmoothKnot r)
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
    ∀ n : ℕ,
      Set.Ioo (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).J.lo
          (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).J.hi ⊆
        Set.Ioo (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J.lo
          (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J.hi := by
  intro n
  change Set.Ioo ((nestedArcLevel_step h hqf hgp cl e hoverlap x₀ n
      (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n)
      (walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀ hland (n + 1))).1.J).lo
      ((nestedArcLevel_step h hqf hgp cl e hoverlap x₀ n
      (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n)
      (walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀ hland (n + 1))).1.J).hi ⊆
      Set.Ioo (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J.lo
        (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J.hi
  exact (nestedArcLevel_step h hqf hgp cl e hoverlap x₀ n
    (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n)
    (walkOrbit_all_lengths h hqf hgp cl e hoverlap x₀ hland (n + 1))).2


/-! ## S141 — the per-level cell family read off the nested levels
(`nestedArcLevel_range`, `nestedArcLevel_range_open`,
`nestedArcLevel_cellChart`, `nestedArcLevel_range_subset`,
`nestedArcLevel_package`, and the head-subset helpers)

The T2 interval-charted sets are the open cells of the nested levels:
for each `n` the level-`n` cell is `nestedArcLevel_range n` — the range
of the level-`n` arc (open by S139, with the explicit S140a chart
`nestedArcLevel_cellChart n`) — and the head nesting
(`nestedArcLevel_datum_head_subset`, the datum-piece form of
`nestedArcLevel_family_nested`) gives the S140b inclusions of the cells
(`nestedArcLevel_range_subset`: cell `n+1` ⊆ cell `n`, with the
change-of-chart being the interval reindexing).  The component / E-side
clauses come from the S140d single-level package at the level
(`nestedArcLevel_package`: cell `n` ⊆ component, cell `n` ⊆ the walk
partial union `P'_{n+2}`, arc injective and continuous). -/



/-- The open cell of level `n`: the range of the level-`n` arc (classes
of the first chart's trace whose parameter lies in the level's head
datum interval). -/
def nestedArcLevel_range {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) : Set (OSub r) :=
  Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub))

/-- The level-`n` cell is open in `OSub r` (S139 range openness). -/
lemma nestedArcLevel_range_open {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) : IsOpen (nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n) := by
  dsimp [nestedArcLevel_range]
  rw [walkAlignedArcMap_range_eq_liftCell h hqf hgp cl e hoverlap
    ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub)]
  exact isOpen_lift_cell (walkChart h hqf hgp cl e 0)

/-- The S140a chart of the level-`n` cell. -/
noncomputable def nestedArcLevel_cellChart {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    ChartInterval (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi ≃ₜ
      {c : OSub r // c ∈ nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n} := by
  change ChartInterval (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi ≃ₜ
    {c : OSub r // c ∈ Set.range (walkAlignedArcMap h hqf hgp cl e hoverlap
      ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub))}
  exact walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap
    ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub)

/-- **The level cells nest (inclusion from the head nesting).**  The
level-`(n+1)` cell is contained in the level-`n` cell
(`nestedArcLevel_family_nested` supplies the `hI` of S140b). -/
lemma nestedArcLevel_range_subset {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland (n + 1) ⊆
      nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n := by
  intro c hc
  dsimp [nestedArcLevel_range] at hc ⊢
  rcases hc with ⟨u, rfl⟩
  refine ⟨⟨(u : ℝ), ?_⟩, ?_⟩
  · -- membership of u in the level-n head interval (u ∈ level-(n+1) head ⊆ level-n head)
    have hI : Set.Ioo (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub 0)).lo
          (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub 0)).hi ⊆
        Set.Ioo (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
          (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi := by
      have hh1 : ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub 0) =
          ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).J) :=
        (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).head
      have hh0 : ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0) =
          ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J) :=
        (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).head
      rw [hh1, hh0]
      rw [datumPiece_lo, datumPiece_hi, datumPiece_lo, datumPiece_hi]
      exact nestedArcLevel_family_nested h hqf hgp cl e hoverlap x₀ hland n
    exact hI u.2
  · exact (walkAlignedArcMap_eq_of_nested h hqf hgp cl e hoverlap
      ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub)
      ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub)
      (by
        have hh1 : ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub 0) =
            ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).J) :=
          (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).head
        have hh0 : ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0) =
            ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J) :=
          (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).head
        rw [hh1, hh0]
        rw [datumPiece_lo, datumPiece_hi, datumPiece_lo, datumPiece_hi]
        exact nestedArcLevel_family_nested h hqf hgp cl e hoverlap x₀ hland n) u).symm

/-- **Consecutive head datums nest (datum-piece form).**  The S140b `hI`
for the consecutive levels of the family: the level-`(n+1)` head piece
interval lies inside the level-`n` head piece interval (from
`nestedArcLevel_family_nested` through the level `head` equalities and
`datumPiece_lo/hi`). -/
lemma nestedArcLevel_datum_head_subset {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    Set.Ioo (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub 0)).hi ⊆
      Set.Ioo (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi := by
  rw [(nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).head,
    (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).head]
  rw [datumPiece_lo, datumPiece_hi, datumPiece_lo, datumPiece_hi]
  exact nestedArcLevel_family_nested h hqf hgp cl e hoverlap x₀ hland n

/-- The orbit parameter lies in the level-`n` head PIECE interval (the
datum-piece form of the level membership, through `head` and
`datumPiece_lo/hi`). -/
lemma nestedArcLevel_mem_sub0 {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    (x₀ : ℝ) ∈ Set.Ioo (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi := by
  rw [(nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).head]
  rw [datumPiece_lo, datumPiece_hi]
  exact (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).mem

/-- The level-`n` cell is contained in the component of `c₀` (and the
level-`n` arc has all the S140d package properties) — the S140d single-
level package instantiated at the level of the nested family. -/
lemma nestedArcLevel_package {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
          (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
          chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n ⊆ connectedComponent c₀ ∧
    nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n ⊆
      ⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m)) ∧
    Function.Injective (walkAlignedArcMap h hqf hgp cl e hoverlap
      ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub)) ∧
    Continuous (walkAlignedArcMap h hqf hgp cl e hoverlap
      ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub)) := by
  rcases alignedData_arc_openSet h hqf hgp cl e hoverlap c₀ hc0 n x₀
      (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J
      (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub
      (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).head
      (nestedArcLevel_mem_sub0 h hqf hgp cl e hoverlap x₀ hland n)
      (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).tot with
    ⟨hinj, hcont, hopen, hC, hP, hanchor⟩
  constructor
  · intro c hc
    rcases hc with ⟨u, rfl⟩
    exact hC u
  · constructor
    · intro c hc
      rcases hc with ⟨u, rfl⟩
      exact hP u
    · exact ⟨hinj, hcont⟩

/-! ## S142 — F1: the level cell lies in its exhaustion step
(`nestedArcLevel_cell_in_step`)

The first proof target of the T2 increasing-family assembly (ROADMAP
S142, statement F1): each level's cell is an interval-charted open
subset of the exhaustion step `P'_{n+2}` inside the component.  The two
conjuncts (`cell ⊆ C`, `cell ⊆ ⋃_{m < n+2} T_m`) are the S140d single-
level package at the level (`nestedArcLevel_package`); the interval-
chart of the cell inside the step is S141's `nestedArcLevel_cellChart` +
`nestedArcLevel_range_open`.  The increasing family itself (ROADMAP F2)
remains a design item (the cells nest by decreasing range — the
coordinate refinement of the walk partial unions, not the exhaustion
itself). -/

/-- **F1 — the E-side covering clause.**  Each level's cell is an
interval-charted open subset of the exhaustion step `P'_{n+2}` inside
the component: `cell n ⊆ P'_{n+2} ∩ C` (the two conjuncts of the S140d
single-level package at the level — `cell n ⊆ C` and
`cell n ⊆ ⋃_{m < n+2} T_m` — combined pointwise; the interval-chart of
the cell is S141's `nestedArcLevel_cellChart` + `range_open`). -/
lemma nestedArcLevel_cell_in_step {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
          (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
          chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n ⊆
      (⋃ m ∈ Set.Iio (n + 2), OChartTraceSet h hqf hgp (cl (e m))) ∩
        connectedComponent c₀ := by
  rcases nestedArcLevel_package h hqf hgp cl e hoverlap c₀ hc0 x₀ hland n with
    ⟨hC, hP, hinj, hcont⟩
  intro c hc
  constructor
  · exact hP hc
  · exact hC hc


/-! ## S143 — F2 set side: the walk partial union and the increasing
family `Uₙ := P'_{n+2}` (`walkPartialUnion`, `walkPartialUnion_mono`,
`nestedU_mono`, `nestedArcLevel_cell_in_U`)

Per the ROADMAP S143 statement block, the candidate increasing family is
`Uₙ := P'_{n+2}` with `P'_k` the walk partial union.  This section
verifies the SET side: the partial unions are increasing
(`walkPartialUnion_mono`, pure `Iio` arithmetic), hence
`Uₙ ⊆ Uₙ₊₁` (`nestedU_mono`), and the level-`n` cell lies inside
`Uₙ` (`nestedArcLevel_cell_in_U`, F1 projected onto the union) — the
cell-containment refinement, set side.  The CHARTED side (an
interval-charting of `Uₙ` by the monotone transport coordinate, with
the cells as its chart refinements) remains the open ordering design
content (ROADMAP S143, F2-b). -/

/-- The walk partial union `P'_k := ⋃ m ∈ Iio k, OChartTraceSet (cl (e
m))` — the candidate `Uₙ = P'_{n+2}` of the increasing family. -/
def walkPartialUnion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (k : ℕ) : Set (OSub r) :=
  ⋃ m ∈ Set.Iio k, OChartTraceSet h hqf hgp (cl (e m))

/-- The walk partial unions are increasing: `P'_k ⊆ P'_{k+1}` (pure
initial-segment arithmetic). -/
lemma walkPartialUnion_mono {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (k : ℕ) :
    walkPartialUnion h hqf hgp cl e k ⊆ walkPartialUnion h hqf hgp cl e (k + 1) := by
  intro c hc
  rcases Set.mem_iUnion₂.mp hc with ⟨m, hm, hcm⟩
  exact Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr (by
    have h : m < k := Set.mem_Iio.mp hm
    omega), hcm⟩

/-- The increasing family `Uₙ := P'_{n+2}`: `Uₙ ⊆ Uₙ₊₁` (the SET side of
F2-a, pure `walkPartialUnion_mono`). -/
lemma nestedU_mono {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (n : ℕ) :
    walkPartialUnion h hqf hgp cl e (n + 2) ⊆ walkPartialUnion h hqf hgp cl e (n + 3) := by
  exact walkPartialUnion_mono h hqf hgp cl e (n + 2)

/-- **The cell-containment refinement (F2-c, set side):** the level-`n`
cell lies in `Uₙ = P'_{n+2}` (F1 projected onto the union). -/
lemma nestedArcLevel_cell_in_U {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hc0 : cl (e 0) ∈ connectedComponent c₀)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (hland : ∀ (n : ℕ)
        (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
          (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀),
      chainValue (walkJunctionPiece h hqf hgp cl e hoverlap 0 ::
          chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) ⟨x₀, htr⟩ ∈
        Set.Ioo (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n : ℕ) :
    nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n ⊆
      walkPartialUnion h hqf hgp cl e (n + 2) := by
  intro c hc
  exact (nestedArcLevel_cell_in_step h hqf hgp cl e hoverlap c₀ hc0 x₀ hland n hc).1


/-! ## S144 — S2: the transitive compatibility of the nested family
(`nestedArcLevel_range_antitone`, `nestedArcLevel_head_antitone`)

The F2-b charting coordinate must be consistent over MULTIPLE levels:
the S140b change-of-chart is the interval reindexing between consecutive
cells, so the multi-level change-of-chart is the iterated reindexing.
This section proves the structural core: the cells and the head datums
are ANTITONE in the level — for `m ≤ n`, cell `n` ⊆ cell `m`
(`nestedArcLevel_range_antitone`, iterating the S141 consecutive
inclusion `nestedArcLevel_range_subset`) and
`Ioo (J n) ⊆ Ioo (J m)` (`nestedArcLevel_head_antitone`, iterating
`nestedArcLevel_family_nested`) — so the S140b `hI` for the
level-`n`-vs-level-`m` pair (any `m ≤ n`) is available, and the
multi-level reindexing is the composition of the consecutive ones. -/

/-- **The cells are antitone in the level:** for `m ≤ n` the level-`n`
cell lies in the level-`m` cell (iterating the S141 consecutive
inclusion `nestedArcLevel_range_subset`). -/
lemma nestedArcLevel_range_antitone {r : ℝ → Space} (h : IsSmoothKnot r)
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
    ∀ n : ℕ, ∀ m : ℕ, m ≤ n →
      nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland n ⊆
        nestedArcLevel_range h hqf hgp cl e hoverlap x₀ hland m := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst m
      exact Subset.rfl
  | succ n ih =>
      intro m hm
      rcases lt_or_eq_of_le hm with hmlt | hmeq
      · have hmle : m ≤ n := by omega
        exact Subset.trans
          (nestedArcLevel_range_subset h hqf hgp cl e hoverlap x₀ hland n)
          (ih m hmle)
      · subst m
        exact Subset.rfl

/-- **The head datums are antitone in the level:** for `m ≤ n` the
level-`n` head datum interval lies in the level-`m` head datum interval
(iterating `nestedArcLevel_family_nested`). -/
lemma nestedArcLevel_head_antitone {r : ℝ → Space} (h : IsSmoothKnot r)
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
    ∀ n : ℕ, ∀ m : ℕ, m ≤ n →
      Set.Ioo (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J.lo
          (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).J.hi ⊆
        Set.Ioo (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).J.lo
          (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).J.hi := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst m
      exact Subset.rfl
  | succ n ih =>
      intro m hm
      rcases lt_or_eq_of_le hm with hmlt | hmeq
      · have hmle : m ≤ n := by omega
        exact Subset.trans
          (nestedArcLevel_family_nested h hqf hgp cl e hoverlap x₀ hland n)
          (ih m hmle)
      · subst m
        exact Subset.rfl


/-! ## S145 — S1 verified + the multi-level coordinate agreement
(`nestedArcLevel_datum_head_subset_antitone`,
`nestedArcLevel_arc_eq_antitone`)

S1 of the S144 statement block — a continuous injective real map on an
open interval is strictly monotone in one direction — is ALREADY verified
in the commons: `OChartMonotone.interval_inj_continuous_monotone` (the
primitive) and `OChartAssemblyMonotone.monotoneOnPiece_of_inj_continuous`
(the `MonotoneOnPiece` wrap), already applied to the interval-piece
transition maps in `OChartGlue`; the transition pieces carry
monotonicity by construction (`nb.monotone`), and the chain transport
coordinates by S111 (`chain_transport_monotone_direction`/_injective).
No delegation was needed.

This section adds the multi-level coordinate agreement that S1-type
monotonicity + S144's antitone compatibility support: the datum-piece
form of the head nesting for ANY pair `m ≤ n`
(`nestedArcLevel_datum_head_subset_antitone`, the S140b `hI` for the
pair), and the ITERATED reindexing equality
(`nestedArcLevel_arc_eq_antitone`: a class of the level-`n` cell has the
SAME real parameter in the level-`m` cell — the level-`n` arc at `u`
equals the level-`m` arc at the reindexed parameter, by induction
composing the S140b consecutive reindexings) — the coordinate
consistency of the change-of-chart over multiple levels, which the F2-b
charting coordinate requires. -/

/-- The datum-piece form of the antitone head nesting: for `m ≤ n` the
level-`n` head piece interval lies in the level-`m` head piece interval
(the S140b `hI` for the pair). -/
lemma nestedArcLevel_datum_head_subset_antitone {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n m : ℕ) (hmn : m ≤ n) :
    Set.Ioo (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi ⊆
      Set.Ioo (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).sub 0)).hi := by
  rw [(nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).head,
    (nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).head]
  rw [datumPiece_lo, datumPiece_hi, datumPiece_lo, datumPiece_hi]
  exact nestedArcLevel_head_antitone h hqf hgp cl e hoverlap x₀ hland n m hmn

/-- **Multi-level coordinate agreement.**  For `m ≤ n`, a class of the
level-`n` cell has the SAME real parameter in the level-`m` cell: the
level-`n` arc at `u` equals the level-`m` arc at the reindexed
parameter — the iterated S140b reindexing (coordinate consistency of the
change-of-chart over multiple levels, the F2-b coordinate content). -/
lemma nestedArcLevel_arc_eq_antitone {r : ℝ → Space} (h : IsSmoothKnot r)
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
    ∀ n m : ℕ, ∀ (hmn : m ≤ n),
      ∀ u : ChartInterval (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
          (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi,
        walkAlignedArcMap h hqf hgp cl e hoverlap
            ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub) u =
          walkAlignedArcMap h hqf hgp cl e hoverlap
            ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).sub)
            ⟨(u : ℝ), nestedArcLevel_datum_head_subset_antitone h hqf hgp cl e hoverlap x₀ hland n m hmn u.2⟩ := by
  intro n
  induction n with
  | zero =>
      intro m hm u
      have hm0 : m = 0 := by omega
      subst m
      apply congrArg
      apply Subtype.ext
      rfl
  | succ n ih =>
      intro m hm u
      rcases lt_or_eq_of_le hm with hmlt | hmeq
      · have hmle : m ≤ n := by omega
        have hstep := walkAlignedArcMap_eq_of_nested h hqf hgp cl e hoverlap
          ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub)
          ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub)
          (nestedArcLevel_datum_head_subset h hqf hgp cl e hoverlap x₀ hland n) u
        let u' : ChartInterval (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
            (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi :=
          ⟨(u : ℝ), nestedArcLevel_datum_head_subset h hqf hgp cl e hoverlap x₀ hland n u.2⟩
        have hIH := ih m hmle u'
        calc
          walkAlignedArcMap h hqf hgp cl e hoverlap
              ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland (n + 1)).sub) u
              = walkAlignedArcMap h hqf hgp cl e hoverlap
                  ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub) u' := hstep
          _ = walkAlignedArcMap h hqf hgp cl e hoverlap
                  ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).sub)
                  ⟨(u' : ℝ), nestedArcLevel_datum_head_subset_antitone h hqf hgp cl e hoverlap x₀ hland n m hmle u'.2⟩ := hIH
          _ = walkAlignedArcMap h hqf hgp cl e hoverlap
                  ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).sub)
                  ⟨(u : ℝ), nestedArcLevel_datum_head_subset_antitone h hqf hgp cl e hoverlap x₀ hland (n + 1) m hm u.2⟩ := by
                apply congrArg
                apply Subtype.ext
                rfl
      · subst m
        apply congrArg
        apply Subtype.ext
        rfl


/-! ## S146 — the ordering pivot: the general change-of-chart triangle
(`nestedArcLevel_changeChart_antitone`)

The interval-charting of `Uₙ = P'_{n+2}` (F2-b) pivots on the ordering
fact (ROADMAP S146, form O2): the change-of-chart between ANY two levels
of the nested family is the interval reindexing.  This lemma is the
instantiation of the S140b `walkAligned_changeChart_of_nested` at the
pair `(m, n)` (`m ≤ n`) with `hI` the antitone head nesting
(`nestedArcLevel_datum_head_subset_antitone`): pulling the level-`m`
cell chart back over the level-`n` cell gives the reindexing.  Together
with the arc-value form O1 (`nestedArcLevel_arc_eq_antitone`, S145) the
family of cell charts is ORDER-CONSISTENT — any two levels read the same
real coordinate for a common class up to the identity-on-reals
reindexing; the remaining (open) content of the charting is the SWEEP of
`P'_{n+2}` by cells (classes away from the orbit class need cells
anchored along the walk — the S106-flagged ordering core, recorded in
the ROADMAP, not attempted here). -/

/-- **O2 — the general change-of-chart triangle (the ordering pivot).**
For `m ≤ n`, the level-`m` cell chart `φₘ` pulled back over the level-`n`
cell is the interval reindexing: `φₘ.symm ⟨arcₙ u, range-membership⟩ =
⟨(u : ℝ), hI u.2⟩` with `hI` the antitone head nesting — the S140b
`walkAligned_changeChart_of_nested` instantiated at the pair `(m,n)`. -/
lemma nestedArcLevel_changeChart_antitone {r : ℝ → Space} (h : IsSmoothKnot r)
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
          (walkJunctionPiece h hqf hgp cl e hoverlap (n + 1)).hi)
    (n m : ℕ) (hmn : m ≤ n)
    (u : ChartInterval (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).lo
        (datumPiece ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub 0)).hi) :
    (walkAlignedArcMap_homeo_range h hqf hgp cl e hoverlap
        ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).sub)).symm
      ⟨walkAlignedArcMap h hqf hgp cl e hoverlap
          ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub) u,
        (nestedArcLevel_range_antitone h hqf hgp cl e hoverlap x₀ hland n m hmn)
          (Set.mem_range_self u)⟩ =
      ⟨(u : ℝ), nestedArcLevel_datum_head_subset_antitone h hqf hgp cl e hoverlap x₀ hland n m hmn u.2⟩ := by
  exact walkAligned_changeChart_of_nested h hqf hgp cl e hoverlap
    ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland m).sub)
    ((nestedArcLevel_family h hqf hgp cl e hoverlap x₀ hland n).sub)
    (nestedArcLevel_datum_head_subset_antitone h hqf hgp cl e hoverlap x₀ hland n m hmn) u


/-! ## S148 — the subtype wrap of L29 (W)
(`monotone_or_antitone_on_connected_open`)

The H1 transition fact of the S147-T charting needs the monotone-order
statement on connected OPEN subsets of the chart-interval type (sets,
not whole intervals): L29 gives it for connected open sets of ℝ; the
wrap `monotone_or_antitone_on_connected_open` transports it to real-
valued maps `g : ChartInterval lo hi → ℝ` on connected open sets `C` of
the chart type, by ambientizing `C` to its real-coordinate image
(open in ℝ — the coordinate projection of the open subtype `Ioo lo hi`
is an open map; preconnected — the continuous image of `C`) and applying
L29 to the coordinate function.  The overlap-component transition lemma
(T of the S148 ROADMAP block) instantiates W next. -/

private def realImage {lo hi : ℝ} (C : Set (ChartInterval lo hi)) : Set ℝ :=
  {x : ℝ | x ∈ Set.Ioo lo hi ∧ ∀ _hx : x ∈ Set.Ioo lo hi, (⟨x, _hx⟩ : ChartInterval lo hi) ∈ C}

/-- The coordinate image of a chart-interval subset equals its real-image
set (the coordinate map is injective on the subtype). -/
private lemma realImage_eq_coord_image {lo hi : ℝ} (C : Set (ChartInterval lo hi)) :
    realImage C = (fun t : ChartInterval lo hi => (t : ℝ)) '' C := by
  ext x
  constructor
  · rintro ⟨hxIoo, hxC⟩
    refine ⟨⟨x, hxIoo⟩, hxC hxIoo, rfl⟩
  · rintro ⟨t, htC, htx⟩
    refine ⟨?_, ?_⟩
    · rw [← htx]
      exact t.2
    · intro hxIoo
      have heq : (⟨x, hxIoo⟩ : ChartInterval lo hi) = t := by
        apply Subtype.ext
        exact htx.symm
      rw [heq]
      exact htC

/-- The real image of an open set of the chart-interval type is open in
ℝ (the coordinate map is the projection of the open subtype
`Ioo lo hi`, hence an open map). -/
private lemma isOpen_realImage {lo hi : ℝ} {C : Set (ChartInterval lo hi)} (hC : IsOpen C) :
    IsOpen (realImage C) := by
  rw [realImage_eq_coord_image]
  have hval : IsOpenMap (fun t : ChartInterval lo hi => (t : ℝ)) := by
    exact (isOpen_Ioo (α := ℝ) (a := lo) (b := hi)).isOpenMap_subtype_val
  exact hval C hC

/-- The real image of a preconnected set of the chart-interval type is
preconnected (continuous image of a preconnected set). -/
private lemma isPreconnected_realImage {lo hi : ℝ} {C : Set (ChartInterval lo hi)}
    (hC : IsPreconnected C) : IsPreconnected (realImage C) := by
  rw [realImage_eq_coord_image]
  exact hC.image (fun t : ChartInterval lo hi => (t : ℝ))
    (continuous_subtype_val.continuousOn)

/-- **The subtype wrap of L29.**  A continuous injective real-valued map
`g` on a connected open set `C` of a chart-interval type is strictly
monotone in one direction on `C` (order of the real coordinates). -/
lemma monotone_or_antitone_on_connected_open {lo hi : ℝ} (g : ChartInterval lo hi → ℝ)
    {C : Set (ChartInterval lo hi)} (hCopen : IsOpen C) (hCconn : IsPreconnected C)
    (hcont : ContinuousOn g C) (hinj : Set.InjOn g C) :
    (∀ ⦃a b : ChartInterval lo hi⦄, a ∈ C → b ∈ C → (a : ℝ) < (b : ℝ) → g a < g b) ∨
    (∀ ⦃a b : ChartInterval lo hi⦄, a ∈ C → b ∈ C → (a : ℝ) < (b : ℝ) → g b < g a) := by
  let s : Set ℝ := realImage C
  let f : ℝ → ℝ := fun x => if hx : x ∈ Set.Ioo lo hi then g ⟨x, hx⟩ else 0
  have hsopen : IsOpen s := by
    dsimp [s]
    exact isOpen_realImage hCopen
  have hsconn : IsPreconnected s := by
    dsimp [s]
    exact isPreconnected_realImage hCconn
  have hcontf : ContinuousOn f s := by
    rw [continuousOn_iff_continuous_domRestrict]
    let e : s → ChartInterval lo hi := fun x => ⟨(x : ℝ), x.2.1⟩
    have he : Continuous e :=
      Continuous.subtype_mk continuous_subtype_val (fun x => x.2.1)
    have hem : ∀ x : s, e x ∈ C := by
      intro x
      exact x.2.2 x.2.1
    have hge : Continuous (fun x : s => g (e x)) :=
      ContinuousOn.comp_continuous hcont he hem
    have hEq : (fun x : s => g (e x)) = s.domRestrict f := by
      funext x
      dsimp [e, f]
      simp [x.2.1]
    rwa [← hEq]

  have hinjf : Set.InjOn f s := by
    intro x hx y hy hxy
    -- f x = g ⟨x,hx⟩ and f y = g ⟨y,hy⟩, memberships from hx.2/hy.2
    have hxIoo : x ∈ Set.Ioo lo hi := hx.1
    have hyIoo : y ∈ Set.Ioo lo hi := hy.1
    have hxC : (⟨x, hxIoo⟩ : ChartInterval lo hi) ∈ C := hx.2 hxIoo
    have hyC : (⟨y, hyIoo⟩ : ChartInterval lo hi) ∈ C := hy.2 hyIoo
    have hfx : f x = g ⟨x, hxIoo⟩ := by
      dsimp [f]
      rw [dif_pos hxIoo]
    have hfy : f y = g ⟨y, hyIoo⟩ := by
      dsimp [f]
      rw [dif_pos hyIoo]
    have hg : g ⟨x, hxIoo⟩ = g ⟨y, hyIoo⟩ := by
      rw [← hfx, ← hfy]
      exact hxy
    have hxy' : (⟨x, hxIoo⟩ : ChartInterval lo hi) = ⟨y, hyIoo⟩ := by
      exact hinj hxC hyC hg
    exact congrArg (fun t : ChartInterval lo hi => (t : ℝ)) hxy'
  rcases Commons.Analysis.Order.ConnectedReal.injOn_continuousOn_monotoneOrAntitone
      hsopen hsconn hcontf hinjf with hinc | hdec
  · left
    intro a b haC hbC hab
    have haR : (a : ℝ) ∈ s := by
      dsimp [s, realImage]
      exact ⟨a.2, fun _ => haC⟩
    have hbR : (b : ℝ) ∈ s := by
      dsimp [s, realImage]
      exact ⟨b.2, fun _ => hbC⟩
    have hga : g a = f (a : ℝ) := by
      dsimp [f]
      rw [dif_pos a.2]
    have hgb : g b = f (b : ℝ) := by
      dsimp [f]
      rw [dif_pos b.2]
    rw [hga, hgb]
    exact hinc haR hbR hab
  · right
    intro a b haC hbC hab
    have haR : (a : ℝ) ∈ s := by
      dsimp [s, realImage]
      exact ⟨a.2, fun _ => haC⟩
    have hbR : (b : ℝ) ∈ s := by
      dsimp [s, realImage]
      exact ⟨b.2, fun _ => hbC⟩
    have hga : g a = f (a : ℝ) := by
      dsimp [f]
      rw [dif_pos a.2]
    have hgb : g b = f (b : ℝ) := by
      dsimp [f]
      rw [dif_pos b.2]
    rw [hgb, hga]
    exact hdec haR hbR hab

/-! ## S149 — T: the overlap-component transition lemma
(`transition_monotone_on_connected_open`)

The H1 fact of the S147-T chaining, in parametric form: for two interval
charts `ch₁ ch₂` and a connected open set `C` of the `ch₁`-interval all
of whose classes lie in `ch₂`'s trace, the `ch₂`-coordinate of the class
is strictly monotone-or-antitone in the `ch₁`-coordinate on `C`.  The
relabelling is the S98 `oChartTransitionReal ch₁ ch₂` (continuous and
injective on the whole transition domain — verified in OChartGlue); it
is extended to a total map `g` on the `ch₁`-interval (0 off the
transition domain), which on `C` agrees with `oChartTransitionReal ∘
pack` (`pack : C → OChartTransitionDomain ch₁ ch₂` continuous), so `g`
is ContinuousOn and Set.InjOn `C` and the W wrap
(`monotone_or_antitone_on_connected_open`, S148) applies.  The walk
instance (`ch₁ := walkChart … m`, `ch₂ := walkChart … (m+1)`, `C` the
connected component containing the ch₁-coordinate of
`walkOverlapClass m`) is the next step. -/

/-- **T — the transition relabelling is monotone-or-antitone on a
connected open part of the transition domain.**  For two interval charts
`ch₁ ch₂` and a connected open set `C` of the `ch₁`-interval whose
classes all lie in `ch₂`'s trace, the `ch₂`-coordinate of the class is
strictly monotone or antitone in the `ch₁`-coordinate on `C` (the H1
fact of the S147-T chaining; via the W wrap applied to the relabelling,
which is continuous and injective on the transition domain). -/
theorem transition_monotone_on_connected_open {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    {C : Set (ChartInterval ch₁.lo ch₁.hi)}
    (hCopen : IsOpen C) (hCconn : IsPreconnected C)
    (hCsub : C ⊆ {x : ChartInterval ch₁.lo ch₁.hi |
      (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W}) :
    (∀ ⦃a b : ChartInterval ch₁.lo ch₁.hi⦄, (ha : a ∈ C) → (hb : b ∈ C) →
        (a : ℝ) < (b : ℝ) →
        oChartTransitionReal ch₁ ch₂ ⟨a, hCsub ha⟩ <
        oChartTransitionReal ch₁ ch₂ ⟨b, hCsub hb⟩) ∨
    (∀ ⦃a b : ChartInterval ch₁.lo ch₁.hi⦄, (ha : a ∈ C) → (hb : b ∈ C) →
        (a : ℝ) < (b : ℝ) →
        oChartTransitionReal ch₁ ch₂ ⟨b, hCsub hb⟩ <
        oChartTransitionReal ch₁ ch₂ ⟨a, hCsub ha⟩) := by
  classical
  let g : ChartInterval ch₁.lo ch₁.hi → ℝ := fun t =>
    if ht : (oChartLift ch₁ t : OpenMobius) ∈ ch₂.W then
      oChartTransitionReal ch₁ ch₂ ⟨t, ht⟩ else 0
  have hmemD : ∀ t : ChartInterval ch₁.lo ch₁.hi, t ∈ C →
      (oChartLift ch₁ t : OpenMobius) ∈ ch₂.W := by
    intro t ht
    exact hCsub ht
  let pack : C → OChartTransitionDomain ch₁ ch₂ := fun x =>
    ⟨x.1, hmemD x.1 x.2⟩
  have hpack : Continuous pack :=
    Continuous.subtype_mk continuous_subtype_val (fun x => hmemD x.1 x.2)
  have hge : ∀ x : C, g (x : ChartInterval ch₁.lo ch₁.hi) =
      oChartTransitionReal ch₁ ch₂ (pack x) := by
    intro x
    dsimp [g, pack]
    rw [dif_pos (hmemD x.1 x.2)]
  have hcontg : ContinuousOn g C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hge' : C.domRestrict g = fun x : C => oChartTransitionReal ch₁ ch₂ (pack x) := by
      funext x
      exact hge x
    rw [hge']
    exact (continuous_oChartTransitionReal ch₁ ch₂).comp hpack
  have hinjg : Set.InjOn g C := by
    intro a ha b hb hgab
    have hinjR := injective_oChartTransitionReal ch₁ ch₂
    have haE : g a = oChartTransitionReal ch₁ ch₂ ⟨a, hmemD a ha⟩ := by
      dsimp [g]
      rw [dif_pos (hmemD a ha)]
    have hbE : g b = oChartTransitionReal ch₁ ch₂ ⟨b, hmemD b hb⟩ := by
      dsimp [g]
      rw [dif_pos (hmemD b hb)]
    have hR : oChartTransitionReal ch₁ ch₂ ⟨a, hmemD a ha⟩ =
        oChartTransitionReal ch₁ ch₂ ⟨b, hmemD b hb⟩ := by
      rw [← haE, ← hbE]
      exact hgab
    have ht := hinjR hR
    have hval := congrArg (fun w : OChartTransitionDomain ch₁ ch₂ =>
      (w.1 : ChartInterval ch₁.lo ch₁.hi)) ht
    simpa using hval
  rcases monotone_or_antitone_on_connected_open g hCopen hCconn hcontg hinjg with hinc | hdec
  · left
    intro a b haC hbC hab
    have hga : g a = oChartTransitionReal ch₁ ch₂ ⟨a, hmemD a haC⟩ := by
      dsimp [g]
      rw [dif_pos (hmemD a haC)]
    have hgb : g b = oChartTransitionReal ch₁ ch₂ ⟨b, hmemD b hbC⟩ := by
      dsimp [g]
      rw [dif_pos (hmemD b hbC)]
    rw [← hga, ← hgb]
    exact hinc haC hbC hab
  · right
    intro a b haC hbC hab
    have hga : g a = oChartTransitionReal ch₁ ch₂ ⟨a, hmemD a haC⟩ := by
      dsimp [g]
      rw [dif_pos (hmemD a haC)]
    have hgb : g b = oChartTransitionReal ch₁ ch₂ ⟨b, hmemD b hbC⟩ := by
      dsimp [g]
      rw [dif_pos (hmemD b hbC)]
    rw [← hgb, ← hga]
    exact hdec haC hbC hab


/-! ## S150 — CO: the component of a transition-domain parameter is open
(`isOpen_connectedComponentIn_transitionDomain`)

The only genuinely new local fact needed by the walk instance of T (WI):
the connected component of a transition-domain parameter `t₀` inside
`D := {x | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W}` is open in the
chart-interval type.  Proof: for `y` in the component, take `ε` from the
metric-ball-in-`D` membership; the capped open interval neighbourhood
`V := val ⁻¹' Ioo (max ch₁.lo (y.1−ε)) (min ch₁.hi (y.1+ε))` of `y` is
open (preimage of an open real interval), preconnected
(`IsPreconnected.preimage_of_isOpenMap` with the coordinate map
injective/open, the cap keeping `Ioo A B ⊆ Ioo ch₁.lo ch₁.hi` inside the
coordinate range), contained in the metric ball (the cap bounds `A ≥
y.1−ε`, `B ≤ y.1+ε` + plain-real `abs_lt.mpr`), hence in `D`; a
preconnected set inside `D` through `y` lies in the component of `y`,
which equals the component of `t₀` (`connectedComponentIn_eq hy`,
`symm`) — so every point of the component is interior.  This is CO of
the S150 statement block; WI (the walk instance with `ch m`/`ch (m+1)`
and `walkOverlapClass m`) consumes it next. -/

lemma isOpen_connectedComponentIn_transitionDomain {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (t₀ : OChartTransitionDomain ch₁ ch₂) :
    IsOpen (connectedComponentIn
      {x : ChartInterval ch₁.lo ch₁.hi | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W} t₀.1) := by
  classical
  let D : Set (ChartInterval ch₁.lo ch₁.hi) :=
    {x | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W}
  have hDopen : IsOpen D := by
    dsimp [D]
    exact isOpen_oChartTransitionDomain ch₁ ch₂
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyD : y ∈ D := connectedComponentIn_subset D t₀.1 hy
  have hDnhd : D ∈ 𝓝 y := hDopen.mem_nhds hyD
  rcases Metric.mem_nhds_iff.mp hDnhd with ⟨ε, hεpos, hball⟩
  let A : ℝ := max ch₁.lo (y.1 - ε)
  let B : ℝ := min ch₁.hi (y.1 + ε)
  let V : Set (ChartInterval ch₁.lo ch₁.hi) :=
    (fun t : ChartInterval ch₁.lo ch₁.hi => t.1) ⁻¹' Set.Ioo A B
  have hylt : ch₁.lo < y.1 := y.2.1
  have hylthi : y.1 < ch₁.hi := y.2.2
  have hVy : y ∈ V := by
    dsimp [V, A, B]
    change max ch₁.lo (y.1 - ε) < y.1 ∧ y.1 < min ch₁.hi (y.1 + ε)
    constructor
    · rw [max_lt_iff]
      constructor <;> linarith
    · rw [lt_min_iff]
      constructor <;> linarith
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hVpre : IsPreconnected V := by
    dsimp [V]
    apply IsPreconnected.preimage_of_isOpenMap
    · exact isPreconnected_Ioo
    · exact Subtype.val_injective
    · exact (isOpen_Ioo (α := ℝ) (a := ch₁.lo) (b := ch₁.hi)).isOpenMap_subtype_val
    · intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hVsubBall : V ⊆ Metric.ball y ε := by
    intro t ht
    have hyloT : y.1 - ε < t.1 := lt_of_le_of_lt (le_max_right ch₁.lo (y.1 - ε)) ht.1
    have htly : t.1 < y.1 + ε := lt_of_lt_of_le ht.2 (min_le_right ch₁.hi (y.1 + ε))
    rw [Metric.mem_ball]
    change dist t.1 y.1 < ε
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith
  have hVsubD : V ⊆ D := by
    intro t ht
    exact hball (hVsubBall ht)
  have hsubY : V ⊆ connectedComponentIn D y := by
    exact hVpre.subset_connectedComponentIn hVy hVsubD
  have hsubT : V ⊆ connectedComponentIn D t₀.1 := by
    calc
      V ⊆ connectedComponentIn D y := hsubY
      _ = connectedComponentIn D t₀.1 := (connectedComponentIn_eq hy).symm
  exact Filter.mem_of_superset (hVopen.mem_nhds hVy) hsubT

/-! ## S150 — WI: the walk instance of the ordered transition

**WI — the overlap-component transition at a walk junction.**  For the
walk junction `m`, on the connected component of the transition domain
containing the `ch m`-coordinate of the walk overlap class, the
`ch (m+1)`-coordinate relabelling is strictly monotone-or-antitone in
the `ch m`-coordinate — the H1 ordered transition of the S147-T
chaining (instance of `transition_monotone_on_connected_open` with
`ch₁ := walkChart m`, `ch₂ := walkChart (m+1)`, and `C` the connected
component of `t₀`, the coordinate of `walkOverlapClass m`). -/

theorem walk_junction_transition_monotone {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (m : ℕ) :
    let ch₁ := walkChart h hqf hgp cl e m
    let ch₂ := walkChart h hqf hgp cl e (m + 1)
    let t₀ : OChartTransitionDomain ch₁ ch₂ :=
      oChartTraceOverlapParam ch₁ ch₂ (walkOverlapClass h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_left h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_right h hqf hgp cl e hoverlap m)
    let D : Set (ChartInterval ch₁.lo ch₁.hi) :=
      {x | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W}
    (∀ ⦃a b : ChartInterval ch₁.lo ch₁.hi⦄,
        (ha : a ∈ connectedComponentIn D t₀.1) →
        (hb : b ∈ connectedComponentIn D t₀.1) → (a : ℝ) < (b : ℝ) →
        oChartTransitionReal ch₁ ch₂ ⟨a, connectedComponentIn_subset D t₀.1 ha⟩ <
        oChartTransitionReal ch₁ ch₂ ⟨b, connectedComponentIn_subset D t₀.1 hb⟩) ∨
    (∀ ⦃a b : ChartInterval ch₁.lo ch₁.hi⦄,
        (ha : a ∈ connectedComponentIn D t₀.1) →
        (hb : b ∈ connectedComponentIn D t₀.1) → (a : ℝ) < (b : ℝ) →
        oChartTransitionReal ch₁ ch₂ ⟨b, connectedComponentIn_subset D t₀.1 hb⟩ <
        oChartTransitionReal ch₁ ch₂ ⟨a, connectedComponentIn_subset D t₀.1 ha⟩) := by
  classical
  dsimp
  exact transition_monotone_on_connected_open
    (walkChart h hqf hgp cl e m) (walkChart h hqf hgp cl e (m + 1))
    (isOpen_connectedComponentIn_transitionDomain (walkChart h hqf hgp cl e m)
      (walkChart h hqf hgp cl e (m + 1))
      (oChartTraceOverlapParam (walkChart h hqf hgp cl e m) (walkChart h hqf hgp cl e (m + 1))
        (walkOverlapClass h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_left h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_right h hqf hgp cl e hoverlap m)))
    (isPreconnected_connectedComponentIn)
    (connectedComponentIn_subset
      {x : ChartInterval (walkChart h hqf hgp cl e m).lo (walkChart h hqf hgp cl e m).hi |
        (oChartLift (walkChart h hqf hgp cl e m) x : OpenMobius) ∈
          (walkChart h hqf hgp cl e (m + 1)).W}
      (oChartTraceOverlapParam (walkChart h hqf hgp cl e m) (walkChart h hqf hgp cl e (m + 1))
        (walkOverlapClass h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_left h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_right h hqf hgp cl e hoverlap m)).1)

end LeanEval.KnotTheory.Quadrisecant