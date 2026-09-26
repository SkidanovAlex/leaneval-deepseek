import Mathlib
import Submission.NestedFamily

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

/-!
# Milestone-2 (iv) step 6, brick (b) — the walk partial-union API
(open / path-connected / component-subset / trace-membership /
overlap-class / covering)

`NestedFamily.lean` (S143) defined the walk partial unions
`P'_k := ⋃ m ∈ Iio k, OChartTraceSet h hqf hgp (cl (e m))` (the
candidate `Uₙ = P'_{n+2}` of the increasing family) and verified the
set-side F2-a clauses (monotonicity `P'_k ⊆ P'_{k+1}`).  This module
consolidates the remaining topological API of the partial unions in the
same S135–S150 notation, ready for the interval-charting (sweep) slice:

1. **`isOpen_walkPartialUnion`** — each `P'_k` is open in `OSub r` (a
   finite union of the open chart traces `isOpen_OChartTraceSet`);
2. **`walkPartialUnion_pathConnected`** — each nonempty step `P'_{k+1}`
   is path-connected: a chain of pairwise-overlapping path-connected
   traces (`IsPathConnected.union` induction over `k`, the overlap point
   of `T_k ∩ T_{k+1}` lying in `P'_{k+1}`);
3. **`walkPartialUnion_subset_component`** — under
   `hcl : ∀ n, cl (e n) ∈ connectedComponent c₀` each `P'_k` lies in the
   component `C` (each trace lies in the component of its centre,
   `OChartTrace_subset_component`);
4. **`walkTrace_subset_partialUnion`** — the trace-membership clause
   (`m < k` ⇒ `T_m ⊆ P'_k`);
5. **`walkOverlapClass_mem_partialUnion`** — the junction class
   `walkOverlapClass m ∈ T_m ∩ T_{m+1}` lies in `P'_{m+2}`;
6. **`walkPartialUnion_covers_component`** — if the enumeration `cl`
   covers `C` and the walk index `e` is surjective, the partial unions
   exhaust `C`: `C ⊆ ⋃ₖ P'_k`;
7. **`walkPartialUnion_subset_of_le`** — the index-monotonicity closure
   (`m ≤ k` ⇒ `P'_m ⊆ P'_k`, iterating `walkPartialUnion_mono`);
8. **`compact_subset_walkPartialUnion`** — **compact subsets of the
   component are absorbed by a single partial union**: `K ⊆ C` compact
   ⇒ `∃ k, K ⊆ P'_k` (finite-subcover bookkeeping, via
   `IsCompact.elim_finite_subcover` + `Finset.le_sup` + the
   index-monotonicity closure);
9. **`compact_component_in_partialUnion`** — a compact component is a
   single partial union: `IsCompact C` ⇒ `∃ k, C ⊆ P'_k` (the
   chain-wraps-around marker of the circle side of the dichotomy; with
   item 3, `C = P'_k`).

Together with `walkPartialUnion_mono`/`nestedU_mono` (S143) this is the
complete walk-side skeleton the classification consumes: an increasing
open path-connected covering family of a path-connected open 1-manifold
component.  All hypotheses are in the walk-data shape of
`component_trace_walk` (S115), so the API instantiates directly on the
component walk.  Everything here is elementary and verified (no axioms,
no `sorry`).
-/

/-- The walk partial unions are open in `OSub r`: finite unions of the
open chart traces (`isOpen_OChartTraceSet`). -/
lemma isOpen_walkPartialUnion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (k : ℕ) :
    IsOpen (walkPartialUnion h hqf hgp cl e k) := by
  dsimp [walkPartialUnion]
  exact isOpen_biUnion (fun m hm => isOpen_OChartTraceSet (x := cl (e m)))

/-- **The walk partial union `P'_{k+1}` is path-connected**: a chain of
pairwise-overlapping path-connected traces (`IsPathConnected.union`
induction over `k`, the overlap point from `hoverlap k` lying in
`P'_{k+1}` through the left trace). -/
lemma walkPartialUnion_pathConnected {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (k : ℕ) :
    IsPathConnected (walkPartialUnion h hqf hgp cl e (k + 1)) := by
  have hmain : ∀ n : ℕ,
      IsPathConnected (⋃ m ∈ Set.Iio (n + 1), OChartTraceSet h hqf hgp (cl (e m))) := by
    intro n
    induction n with
    | zero =>
        have hset : (⋃ m ∈ Set.Iio (0 + 1), OChartTraceSet h hqf hgp (cl (e m))) =
            OChartTraceSet h hqf hgp (cl (e 0)) := by
          ext c
          constructor
          · intro hc
            rcases Set.mem_iUnion₂.mp hc with ⟨m, hm, hcm⟩
            have hmlt : m < 0 + 1 := Set.mem_Iio.mp hm
            have hm0 : m = 0 := by omega
            simpa [hm0] using hcm
          · intro hc
            exact Set.mem_iUnion₂.mpr ⟨0, Set.mem_Iio.mpr (by omega), hc⟩
        rw [hset]
        exact oChartTrace_pathConnected (x := cl (e 0))
    | succ n ih =>
        have hset : (⋃ m ∈ Set.Iio (n + 1 + 1), OChartTraceSet h hqf hgp (cl (e m))) =
            (⋃ m ∈ Set.Iio (n + 1), OChartTraceSet h hqf hgp (cl (e m))) ∪
              OChartTraceSet h hqf hgp (cl (e (n + 1))) := by
          ext c
          constructor
          · intro hc
            rcases Set.mem_iUnion₂.mp hc with ⟨m, hm, hcm⟩
            have hmlt : m < n + 1 + 1 := Set.mem_Iio.mp hm
            by_cases hmk : m < n + 1
            · left
              exact Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr hmk, hcm⟩
            · right
              have hm' : m = n + 1 := by omega
              simpa [hm'] using hcm
          · intro hc
            rcases hc with hc | hc
            · rcases Set.mem_iUnion₂.mp hc with ⟨m, hm, hcm⟩
              exact Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr (by
                have hmk : m < n + 1 := Set.mem_Iio.mp hm
                omega), hcm⟩
            · exact Set.mem_iUnion₂.mpr ⟨n + 1, Set.mem_Iio.mpr (by omega), hc⟩
        rw [hset]
        apply IsPathConnected.union ih
        · exact oChartTrace_pathConnected (x := cl (e (n + 1)))
        · rcases hoverlap n with ⟨z, hzL, hzR⟩
          refine ⟨z, ?_, hzR⟩
          apply Set.mem_iUnion₂.mpr
          exact ⟨n, Set.mem_Iio.mpr (by omega), hzL⟩
  change IsPathConnected (⋃ m ∈ Set.Iio (k + 1), OChartTraceSet h hqf hgp (cl (e m)))
  exact hmain k

/-- The walk partial unions lie in the connected component `C` of `c₀`
when every walk centre class does (each trace lies in the component of
its centre class, `OChartTrace_subset_component`). -/
lemma walkPartialUnion_subset_component {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (c₀ : OSub r)
    (hcl : ∀ n : ℕ, cl (e n) ∈ connectedComponent c₀) (k : ℕ) :
    walkPartialUnion h hqf hgp cl e k ⊆ connectedComponent c₀ := by
  intro y hy
  rcases Set.mem_iUnion₂.mp hy with ⟨m, hm, hym⟩
  exact OChartTrace_subset_component c₀ (cl (e m)) (hcl m) hym

/-- A trace before `k` lies in `P'_k` (the trace-membership clause:
`m < k` implies `T_m ⊆ P'_k`). -/
lemma walkTrace_subset_partialUnion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) {m k : ℕ} (hmk : m < k) :
    OChartTraceSet h hqf hgp (cl (e m)) ⊆ walkPartialUnion h hqf hgp cl e k := by
  intro y hy
  exact Set.mem_iUnion₂.mpr ⟨m, Set.mem_Iio.mpr hmk, hy⟩

/-- The overlap class at junction `m` lies in `P'_{m+2}` (the left trace
membership of `walkOverlapClass_mem_left` lands in the union of the
first `m+2` traces). -/
lemma walkOverlapClass_mem_partialUnion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (m : ℕ) :
    walkOverlapClass h hqf hgp cl e hoverlap m ∈
      walkPartialUnion h hqf hgp cl e (m + 2) := by
  apply Set.mem_iUnion₂.mpr
  exact ⟨m, Set.mem_Iio.mpr (by omega),
    walkOverlapClass_mem_left h hqf hgp cl e hoverlap m⟩

/-- **The walk partial unions cover the component** (in the limit): if
the enumeration `cl` covers `C` (`hcov`, the S107 cover property) and the
walk index `e` is surjective, then every class of `C` lies in some
`P'_k` (`P'_{j+1}` for a preimage `j` of its covering index). -/
lemma walkPartialUnion_covers_component {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (c₀ : OSub r)
    (hcov : ∀ y : OSub r, y ∈ connectedComponent c₀ →
      ∃ n : ℕ, y ∈ OChartTraceSet h hqf hgp (cl n))
    (he : Function.Surjective e) :
    connectedComponent c₀ ⊆
      ⋃ k : ℕ, walkPartialUnion h hqf hgp cl e k := by
  intro y hy
  rcases hcov y hy with ⟨n, hyn⟩
  rcases he n with ⟨j, hj⟩
  refine Set.mem_iUnion.mpr ⟨j + 1, ?_⟩
  apply Set.mem_iUnion₂.mpr
  exact ⟨j, Set.mem_Iio.mpr (by omega), by simpa [hj] using hyn⟩


set_option maxHeartbeats 1600000

/-- The walk partial unions are monotone in the index: `m ≤ k` implies
`P'_m ⊆ P'_k` (iteration of `walkPartialUnion_mono`). -/
lemma walkPartialUnion_subset_of_le {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (m k : ℕ) (hmk : m ≤ k) :
    walkPartialUnion h hqf hgp cl e m ⊆ walkPartialUnion h hqf hgp cl e k := by
  induction k with
  | zero =>
      have hm0 : m = 0 := by omega
      simp [hm0]
  | succ k ih =>
      rcases lt_or_eq_of_le hmk with hlt | heq
      · exact Subset.trans (ih (Nat.le_of_lt_succ hlt))
          (walkPartialUnion_mono h hqf hgp cl e k)
      · simp [heq]

/-- **Compact subsets of the component are absorbed by a single walk
partial union**: if `K ⊆ C` is compact and the walk exhausts `C`
(`hcov` + `he`), then `∃ k, K ⊆ P'_k` (finite-subcover bookkeeping of
the compact side of the dichotomy). -/
lemma compact_subset_walkPartialUnion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (c₀ : OSub r)
    (hcov : ∀ y : OSub r, y ∈ connectedComponent c₀ →
      ∃ n : ℕ, y ∈ OChartTraceSet h hqf hgp (cl n))
    (he : Function.Surjective e)
    {K : Set (OSub r)} (hK : IsCompact K) (hKsub : K ⊆ connectedComponent c₀) :
    ∃ k : ℕ, K ⊆ walkPartialUnion h hqf hgp cl e k := by
  have hcover : K ⊆ ⋃ k : ℕ, walkPartialUnion h hqf hgp cl e k := by
    intro y hy
    exact walkPartialUnion_covers_component h hqf hgp cl e c₀ hcov he (hKsub hy)
  rcases hK.elim_finite_subcover (fun k : ℕ => walkPartialUnion h hqf hgp cl e k)
    (fun k => isOpen_walkPartialUnion h hqf hgp cl e k) hcover with ⟨t, hKt⟩
  let N : ℕ := t.sup id
  have hsubUnion : (⋃ i ∈ (t : Set ℕ), walkPartialUnion h hqf hgp cl e i) ⊆
      walkPartialUnion h hqf hgp cl e N := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨i, hi, hyi⟩
    exact walkPartialUnion_subset_of_le h hqf hgp cl e i N (Finset.le_sup (s := t) (f := id) hi) hyi
  refine ⟨N, Subset.trans hKt hsubUnion⟩

/-- **A compact component is a single partial union**: if the component
`C` is compact, then for some `k`, `C ⊆ P'_k` (and since `P'_k ⊆ C`
always, `C = P'_k` — the chain wraps around; the circle side of the
dichotomy). -/
lemma compact_component_in_partialUnion {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ) (c₀ : OSub r)
    (hcov : ∀ y : OSub r, y ∈ connectedComponent c₀ →
      ∃ n : ℕ, y ∈ OChartTraceSet h hqf hgp (cl n))
    (he : Function.Surjective e)
    (hC : IsCompact (connectedComponent c₀)) :
    ∃ k : ℕ, connectedComponent c₀ ⊆ walkPartialUnion h hqf hgp cl e k := by
  exact compact_subset_walkPartialUnion h hqf hgp cl e c₀ hcov he hC (fun y hy => hy)

end LeanEval.KnotTheory.Quadrisecant
