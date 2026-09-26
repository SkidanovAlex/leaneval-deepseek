import Mathlib
import ChallengeDeps
import Submission.OSubChart
import Submission.ComponentPath
import Submission.Commons.Analysis.Real.open_cover_subdivision

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — chart chains along `O`-paths

`OSubChart.lean` (S97) gave every trisecant class an interval chart
(`OSub1Chart`, an open real interval homeomorphic to an open trace of the
trisecant set `O`), and its transition section made overlapping charts
compatible by homeomorphisms of open interval domains preserving the class
(`oSub1Chart_transition`, `oChartTransitionHomeo`,
`exists_oChartTransitionParam_of_mem_both`).  This module builds the
**global chaining** statement on top: every continuous path of trisecant
classes (e.g. a path inside one connected component of `O`, supplied by
`ComponentPath.exists_path_in_component_in_O`) is covered by finitely many
interval charts whose traces overlap consecutively.

1. **cover machinery** — `oChartAtClass` (the interval chart at a class,
   a classical choice from `osub1Chart_at_class`), `oTraceTime` (the open
   set of times whose path class lies in the trace of the chart at `t`),
   its ambient-open real representative `oTraceTimeReal`, the real-cover
   fact and the uniform subdivision `oTraceTime_subdivision`
   (Lebesgue-number style via the commons lemma
   `Commons.Analysis.Real.open_cover_subdivision`);
2. **grid real arithmetic** — `gridReal_mem_Icc`, `gridReal_mono`,
   `gridReal_succ_sub` (grid points `i/N`, monotonicity, spacing `1/N`);
3. **the chain theorem `exists_oChart_chain_along_path`**: for a path `γ`
   of classes and a subdivision size `N`, cover times `τ i` and charts
   `ch i` (centred at `γ (τ i)`) such that every path class over the grid
   subinterval `[i/N, (i+1)/N]` lies in the trace of `ch i`, the initial
   class lies in the trace of the first chart and the final class in the
   trace of the last chart, and the traces of consecutive charts both
   contain the class at the common grid point `(i+1)/N` (so each
   consecutive pair has an inhabited transition domain);
4. **the transition chain `exists_oChartTransition_chain_along_path`**:
   the consecutive charts (and the endpoint charts at the source and
   target classes) have inhabited transition domains — the transition
   homeomorphisms `oChartTransitionHomeo` can be applied successively
   along the chain.

This is the elementary glue of the component classification (brick (b)):
applied to the component path of `ComponentPath` it shows that any two
classes of one connected component of `O` are connected by a finite chain
of interval charts with compatible (homeomorphic) change-of-parameters —
the input to the arc/circle classification of the components.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- A real number of `[0,1]` viewed as an element of the unit interval. -/
def realTime {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : I := ⟨x, hx⟩

/-- chart choice along a path -/
def oChartAtClass {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (c : OSub r) : OSub1Chart r c :=
  Classical.choice (osub1Chart_at_class h hqf hgp c)

def oTraceTime {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) (t : I) : Set I :=
  {u : I | (γ u : OpenMobius) ∈ (oChartAtClass h hqf hgp (γ t)).W}

lemma isOpen_oTraceTime {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) (t : I) : IsOpen (oTraceTime h hqf hgp γ t) := by
  dsimp [oTraceTime]
  have hmap : Continuous (fun u : I => (γ u : OpenMobius)) :=
    continuous_subtype_val.comp γ.toContinuousMap.continuous
  exact ((oChartAtClass h hqf hgp (γ t)).W_open).preimage hmap

noncomputable def oTraceTimeReal {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) (t : I) : Set ℝ :=
  Classical.choose (isOpen_induced_iff.mp (isOpen_oTraceTime h hqf hgp γ t))

lemma isOpen_oTraceTimeReal {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) (t : I) : IsOpen (oTraceTimeReal h hqf hgp γ t) :=
  (Classical.choose_spec (isOpen_induced_iff.mp (isOpen_oTraceTime h hqf hgp γ t))).1

lemma oTraceTime_eq_oTraceTimeReal {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) (t : I) :
    oTraceTime h hqf hgp γ t =
      (fun u : I => (u : ℝ)) ⁻¹' oTraceTimeReal h hqf hgp γ t :=
  (Classical.choose_spec (isOpen_induced_iff.mp (isOpen_oTraceTime h hqf hgp γ t))).2.symm

lemma real_cover_oTraceTime {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) :
    (Set.Icc (0 : ℝ) 1 : Set ℝ) ⊆
      ⋃ t : I, oTraceTimeReal h hqf hgp γ t := by
  intro x hx
  let u : I := ⟨x, hx⟩
  have hu : u ∈ oTraceTime h hqf hgp γ u := by
    dsimp [oTraceTime]
    exact (oChartAtClass h hqf hgp (γ u)).c₀_mem
  have hur : (u : ℝ) ∈ oTraceTimeReal h hqf hgp γ u := by
    simpa [oTraceTime_eq_oTraceTimeReal h hqf hgp γ u] using hu
  exact Set.mem_iUnion.mpr ⟨u, hur⟩

theorem oTraceTime_subdivision {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x ≤ y → y - x ≤ δ →
        ∃ t : I, Set.Icc x y ⊆ oTraceTimeReal h hqf hgp γ t := by
  let U : I → Set ℝ := fun t => oTraceTimeReal h hqf hgp γ t
  have hUo : ∀ t : I, IsOpen (U t) := fun t => isOpen_oTraceTimeReal h hqf hgp γ t
  exact Commons.Analysis.Real.open_cover_subdivision (by norm_num) U hUo
    (by simpa [U] using real_cover_oTraceTime h hqf hgp γ)

/-- A real point of a covered subinterval gives a class in the trace of the
covering chart. -/
lemma mem_trace_of_real_in_cell {r : ℝ → Space} {a b : OSub r} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (γ : Path a b) {τ : I} {xL xR : ℝ} {x : ℝ}
    (hcell : Set.Icc xL xR ⊆ oTraceTimeReal h hqf hgp γ τ)
    (hr01 : x ∈ Set.Icc (0 : ℝ) 1) (hr : x ∈ Set.Icc xL xR) :
    (γ (realTime hr01) : OpenMobius) ∈ (oChartAtClass h hqf hgp (γ τ)).W := by
  have hgV : (realTime hr01 : I) ∈ oTraceTime h hqf hgp γ τ := by
    rw [oTraceTime_eq_oTraceTimeReal h hqf hgp γ τ]
    exact hcell hr
  simpa [oTraceTime, realTime] using hgV

/-- nonnegativity/≤1 of i/N for i ≤ N. -/
lemma gridReal_mem_Icc {N : ℕ} (hN : 0 < N) (i : ℕ) (hi : i ≤ N) :
    (i : ℝ) / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg i) (le_of_lt (by exact_mod_cast hN : (0 : ℝ) < (N : ℝ)))
  · rw [div_le_iff₀ (by exact_mod_cast hN)]
    norm_num
    exact_mod_cast hi

/-- i/N ≤ (i+1)/N. -/
lemma gridReal_mono {N : ℕ} (hN : 0 < N) (i : ℕ) :
    (i : ℝ) / (N : ℝ) ≤ ((i + 1 : ℕ) : ℝ) / (N : ℝ) := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.le_succ i))
    (le_of_lt (by exact_mod_cast hN : (0 : ℝ) < (N : ℝ)))

/-- (i+1)/N − i/N = 1/N. -/
lemma gridReal_succ_sub {N : ℕ} (hN : 0 < N) (i : ℕ) :
    (((i + 1 : ℕ) : ℝ) / (N : ℝ)) - ((i : ℝ) / (N : ℝ)) = (1 : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  field_simp [hNpos.ne']
  norm_num



/-- **Chart-chain along an `O`-path.**  A continuous path of trisecant
classes is covered by finitely many interval charts of `O` whose traces
overlap consecutively: there is a positive `N`, for each grid interval
`[i/N, (i+1)/N]` a cover time `τ i` whose chart `ch i` (centred at
`γ (τ i)`) contains every path class over that subinterval, the first
chart's trace contains the initial class and the last chart's trace the
final class, and the traces of `ch i` and `ch (i+1)` both contain the
class at the common grid point `(i+1)/N` — so each consecutive pair has a
nonempty transition domain and the transition homeomorphisms can be
applied successively along the chain. -/
theorem exists_oChart_chain_along_path {r : ℝ → Space} {a b : OSub r}
    (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (γ : Path a b) :
    ∃ (N : ℕ) (hN : 0 < N) (τ : Fin N → I),
      ∃ ch : (i : Fin N) → OSub1Chart r (γ (τ i)),
        (γ (realTime (gridReal_mem_Icc hN 0 (Nat.zero_le N))) : OpenMobius) ∈
            (ch ⟨0, hN⟩).W ∧
        (γ (realTime (gridReal_mem_Icc hN N (le_rfl))) : OpenMobius) ∈
            (ch ⟨N - 1, (by omega)⟩).W ∧
        ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
          let j : Fin N := ⟨i.1 + 1, hi⟩
          (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈
              (ch i).W ∧
          (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈
              (ch j).W := by
  classical
  rcases oTraceTime_subdivision h hqf hgp γ with ⟨δ, hδpos, hsub⟩
  rcases exists_nat_gt ((1 : ℝ) / δ) with ⟨M, hM⟩
  let N : ℕ := M + 1
  have hN0 : 0 < N := by omega
  have hδN : (1 : ℝ) / (N : ℝ) ≤ δ := by
    have hM' : (1 : ℝ) / δ < (N : ℝ) := by
      dsimp [N]
      exact lt_of_lt_of_le hM (by exact_mod_cast (Nat.le_succ M))
    have h1le : (1 : ℝ) ≤ δ * (N : ℝ) := by
      have h1lt : (1 : ℝ) < (N : ℝ) * δ := (div_lt_iff₀ hδpos).mp hM'
      exact le_of_lt (by simpa [mul_comm] using h1lt)
    rw [div_le_iff₀ (by exact_mod_cast hN0 : (0 : ℝ) < (N : ℝ))]
    exact h1le
  -- each grid interval is covered by a chart-time
  have hsub_i : ∀ i : Fin N, ∃ τ : I,
      Set.Icc ((i.1 : ℝ) / (N : ℝ)) (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ)) ⊆
        oTraceTimeReal h hqf hgp γ τ := by
    intro i
    have hx : (i.1 : ℝ) / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      gridReal_mem_Icc hN0 i.1 (le_of_lt i.isLt)
    have hy : (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ)) ∈ Set.Icc (0 : ℝ) 1 :=
      gridReal_mem_Icc hN0 (i.1 + 1) (Nat.succ_le_of_lt i.isLt)
    have hxy : (i.1 : ℝ) / (N : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) :=
      gridReal_mono hN0 i.1
    have hlen : (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ)) - ((i.1 : ℝ) / (N : ℝ)) ≤ δ := by
      rw [gridReal_succ_sub hN0 i.1]
      exact hδN
    exact hsub ((i.1 : ℝ) / (N : ℝ)) (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ)) hx hy hxy hlen
  let τ : Fin N → I := fun i => Classical.choose (hsub_i i)
  have hcell : ∀ i : Fin N,
      Set.Icc ((i.1 : ℝ) / (N : ℝ)) (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ)) ⊆
        oTraceTimeReal h hqf hgp γ (τ i) := by
    intro i
    exact Classical.choose_spec (hsub_i i)
  let ch : (i : Fin N) → OSub1Chart r (γ (τ i)) :=
    fun i => oChartAtClass h hqf hgp (γ (τ i))
  -- initial class in the first chart trace
  have hstart : (γ (realTime (gridReal_mem_Icc hN0 0 (Nat.zero_le N))) : OpenMobius) ∈
      (ch ⟨0, hN0⟩).W := by
    dsimp [ch]
    refine mem_trace_of_real_in_cell h hqf hgp γ (hcell ⟨0, hN0⟩)
      (gridReal_mem_Icc hN0 0 (Nat.zero_le N)) ?_
    constructor
    · rfl
    · exact gridReal_mono hN0 0
  -- final class in the last chart trace
  have hend : (γ (realTime (gridReal_mem_Icc hN0 N (le_rfl))) : OpenMobius) ∈
      (ch ⟨N - 1, (by omega : N - 1 < N)⟩).W := by
    dsimp [ch]
    refine mem_trace_of_real_in_cell h hqf hgp γ
      (hcell ⟨N - 1, (by omega : N - 1 < N)⟩) (gridReal_mem_Icc hN0 N (le_rfl)) ?_
    constructor
    · -- (N-1)/N ≤ N/N: via (N-1) ≤ N as naturals
      exact gridReal_mono hN0 (N - 1)
    · -- N/N ≤ ((N-1)+1)/N  (numerator equality)
      have hnum : (((N - 1) + 1 : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast (by omega : (N - 1) + 1 = N)
      rw [hnum]
  -- consecutive overlaps
  have hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
      let j : Fin N := ⟨i.1 + 1, hi⟩
      (γ (realTime (gridReal_mem_Icc hN0 (i.1 + 1) (by omega))) : OpenMobius) ∈
          (ch i).W ∧
      (γ (realTime (gridReal_mem_Icc hN0 (i.1 + 1) (by omega))) : OpenMobius) ∈
          (ch j).W := by
    intro i hi
    let j : Fin N := ⟨i.1 + 1, hi⟩
    have hleN : i.1 + 1 ≤ N := le_of_lt hi
    constructor
    · dsimp [ch]
      refine mem_trace_of_real_in_cell h hqf hgp γ (hcell i)
        (gridReal_mem_Icc hN0 (i.1 + 1) hleN) ?_
      constructor
      · exact gridReal_mono hN0 i.1
      · rfl
    · dsimp [ch, j]
      refine mem_trace_of_real_in_cell h hqf hgp γ (hcell j)
        (gridReal_mem_Icc hN0 (i.1 + 1) hleN) ?_
      constructor
      · rfl
      · exact gridReal_mono hN0 (i.1 + 1)
  exact ⟨N, hN0, τ, ch, hstart, hend, hover⟩

/-! ## 5. The chain gives inhabited consecutive transition domains -/

/-- The real grid point 0 equals the unit-interval point 0. -/
lemma realTime_zero {N : ℕ} (hN : 0 < N) :
    realTime (gridReal_mem_Icc hN 0 (Nat.zero_le N)) = (⟨0, by norm_num⟩ : I) := by
  apply Subtype.ext
  simp [realTime]

/-- The real grid point N/N equals the unit-interval point 1. -/
lemma realTime_one {N : ℕ} (hN : 0 < N) :
    realTime (gridReal_mem_Icc hN N (le_rfl)) = (⟨1, by norm_num⟩ : I) := by
  apply Subtype.ext
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  simp [realTime, hNne]

/-- **The transition chain along an `O`-path.**  The interval charts of the
grid chain of `exists_oChart_chain_along_path` have inhabited consecutive
transition domains — and the charts at the source and target classes of
the path also chain to the first and last grid charts — so the transition
homeomorphisms `oChartTransitionHomeo` can be applied successively along
the whole chain. -/
theorem exists_oChartTransition_chain_along_path {r : ℝ → Space} {a b : OSub r}
    (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (γ : Path a b) :
    ∃ (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
      (ch : (i : Fin N) → OSub1Chart r (γ (τ i))),
      Nonempty (OChartTransitionDomain (oChartAtClass h hqf hgp a) (ch ⟨0, hN⟩)) ∧
      Nonempty (OChartTransitionDomain (ch ⟨N - 1, (by omega : N - 1 < N)⟩)
        (oChartAtClass h hqf hgp b)) ∧
      ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        Nonempty (OChartTransitionDomain (ch i) (ch j)) := by
  rcases exists_oChart_chain_along_path h hqf hgp γ with ⟨N, hN, τ, ch, hstart, hend, hover⟩
  refine ⟨N, hN, τ, ch, ?_, ?_, ?_⟩
  · have hA0 : (γ (realTime (gridReal_mem_Icc hN 0 (Nat.zero_le N))) : OpenMobius) =
        (a : OpenMobius) := by
      rw [realTime_zero hN]
      exact congrArg (fun z : OSub r => (z : OpenMobius)) γ.source
    have haW : (a : OpenMobius) ∈ (oChartAtClass h hqf hgp a).W :=
      (oChartAtClass h hqf hgp a).c₀_mem
    have ha0 : (a : OpenMobius) ∈ (ch ⟨0, hN⟩).W := by
      rw [hA0] at hstart
      exact hstart
    rcases exists_oChartTransitionParam_of_mem_both (oChartAtClass h hqf hgp a) (ch ⟨0, hN⟩)
      a haW ha0 with ⟨x, hx⟩
    exact Nonempty.intro x
  · have hB1 : (γ (realTime (gridReal_mem_Icc hN N (le_rfl))) : OpenMobius) =
        (b : OpenMobius) := by
      rw [realTime_one hN]
      exact congrArg (fun z : OSub r => (z : OpenMobius)) γ.target
    have hbW : (b : OpenMobius) ∈ (oChartAtClass h hqf hgp b).W :=
      (oChartAtClass h hqf hgp b).c₀_mem
    have hb1 : (b : OpenMobius) ∈ (ch ⟨N - 1, (by omega : N - 1 < N)⟩).W := by
      rw [hB1] at hend
      exact hend
    rcases exists_oChartTransitionParam_of_mem_both (ch ⟨N - 1, (by omega : N - 1 < N)⟩)
      (oChartAtClass h hqf hgp b) b hb1 hbW with ⟨x, hx⟩
    exact Nonempty.intro x
  · intro i hi
    let j : Fin N := ⟨i.1 + 1, hi⟩
    rcases exists_oChartTransitionParam_of_mem_both (ch i) (ch j) (γ (realTime
      (gridReal_mem_Icc hN (i.1 + 1) (by omega : i.1 + 1 ≤ N)))) (hover i hi).1 (hover i hi).2
      with ⟨x, hx⟩
    exact Nonempty.intro x

end LeanEval.KnotTheory.Quadrisecant
