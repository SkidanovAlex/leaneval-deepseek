import Mathlib
import Submission.Work.Smooth.Schoenflies.Unconditional
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.annulusRegionAux

/-!
# The innermost curve of a finite family of pairwise disjoint simple plane curves

Let `κ i`, `i` in a finite non-empty type, be pairwise disjoint simple closed plane curves, all
contained in a closed convex set `C ⊆ ℂ` (in the application, the closed unit disc).  Then some
`κ i₀` is *innermost*: the bounded side of its Jordan--Schoenflies datum contains no point of any
curve of the family, and its closure is still contained in `C`.

The proof is the classical "take a curve innermost in `S`" argument, in the plane.

* For `i ≠ j` the trace of `κ j` is preconnected (it is the continuous image of `ℝ`) and disjoint
  from the trace of `κ i`, so it lies on one side of `κ i`:
  `Work.Smooth.Jordan.innermost_trace_subset_U_or_V`.
* **Nesting** (`Work.Smooth.Jordan.innermost_nested_of_trace_subset_V`): if the trace of `d` lies in the
  bounded side `P.V` of a Schoenflies datum for `c`, then the two sides are nested, `P.U ⊆ Q.U` and
  `Q.V ⊆ P.V`.  The unbounded side of `c` is preconnected, disjoint from the trace of `d` (which is
  inside `P.V`) and unbounded, hence lies in the unbounded side of `d`; every point of the trace of
  `c` is a limit point of the outside of `c`
  (`Work.Smooth.SphereJordan.trace_subset_closure_U`), so it is a limit point of `Q.U` as well, and
  being off the trace of `d` (which is inside `P.V ⊂ c.traceᶜ`) it lies in `Q.U`; the two inclusions
  `Q.U ⊇ P.U ∪ c.trace` then force `Q.V ⊆ P.V` because the complement of `U ∪ trace` is `V`.
* The relation `trace (κ j) ⊆ (P i).V` on the finite type `ι` is therefore irreflexive and
  transitive (a strict partial order), so the counting function
  `i ↦ #{j | trace (κ j) ⊆ (P i).V}` attains its minimum: at a minimiser `i₀` no curve of the family
  lies in `(P i₀).V`.
* A curve meeting `(P i₀).V` lies wholly in it (dichotomy), so no curve meets `(P i₀).V`.
* Finally the bounded side is contained in the convex set `C`, by
  `Work.Smooth.Jordan.plane_schoenflies_convex`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

/-- The trace of a closed plane curve is preconnected: it is the continuous image of `ℝ`. -/
theorem innermost_trace_preconnected (d : PlaneCurve) : IsPreconnected d.trace :=
  isPreconnected_range d.cont

/-- **A curve disjoint from `c` lies on one side of `c`.** -/
theorem innermost_trace_subset_U_or_V {c d : PlaneCurve} (P : PlaneSchoenflies c)
    (hdisj : Disjoint d.trace c.trace) : d.trace ⊆ P.U ∨ d.trace ⊆ P.V :=
  plane_separation_preconnected_subset P.toPlaneSeparation (innermost_trace_preconnected d)
    (fun _ hz hzc => Set.disjoint_left.mp hdisj hz hzc)

/-- **Nesting of the two sides of two simple closed plane curves.**  If the trace of `d` lies in the
bounded side of a Jordan--Schoenflies datum `P` for `c`, then the two sides are nested: the
unbounded side of `c` is contained in the unbounded side of `d`, and the bounded side of `d` is
contained in the bounded side of `c`. -/
theorem innermost_nested_of_trace_subset_V {c d : PlaneCurve} (P : PlaneSchoenflies c) (Q : PlaneSchoenflies d)
    (hsub : d.trace ⊆ P.V) : P.U ⊆ Q.U ∧ Q.V ⊆ P.V := by
  -- `V` is contained in the complement of the trace of its own curve
  have hVsub : P.V ⊆ c.traceᶜ := by
    intro z hz
    rw [← P.union_eq]
    exact Or.inr hz
  -- the outside of `c` avoids the trace of `d`
  have hPU_d : P.U ⊆ d.traceᶜ := fun z hz hzd =>
    Set.disjoint_left.mp P.disjoint_UV hz (hsub hzd)
  -- `P.U` is preconnected, unbounded and lies in `d.traceᶜ`, hence in the unbounded side of `d`
  have hPU_sub : P.U ⊆ Q.U := by
    rcases plane_separation_preconnected_subset Q.toPlaneSeparation P.preconn_U hPU_d with h | h
    · exact h
    · exfalso
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp Q.bounded_V
      obtain ⟨x, hxU, hx⟩ := plane_separation_unbounded P.toPlaneSeparation (M + 1)
      have := hM x (h hxU)
      linarith
  -- every point of the trace of `c` is a limit point of the outside of `d`
  have htrace_c : c.trace ⊆ Q.U := by
    intro z hz
    have hzcl : z ∈ closure P.U := Work.Smooth.SphereJordan.trace_subset_closure_U P hz
    have hzd : z ∉ d.trace := fun hzd => (hVsub (hsub hzd)) hz
    obtain ⟨ε, hε, _⟩ := Metric.isOpen_iff.mp d.isClosed_trace.isOpen_compl z hzd
    have hzcl' : z ∈ closure Q.U := by
      rw [mem_closure_iff]
      intro t htopen hzt
      obtain ⟨w, hw⟩ := (mem_closure_iff.mp hzcl) (t ∩ Metric.ball z ε)
        (htopen.inter Metric.isOpen_ball) ⟨hzt, Metric.mem_ball_self hε⟩
      exact ⟨w, hw.1.1, hPU_sub hw.2⟩
    rcases (show z ∈ Q.U ∪ Q.V by rw [Q.union_eq]; exact hzd) with h | h
    · exact h
    · exfalso
      obtain ⟨w, hwV, hwU⟩ := (mem_closure_iff.mp hzcl') Q.V Q.isOpen_V h
      exact Set.disjoint_left.mp Q.disjoint_UV hwU hwV
  refine ⟨hPU_sub, ?_⟩
  intro x hxV
  have hxnotU : x ∉ Q.U := fun h => Set.disjoint_left.mp Q.disjoint_UV h hxV
  have hxnotT : x ∉ c.trace := fun h => hxnotU (htrace_c h)
  rcases (show x ∈ P.U ∪ P.V by rw [P.union_eq]; exact hxnotT) with h | h
  · exact absurd (hPU_sub h) hxnotU
  · exact h

end

end Work.Smooth.Jordan

namespace Work.Drive

noncomputable section

/-- **The innermost curve of a finite family of pairwise disjoint simple plane curves.**
Let `κ i` (`i` in a finite non-empty type) be pairwise disjoint simple closed plane curves, all
contained in the closed unit disc.  Then some `κ i₀` is *innermost*: the bounded side `V` of its
Jordan–Schoenflies datum contains no point of any curve of the family, and its closure is still
contained in the closed unit disc. -/
theorem InnermostPlaneCurve {ι : Type} [Fintype ι] [Nonempty ι]
    (κ : ι → Work.Smooth.Jordan.PlaneCurve) (hsimple : ∀ i, (κ i).IsSimple)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (κ i).γ) (Set.range (κ j).γ))
    (hball : ∀ i, Set.range (κ i).γ ⊆ {z : ℂ | ‖z‖ ≤ 1}) :
    ∃ i₀ : ι, ∃ h : Work.Smooth.Jordan.PlaneSchoenflies (κ i₀),
      (∀ j : ι, Disjoint (Set.range (κ j).γ) h.V) ∧
      closure h.V ⊆ {z : ℂ | ‖z‖ ≤ 1} := by
  classical
  -- a Schoenflies datum for each curve
  have hP : ∀ i : ι, Nonempty (Work.Smooth.Jordan.PlaneSchoenflies (κ i)) := fun i =>
    Work.Smooth.Schoenflies.classicalInput (κ i) (hsimple i)
  let P : ∀ i : ι, Work.Smooth.Jordan.PlaneSchoenflies (κ i) := fun i => Classical.choice (hP i)
  -- the bounded side of a curve does not meet the curve itself
  have hVsub : ∀ i : ι, (P i).V ⊆ (κ i).traceᶜ := by
    intro i z hz
    rw [← (P i).union_eq]
    exact Or.inr hz
  -- the relation "the trace of `κ j` lies in the bounded side of `κ i`" is irreflexive
  have hirrefl : ∀ i : ι, ¬ (Set.range (κ i).γ ⊆ (P i).V) := by
    intro i h
    exact hVsub i (h ((κ i).mem_trace 0)) ((κ i).mem_trace 0)
  -- ... so the counting function attains its minimum: `i₀`
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset ι)
    (fun i => (Finset.univ.filter (fun k => Set.range (κ k).γ ⊆ (P i).V)).card)
    Finset.univ_nonempty
  have hmin' : ∀ j : ι,
      (Finset.univ.filter (fun k => Set.range (κ k).γ ⊆ (P i₀).V)).card ≤
      (Finset.univ.filter (fun k => Set.range (κ k).γ ⊆ (P j).V)).card := by
    intro j
    simpa using hmin j (Finset.mem_univ j)
  -- at a minimiser no curve of the family lies inside its bounded side
  have key : ∀ j : ι, ¬ (Set.range (κ j).γ ⊆ (P i₀).V) := by
    intro j hj
    have hji : j ≠ i₀ := by
      rintro rfl
      exact hirrefl j hj
    -- everything inside the bounded side of `κ j` is inside the bounded side of `κ i₀`
    have hVsub' : (P j).V ⊆ (P i₀).V :=
      (Work.Smooth.Jordan.innermost_nested_of_trace_subset_V (c := κ i₀) (d := κ j) (P i₀) (P j) hj).2
    have hsub : insert j (Finset.univ.filter (fun k => Set.range (κ k).γ ⊆ (P j).V)) ⊆
        (Finset.univ.filter (fun k => Set.range (κ k).γ ⊆ (P i₀).V)) := by
      intro k hk
      rw [Finset.mem_insert, Finset.mem_filter] at hk
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ k, ?_⟩
      rcases hk with h | ⟨-, hk⟩
      · rw [h]; exact hj
      · exact hk.trans hVsub'
    have hnotmem : j ∉ Finset.univ.filter (fun k => Set.range (κ k).γ ⊆ (P j).V) := by
      rw [Finset.mem_filter]
      rintro ⟨-, h⟩
      exact hirrefl j h
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotmem] at hcard
    have hle := hmin' j
    omega
  refine ⟨i₀, P i₀, ?_, ?_⟩
  · -- no curve of the family meets the bounded side of `κ i₀`
    intro j
    rw [Set.disjoint_left]
    intro x hx hxV
    by_cases hji : j = i₀
    · -- the curve itself is the boundary of its own side
      rw [hji] at hx
      exact hVsub i₀ hxV hx
    · -- otherwise the curve is disjoint from `κ i₀` and lies on one side of it
      rcases Work.Smooth.Jordan.innermost_trace_subset_U_or_V (P i₀)
        (show Disjoint (Set.range (κ j).γ) (Set.range (κ i₀).γ) from hdisj hji) with h | h
      · exact Set.disjoint_left.mp (P i₀).disjoint_UV (h hx) hxV
      · exact key j h
  · -- the bounded side lies in the closed unit disc
    rw [← (P i₀).range_e]
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Work.Smooth.Jordan.plane_schoenflies_convex (P i₀) (convex_closedBall _ _)
        Metric.isClosed_closedBall (fun w hw => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hball i₀ hw) hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz'
    exact hz'

end

end Work.Drive
