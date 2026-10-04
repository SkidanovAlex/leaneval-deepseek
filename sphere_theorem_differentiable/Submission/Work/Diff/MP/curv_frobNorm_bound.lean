import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.MP

/-- **Joint continuity of the squared curvature norm along a Ricci flow.**

`(s, x) ↦ |Rm(G s)|²(x)` is continuous on `[0,T'] × M` whenever `G` is a Ricci flow on `[0,T)` and
`T' < T`.  This is the regularity statement underlying the uniform Frobenius bound
`Work.Diff.MP.curv_frobNorm_bound`: the value `rmNormSq (G s) x` is frame independent, so it is the
jointly smooth contraction `N4 (GramM G x₀) (rmC4 G x₀)` in a chart, and `IsRicciFlow` gives joint
smoothness of the metric family on the *half-open* interval `[0,T)` — the endpoint `s = 0` (and any
`x`) is reached by the time reparametrisation `t = τ²`
(`Work.Diff.GE.cfq_jointSmooth_sqFlow`), which turns `[0,T)` into an open interval around `0`. -/
theorem curv_rmNormSq_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {T T' : ℝ}
    (hflow : IsRicciFlow G T) (hT' : T' < T) (hT'0 : 0 ≤ T') :
    ContinuousOn (fun p : ℝ × M ↦ rmNormSq (G p.1) p.2) (Icc 0 T' ×ˢ (univ : Set M)) := by
  have hTpos : 0 < T := lt_of_le_of_lt hT'0 hT'
  have hsqrt_lt : Real.sqrt T' < Real.sqrt T := Real.sqrt_lt_sqrt hT'0 hT'
  -- a radius `ρ` with `√T' < ρ` and `ρ² < T`; then `τ ↦ G (τ²)` is smooth on `(-ρ, ρ)`
  set ρ : ℝ := (Real.sqrt T' + Real.sqrt T) / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith [Real.sqrt_nonneg T']
  have hρlt : ρ < Real.sqrt T := by rw [hρ]; linarith
  have hρsq : ρ ^ 2 < T := by
    have h1 : ρ ^ 2 < (Real.sqrt T) ^ 2 := by
      nlinarith [hρlt, hρpos, Real.sqrt_nonneg T]
    rwa [Real.sq_sqrt (le_of_lt hTpos)] at h1
  have hG : JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Ioo (-ρ) ρ) :=
    Work.Diff.GE.cfq_jointSmooth_sqFlow G hTpos hρpos hρsq hflow.1
  rintro ⟨s₀, x₀⟩ ⟨hs, -⟩
  have hτ : Real.sqrt s₀ ∈ Ioo (-ρ) ρ := by
    refine ⟨?_, ?_⟩
    · have := Real.sqrt_nonneg s₀; linarith
    · have h2 : Real.sqrt s₀ ≤ Real.sqrt T' := Real.sqrt_le_sqrt hs.2
      linarith
  have hsm := Work.Diff.GE.cfq_rmNormSq_jointSmoothAt (M := M) hLC isOpen_Ioo hG hτ x₀
  have hcont : ContinuousAt (fun p : ℝ × M ↦ rmNormSq (Work.Diff.GE.cfq_sqFlow G p.1) p.2)
      (Real.sqrt s₀, x₀) := hsm.continuousAt
  have hmap : ContinuousAt (fun p : ℝ × M ↦ (Real.sqrt p.1, p.2)) (s₀, x₀) :=
    ((Real.continuous_sqrt.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hcomp : ContinuousAt (fun p : ℝ × M ↦
      rmNormSq (Work.Diff.GE.cfq_sqFlow G (Real.sqrt p.1)) p.2) (s₀, x₀) := by
    have h1 : ContinuousAt ((fun p : ℝ × M ↦
        rmNormSq (Work.Diff.GE.cfq_sqFlow G p.1) p.2) ∘
        (fun p : ℝ × M ↦ (Real.sqrt p.1, p.2))) (s₀, x₀) :=
      ContinuousAt.comp (g := fun p : ℝ × M ↦
          rmNormSq (Work.Diff.GE.cfq_sqFlow G p.1) p.2)
        (f := fun p : ℝ × M ↦ (Real.sqrt p.1, p.2)) (x := (s₀, x₀)) hcont hmap
    simpa only [Function.comp_def] using h1
  refine hcomp.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    show rmNormSq (G p.1) p.2 = rmNormSq (Work.Diff.GE.cfq_sqFlow G (Real.sqrt p.1)) p.2
    rw [show Work.Diff.GE.cfq_sqFlow G (Real.sqrt p.1) = G ((Real.sqrt p.1) ^ 2) from rfl,
      Real.sq_sqrt hp.1.1]
  · show rmNormSq (G s₀) x₀ = rmNormSq (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s₀)) x₀
    rw [show Work.Diff.GE.cfq_sqFlow G (Real.sqrt s₀) = G ((Real.sqrt s₀) ^ 2) from rfl,
      Real.sq_sqrt hs.1]

/-- On a compact time interval strictly inside the interval of existence of a Ricci flow, the
Frobenius norm of the curvature is uniformly bounded.  (`frobNorm (rmC (G s) x)` is the
frame-independent value `√(rmNormSq (G s) x)`, so this is joint continuity of `rmNormSq` on the
compact `[0,T'] × M`; the `t`-dependence enters through `IsRicciFlow.JointSmooth`, the `x`-dependence
through the spatial smoothness of the curvature, e.g. `Work.Diff.GE.contMDiff_rmP_fields`; `LCSmooth`
may be derived from `[I.Boundaryless] [T2Space M]` via `Work.Diff.T.lc_smooth` if needed.) -/
theorem curv_frobNorm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → SMet I M) (T T' : ℝ) (hflow : IsRicciFlow G T) (hT' : T' < T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ Icc 0 T', ∀ x : M, frobNorm (rmC (G s) x) ≤ ρ := by
  rcases lt_or_ge T' 0 with hneg | hnonneg
  · -- the interval `[0,T']` is empty
    exact ⟨1, one_pos, fun s hs _ => absurd hs.1 (not_le.mpr (lt_of_le_of_lt hs.2 hneg))⟩
  · have hLC : LCSmooth I M := Work.Diff.T.lc_smooth
    have hcont := curv_rmNormSq_continuousOn (I := I) (M := M) hLC hflow hT' hnonneg
    have hcomp : IsCompact (Icc 0 T' ×ˢ (univ : Set M)) := isCompact_Icc.prod isCompact_univ
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
    refine ⟨Real.sqrt (max C 0) + 1, ?_, fun s hs x => ?_⟩
    · have := Real.sqrt_nonneg (max C 0); linarith
    · have h1 : |rmNormSq (G s) x| ≤ C := by
        have h := hC (s, x) ⟨hs, mem_univ x⟩
        rwa [Real.norm_eq_abs] at h
      have h2 : rmNormSq (G s) x ≤ max C 0 :=
        le_trans (le_trans (le_abs_self _) h1) (le_max_left _ _)
      have h3 : frobNorm (rmC (G s) x) = Real.sqrt (rmNormSq (G s) x) := by
        rw [frobNorm, rmNormSq, frobSq_eq_frobDot_self]
      rw [h3]
      have h4 : Real.sqrt (rmNormSq (G s) x) ≤ Real.sqrt (max C 0) := Real.sqrt_le_sqrt h2
      have h5 : Real.sqrt (max C 0) ≤ Real.sqrt (max C 0) + 1 := by
        linarith [Real.sqrt_nonneg (max C 0)]
      linarith

end Work.Diff.MP
