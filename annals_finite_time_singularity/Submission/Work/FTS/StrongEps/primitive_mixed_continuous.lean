import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsSlotAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem primitive_mixed_continuous {W : ℝ → ℝ → ℝ → ℝ} {T a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (W s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (W s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), ∀ q : ℝ × ℝ, q ∈ K →
        |Work.Spaces.mixed k l (W s) q.1 q.2| ≤ B)
    (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => ∫ s in a..b, Work.Spaces.mixed j i (W s) q.1 q.2)
      Work.FTS.EllipticEst.Q0 := by
  -- The integral is a limit of the parametric integrals `q ↦ ∫ s in a..b, mixed j i (W s) q.1 q.2`
  -- along the filter `𝓝[Q0] q₀`; dominated convergence applies because on a compact
  -- neighbourhood `K ⊆ Q0` of `q₀` all the slots `mixed k l (W s)` are uniformly bounded in
  -- `s ∈ [0,T]` by `hbdd`, and pointwise in `s` they are continuous on `Q0`.
  intro q₀ hq₀
  -- `uIoc a b` sits inside the interval `[0,T]` on which all the hypotheses are available.
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro x hx
    simp only [Set.uIoc, Set.mem_Ioc] at hx
    exact ⟨le_trans (le_min ha.1 hb.1) hx.1.le, le_trans hx.2 (max_le ha.2 hb.2)⟩
  -- A compact neighbourhood of `q₀` inside the open quadrant.
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq₀)
  set K : Set (ℝ × ℝ) := Metric.closedBall q₀ (ε / 2) with hKdef
  have hKc : IsCompact K := isCompact_closedBall q₀ (ε / 2)
  have hKQ : K ⊆ Work.FTS.EllipticEst.Q0 := fun q hq =>
    hεK (Metric.closedBall_subset_ball (by linarith) hq)
  have hKmem : K ∈ 𝓝 q₀ := Metric.closedBall_mem_nhds q₀ (by linarith)
  obtain ⟨B, hB0, hB⟩ := hbdd K hKc hKQ
  have hmain := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := a) (b := b) (l := 𝓝[Work.FTS.EllipticEst.Q0] q₀)
    (F := fun q : ℝ × ℝ => fun x : ℝ => Work.Spaces.mixed j i (W x) q.1 q.2)
    (f := fun x : ℝ => Work.Spaces.mixed j i (W x) q₀.1 q₀.2)
    (bound := fun _ => B)
    ?_ ?_ ?_ ?_
  · exact hmain
  · -- measurability in `s`, transferred from the restriction to `[0,T]`
    filter_upwards [self_mem_nhdsWithin (s := Work.FTS.EllipticEst.Q0) (a := q₀)] with q hq
    exact (hmeas j i q.1 q.2 hq).mono_measure (Measure.restrict_mono hsub le_rfl)
  · -- the uniform domination on the compact `K`
    filter_upwards [Filter.mem_inf_of_left hKmem] with q hq
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hxT : x ∈ Set.Icc (0 : ℝ) T := hsub hx
    simpa only [Real.norm_eq_abs] using hB x hxT j i q hq
  · exact intervalIntegrable_const
  · -- pointwise convergence in `s`, from continuity of the slots on `Q0`
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hxT : x ∈ Set.Icc (0 : ℝ) T := hsub hx
    exact (((hsm x hxT).mixed j i).continuousOn).continuousWithinAt hq₀

end Work.FTS.StrongEps
