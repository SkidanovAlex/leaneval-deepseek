import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Identification of the a.e. limit of the level-5 slots with the mixed derivative of the limit

`Work.FTS.StrongEps.LocUnif.D5.ae_limit_eq_deriv`: let a sequence `L n` converge uniformly to
`Llim` on a closed box `[a₀,b₀] × [c,d]`, let `W n` be the `z`-derivative of `L n` on the smaller
box `[a,b] × [c,d]` (where `a₀ < a < b < b₀`), and let `w` be an a.e. limit of `W n` whose slices
converge in `L¹([a,b])` for a.e. angle `θ`.  Then `w` agrees a.e. with the (totalised) partial
derivative `∂_z Llim`.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Two elementary helpers -/

/-- **The `ε`-`δ` form of `HasDerivAt`.** -/
theorem exists_delta_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < |y - x| → |y - x| < δ →
      |(f y - f x) / (y - x) - f'| < ε := by
  rw [hasDerivAt_iff_tendsto_slope] at h
  rw [Metric.tendsto_nhds] at h
  have h2 : ∀ᶠ y in 𝓝 x, y ≠ x → dist (slope f x y) f' < ε := by
    have h3 := h ε hε
    rwa [eventually_nhdsWithin_iff] at h3
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp h2
  refine ⟨δ, hδpos, fun y hy hyδ => ?_⟩
  have hyball : y ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hyδ
  have hyne : y ≠ x := by
    intro hyx
    rw [hyx, sub_self, abs_zero] at hy
    exact absurd hy (lt_irrefl 0)
  have h4 := hδ hyball hyne
  rw [slope_def_field, Real.dist_eq] at h4
  simpa [abs_sub_comm] using h4

/-- **A bound valid at all rational points of an open set extends to the whole set**, by density
of `ℚ` and continuity. -/
theorem abs_le_of_forall_rat_of_continuousOn {g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hg : ContinuousOn g s) {c : ℝ} (h : ∀ q : ℚ, (q : ℝ) ∈ s → |g (q : ℝ)| ≤ c) :
    ∀ x ∈ s, |g x| ≤ c := by
  intro x hx
  by_contra hcon
  push Not at hcon
  have hopen : IsOpen (s ∩ (fun y : ℝ => |g y|) ⁻¹' (Set.Ioi c)) :=
    hg.abs.isOpen_inter_preimage hs isOpen_Ioi
  have hmem : x ∈ s ∩ (fun y : ℝ => |g y|) ⁻¹' (Set.Ioi c) := ⟨hx, hcon⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen x hmem
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + δ by linarith)
  have hqmem : (q : ℝ) ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hq' := hδ hqmem
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi] at hq'
  exact absurd (h q hq'.1) (not_le.mpr hq'.2)

end Work.FTS.StrongEps.LocUnif.D5
