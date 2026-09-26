import Mathlib
import Submission.Work.Smooth.SphereJordan.jsepDefs
import Submission.Work.Smooth.SphereJordan.thetaFoundation
import Submission.Work.Smooth.Jordan.plane_separation_preconnected_subset

/-!
# The unbounded side contains everything outside a ball containing the trace

For a Jordan separation datum `S : JSep γ` of a simple closed plane curve `γ` and any closed ball
`Metric.closedBall c ρ` of positive radius which contains the trace of `γ`, every point outside that
ball lies on the *unbounded* side `S.U`.

The mathematics is elementary and uses only three of the fields of `JSep`:

* far away (beyond a radius exceeding both `γ.trace` and the bounded side `S.V`) every point is on
  the unbounded side (`JSep.exists_norm_lt_imp_mem_U`);
* the complement of a closed ball of positive radius is preconnected
  (`isPreconnected_compl_closedBall`, an image of the preconnected exterior of the unit disc);
* since that complement is preconnected, is disjoint from the trace (the trace sits inside the
  ball) and is covered by the two disjoint open sides, it lies entirely in one of them; it cannot
  lie in the bounded side because it contains points arbitrarily far away, hence it lies in `U`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **Far points lie on the unbounded side.** For a Jordan separation datum of `γ` there is a radius
`M` beyond which every point of the plane belongs to the unbounded side `U`: such a point is off the
(bounded) trace, and it cannot lie on the (bounded) bounded side `V`. -/
theorem JSep.exists_norm_lt_imp_mem_U {γ : Work.Smooth.Jordan.PlaneCurve} (S : JSep γ) :
    ∃ M : ℝ, ∀ z : ℂ, M < ‖z‖ → z ∈ S.U := by
  obtain ⟨MV, hV⟩ := S.bounded_V.subset_closedBall (0 : ℂ)
  obtain ⟨MT, hT⟩ := γ.isCompact_trace.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max MV MT, fun z hz => ?_⟩
  have hzV : z ∉ S.V := fun h => by
    have h1 := hV h
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith [le_max_left MV MT]
  have hzT : z ∉ γ.trace := fun h => by
    have h1 := hT h
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith [le_max_right MV MT]
  have hmem : z ∈ S.U ∪ S.V := by
    rw [S.union_eq, Set.mem_compl_iff]
    exact hzT
  exact hmem.elim id (fun h => absurd h hzV)

/-- **The complement of a closed ball of positive radius is preconnected**: it is the image of the
preconnected exterior `{w : ℂ | ρ < ‖w‖}` of the disc of radius `ρ` under the continuous translation
`w ↦ w + c`. -/
theorem isPreconnected_compl_closedBall (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected (Metric.closedBall c ρ)ᶜ := by
  have hpre : IsPreconnected {w : ℂ | ρ < ‖w‖} := isPreconnected_far hρ
  have himg : IsPreconnected ((fun w : ℂ => w + c) '' {w : ℂ | ρ < ‖w‖}) :=
    hpre.image _ ((continuous_id.add continuous_const).continuousOn)
  have heq : (fun w : ℂ => w + c) '' {w : ℂ | ρ < ‖w‖} = (Metric.closedBall c ρ)ᶜ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le]
      simpa using hv
    · intro hw
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] at hw
      exact ⟨w - c, by simpa using hw, by simp⟩
  rw [heq] at himg
  exact himg

theorem jsepExterior {γ : Work.Smooth.Jordan.PlaneCurve} (S : Work.Smooth.SphereJordan.JSep γ)
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : γ.trace ⊆ Metric.closedBall c ρ) :
    (Metric.closedBall c ρ)ᶜ ⊆ S.U := by
  have hWpre : IsPreconnected (Metric.closedBall c ρ)ᶜ :=
    isPreconnected_compl_closedBall c hρ
  have hWsub : (Metric.closedBall c ρ)ᶜ ⊆ γ.traceᶜ := by
    intro w hw hwt
    have h1 := hsub hwt
    rw [Metric.mem_closedBall, dist_eq_norm] at h1
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] at hw
    linarith
  have hWUV : (Metric.closedBall c ρ)ᶜ ⊆ S.U ∪ S.V := fun w hw => by
    rw [S.union_eq, Set.mem_compl_iff]
    exact hWsub hw
  obtain ⟨M, hM⟩ := S.exists_norm_lt_imp_mem_U
  set A : ℝ := max M 0 + ‖c‖ + ρ + 1 with hAdef
  set q : ℂ := c + (A : ℂ) with hqdef
  have hApos : 0 < A := by
    rw [hAdef]
    have hc := norm_nonneg c
    have hmax0 : 0 ≤ max M 0 := le_max_right M 0
    linarith
  have hqW : q ∈ (Metric.closedBall c ρ)ᶜ := by
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le]
    have hqc : q - c = (A : ℂ) := by rw [hqdef]; ring
    rw [hqc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
    rw [hAdef]
    have hc := norm_nonneg c
    have hM0 : M ≤ max M 0 := le_max_left _ _
    have hmax0 : 0 ≤ max M 0 := le_max_right M 0
    linarith
  have hqq : M < ‖q‖ := by
    have hb : ‖q - c‖ ≤ ‖q‖ + ‖c‖ := norm_sub_le q c
    have hqc : q - c = (A : ℂ) := by rw [hqdef]; ring
    have hA : ‖(A : ℂ)‖ = A := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
    rw [hqc, hA, hAdef] at hb
    have hc := norm_nonneg c
    have hM0 : M ≤ max M 0 := le_max_left _ _
    linarith
  rcases hWpre.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV hWUV with hU | hV
  · exact hU
  · exact absurd (hV hqW) (Set.disjoint_left.mp S.disjoint_UV (hM q hqq))

end

end Work.Smooth.SphereJordan
