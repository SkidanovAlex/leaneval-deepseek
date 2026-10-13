import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS_EllLimOK.ProducerH.ThetaZero.tendsto_of_deriv_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open scoped Topology
open Filter Set

-- The hypothesis `A < B` of `eg_limit_family` is part of the requested interface but is not
-- needed by the argument (which works for any `A`, `B`); silence the unused-variable linter.
set_option linter.unusedVariables false

/-- A point of `(0, π/2)` at which `M θ` is as small as we like. -/
private lemma exists_theta_small {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 2 * (M * θ) < ε / 2 := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_lt (show (0 : ℝ) < ε / 2 by linarith) (2 * M)
  refine ⟨min (Real.pi / 4) c, ⟨lt_min (by linarith [Real.pi_pos]) hcpos, ?_⟩, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos])
  · have hle : min (Real.pi / 4) c ≤ c := min_le_right _ _
    calc 2 * (M * min (Real.pi / 4) c) = (2 * M) * min (Real.pi / 4) c := by ring
      _ ≤ (2 * M) * c := mul_le_mul_of_nonneg_left hle (by linarith [hM])
      _ < ε / 2 := hc

/-- A point of `(0, π/2)` at which `M (π/2 - θ)` is as small as we like. -/
private lemma exists_theta_close_pi {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 2 * (M * (Real.pi / 2 - θ)) < ε / 2 := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_lt (show (0 : ℝ) < ε / 2 by linarith) (2 * M)
  refine ⟨Real.pi / 2 - min (Real.pi / 4) c, ⟨?_, ?_⟩, ?_⟩
  · have hle : min (Real.pi / 4) c ≤ Real.pi / 4 := min_le_left _ _
    linarith [Real.pi_pos]
  · have hpos : 0 < min (Real.pi / 4) c := lt_min (by linarith [Real.pi_pos]) hcpos
    linarith
  · have hsub : Real.pi / 2 - (Real.pi / 2 - min (Real.pi / 4) c) = min (Real.pi / 4) c := by ring
    rw [hsub]
    have hle : min (Real.pi / 4) c ≤ c := min_le_right _ _
    calc 2 * (M * min (Real.pi / 4) c) = (2 * M) * min (Real.pi / 4) c := by ring
      _ ≤ (2 * M) * c := mul_le_mul_of_nonneg_left hle (by linarith [hM])
      _ < ε / 2 := hc

/-- **Endpoint limits of a uniformly Lipschitz family.**  Let `F : ℝ → ℝ → ℝ` be a family of
functions of `θ` which on the strip `z ∈ [A,B]`, `θ ∈ (0, π/2)` is `C¹` in `θ` with
`θ`-derivative bounded by `M`, and whose slices `z ↦ F θ z` are continuous on `[A,B]`.  Then
both one-sided θ-limits exist for every `z ∈ [A,B]`, they are approached at the optimal
Lipschitz rate `M`, and they are continuous functions of `z` on `[A,B]`. -/
theorem eg_limit_family {F : ℝ → ℝ → ℝ} {A B M : ℝ} (hAB : A < B) (hM : 0 ≤ M)
    (hcd : ∀ z ∈ Set.Icc A B, ContDiffOn ℝ 1 (fun θ => F θ z) (Set.Ioo 0 (Real.pi / 2)))
    (hderiv : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv (fun θ' => F θ' z) θ| ≤ M)
    (hcont : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousOn (fun z => F θ z) (Set.Icc A B)) :
    ∃ L R : ℝ → ℝ,
      (∀ z ∈ Set.Icc A B, Filter.Tendsto (fun θ => F θ z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (L z))) ∧
      (∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ z - L z| ≤ M * θ) ∧
      (∀ z ∈ Set.Icc A B, Filter.Tendsto (fun θ => F θ z)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (R z))) ∧
      (∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |F θ z - R z| ≤ M * (Real.pi / 2 - θ)) ∧
      ContinuousOn L (Set.Icc A B) ∧ ContinuousOn R (Set.Icc A B) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  -- ## Existence of the two one-sided limits, for every `z ∈ [A,B]`
  have hexL : ∀ z : ℝ, ∃ L : ℝ, z ∈ Set.Icc A B →
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    intro z
    by_cases hz : z ∈ Set.Icc A B
    · obtain ⟨L, hL⟩ := (Work.FTS_EllLimOK.ProducerH.ThetaZero.tendsto_of_deriv_bounded hpi
        (hcd z hz) (hderiv z hz)).1
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hz⟩
  have hexR : ∀ z : ℝ, ∃ R : ℝ, z ∈ Set.Icc A B →
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds R) := by
    intro z
    by_cases hz : z ∈ Set.Icc A B
    · obtain ⟨R, hR⟩ := (Work.FTS_EllLimOK.ProducerH.ThetaZero.tendsto_of_deriv_bounded hpi
        (hcd z hz) (hderiv z hz)).2
      exact ⟨R, fun _ => hR⟩
    · exact ⟨0, fun h => absurd h hz⟩
  let L : ℝ → ℝ := fun z => Classical.choose (hexL z)
  let R : ℝ → ℝ := fun z => Classical.choose (hexR z)
  have hLtend : ∀ z ∈ Set.Icc A B,
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (L z)) :=
    fun z hz => Classical.choose_spec (hexL z) hz
  have hRtend : ∀ z ∈ Set.Icc A B,
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (R z)) :=
    fun z hz => Classical.choose_spec (hexR z) hz
  -- ## The family is Lipschitz in `θ` on the open strip, with the uniform constant `M`
  have hlip : ∀ z ∈ Set.Icc A B,
      LipschitzOnWith ⟨M, hM⟩ (fun θ => F θ z) (Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x hx => ?_) (fun x hx => ?_)
      (convex_Ioo 0 (Real.pi / 2))
    · exact ((hcd z hz).differentiableOn_one x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    · have hm : |deriv (fun θ => F θ z) x| ≤ M := hderiv z hz x hx
      exact_mod_cast hm
  -- ## The rate at `θ → 0⁺`
  have hboundL : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ z - L z| ≤ M * θ := by
    intro z hz θ hθ
    have hev : ∀ᶠ θ' in nhdsWithin (0 : ℝ) (Set.Ioi 0), |F θ' z - F θ z| ≤ M * θ := by
      filter_upwards [Ioo_mem_nhdsGT hθ.1] with θ' hθ'
      have hθ'm : θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ'.1, lt_trans hθ'.2 hθ.2⟩
      have h1 : dist (F θ' z) (F θ z) ≤ M * dist θ' θ := (hlip z hz).dist_le_mul θ' hθ'm θ hθ
      rw [Real.dist_eq, Real.dist_eq] at h1
      have h2 : |θ' - θ| = θ - θ' := by
        rw [abs_of_neg (show θ' - θ < 0 by linarith [hθ'.2])]
        ring
      rw [h2] at h1
      calc |F θ' z - F θ z| = dist (F θ' z) (F θ z) := by rw [Real.dist_eq]
        _ ≤ M * (θ - θ') := h1
        _ ≤ M * θ := by nlinarith [hM, hθ'.1]
    have hT : Filter.Tendsto (fun θ' => F θ' z - F θ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (L z - F θ z)) := (hLtend z hz).sub_const (F θ z)
    have hTabs : Filter.Tendsto (fun θ' => |F θ' z - F θ z|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds |L z - F θ z|) := by
      simpa only [Real.norm_eq_abs] using hT.norm
    have := le_of_tendsto hTabs hev
    calc |F θ z - L z| = |L z - F θ z| := abs_sub_comm _ _
      _ ≤ M * θ := this
  -- ## The rate at `θ → (π/2)⁻`
  have hboundR : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |F θ z - R z| ≤ M * (Real.pi / 2 - θ) := by
    intro z hz θ hθ
    have hev : ∀ᶠ θ' in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        |F θ' z - F θ z| ≤ M * (Real.pi / 2 - θ) := by
      filter_upwards [Ioo_mem_nhdsLT hθ.2] with θ' hθ'
      have hθ'm : θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨lt_trans hθ.1 hθ'.1, hθ'.2⟩
      have h1 : dist (F θ' z) (F θ z) ≤ M * dist θ' θ := (hlip z hz).dist_le_mul θ' hθ'm θ hθ
      rw [Real.dist_eq, Real.dist_eq] at h1
      have h2 : |θ' - θ| = θ' - θ := abs_of_pos (show 0 < θ' - θ by linarith [hθ'.1])
      rw [h2] at h1
      calc |F θ' z - F θ z| = dist (F θ' z) (F θ z) := by rw [Real.dist_eq]
        _ ≤ M * (θ' - θ) := h1
        _ ≤ M * (Real.pi / 2 - θ) := by nlinarith [hM, hθ'.2]
    have hT : Filter.Tendsto (fun θ' => F θ' z - F θ z)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (R z - F θ z)) :=
      (hRtend z hz).sub_const (F θ z)
    have hTabs : Filter.Tendsto (fun θ' => |F θ' z - F θ z|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds |R z - F θ z|) := by
      simpa only [Real.norm_eq_abs] using hT.norm
    have := le_of_tendsto hTabs hev
    calc |F θ z - R z| = |R z - F θ z| := abs_sub_comm _ _
      _ ≤ M * (Real.pi / 2 - θ) := this
  -- ## Continuity of the limit functions on `[A,B]`
  have hcontL : ContinuousOn L (Set.Icc A B) := by
    intro z hz
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨θ₀, hθ₀, hθ₀s⟩ := exists_theta_small hM hε
    have hcw : ContinuousWithinAt (fun z => F θ₀ z) (Set.Icc A B) z :=
      (hcont θ₀ hθ₀).continuousWithinAt hz
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδpos, hδ⟩ := hcw (ε / 2) (by linarith)
    refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
    have h1 : |F θ₀ z' - F θ₀ z| < ε / 2 := by
      have := hδ hz' hdist
      rwa [Real.dist_eq] at this
    have h2 : |F θ₀ z - L z| ≤ M * θ₀ := hboundL z hz θ₀ hθ₀
    have h3 : |F θ₀ z' - L z'| ≤ M * θ₀ := hboundL z' hz' θ₀ hθ₀
    rw [Real.dist_eq]
    have hsplit : L z' - L z
        = (L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - L z) := by ring
    rw [hsplit]
    calc |(L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - L z)|
        ≤ |(L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)| + |F θ₀ z - L z| :=
          abs_add_le ((L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)) (F θ₀ z - L z)
      _ ≤ (|L z' - F θ₀ z'| + |F θ₀ z' - F θ₀ z|) + |F θ₀ z - L z| := by
          have h := abs_add_le (L z' - F θ₀ z') (F θ₀ z' - F θ₀ z)
          linarith
      _ < ε := by
          have h3' : |L z' - F θ₀ z'| ≤ M * θ₀ := by
            rw [abs_sub_comm (L z') (F θ₀ z')]
            exact h3
          linarith
  have hcontR : ContinuousOn R (Set.Icc A B) := by
    intro z hz
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨θ₀, hθ₀, hθ₀s⟩ := exists_theta_close_pi hM hε
    have hcw : ContinuousWithinAt (fun z => F θ₀ z) (Set.Icc A B) z :=
      (hcont θ₀ hθ₀).continuousWithinAt hz
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδpos, hδ⟩ := hcw (ε / 2) (by linarith)
    refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
    have h1 : |F θ₀ z' - F θ₀ z| < ε / 2 := by
      have := hδ hz' hdist
      rwa [Real.dist_eq] at this
    have h2 : |F θ₀ z - R z| ≤ M * (Real.pi / 2 - θ₀) := hboundR z hz θ₀ hθ₀
    have h3 : |F θ₀ z' - R z'| ≤ M * (Real.pi / 2 - θ₀) := hboundR z' hz' θ₀ hθ₀
    rw [Real.dist_eq]
    have hsplit : R z' - R z
        = (R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - R z) := by ring
    rw [hsplit]
    calc |(R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - R z)|
        ≤ |(R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)| + |F θ₀ z - R z| :=
          abs_add_le ((R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)) (F θ₀ z - R z)
      _ ≤ (|R z' - F θ₀ z'| + |F θ₀ z' - F θ₀ z|) + |F θ₀ z - R z| := by
          have h := abs_add_le (R z' - F θ₀ z') (F θ₀ z' - F θ₀ z)
          linarith
      _ < ε := by
          have h3' : |R z' - F θ₀ z'| ≤ M * (Real.pi / 2 - θ₀) := by
            rw [abs_sub_comm (R z') (F θ₀ z')]
            exact h3
          linarith
  exact ⟨L, R, hLtend, hboundL, hRtend, hboundR, hcontL, hcontR⟩

end Work.FTS_EllLimOK.ProducerH.H2
