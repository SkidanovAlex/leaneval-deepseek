/-
**The weak gradient of a viscosity solution of `σ₂ = 1` with `Δu ≥ 0`**, derived from
Trudinger--Wang's weighted interior gradient estimate (`Submission.GradientEstimateInput`).

The paper (Shankar--Yuan, §3 and the appendix) obtains the weak gradient of the limit function not
from Chaudhuri--Trudinger's Hessian measure theorem `[CT]` but from the gradient estimate `[TW]`:
a viscosity solution of `σ₂ = 1` with `Δu ≥ 0` is locally Lipschitz, hence (Rademacher) almost
everywhere differentiable, and the a.e. derivative is a weak gradient (integration by parts along
lines).  Consequently the Chaudhuri--Trudinger input can be weakened to a statement about the
*Hessian measure* only (`Submission.HessianMeasureInput`), which is exactly the content of
``[CT]`` Theorem 2.4.

Contents:
* `Submission.gradOf` — the a.e. derivative `x ↦ (toDual ℝ ℝ⁴).symm (fderiv ℝ g x)`;
* `Submission.exists_lipschitzOn_of_gradientEstimate` — local Lipschitzness of `g` from `[TW]`;
* `Submission.locallyIntegrable_gradOf_indicator` — `L¹_loc` of the truncated gradient;
* `Submission.hasWeakGradient_gradOf_indicator` — the weak gradient identity.
-/
import Mathlib
import Submission.WeakDerivative
import Submission.AlexandrovInputs
import Submission.AlexandrovQuad
import Submission.AlexandrovSlope
import Submission.TaylorCore
import Submission.Commons.Analysis.Asymptotics.isLittleO_of_sup_ball_bound

open HessianEstimates
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The candidate weak gradient of `g`: the almost everywhere Fréchet derivative, read as a vector
through the Riesz isomorphism `InnerProductSpace.toDual ℝ ℝ⁴`. -/
noncomputable def gradOf (g : ℝ⁴ → ℝ) : ℝ⁴ → ℝ⁴ :=
  fun x => (InnerProductSpace.toDual ℝ ℝ⁴).symm (fderiv ℝ g x)

theorem measurable_gradOf (g : ℝ⁴ → ℝ) : Measurable (gradOf g) := by
  unfold gradOf
  exact ((LinearIsometryEquiv.lipschitz _).continuous.measurable).comp (measurable_fderiv ℝ g)

theorem norm_gradOf (g : ℝ⁴ → ℝ) (x : ℝ⁴) :
    ‖gradOf g x‖ = ‖fderiv ℝ g x‖ := by
  unfold gradOf
  exact LinearIsometryEquiv.norm_map _ _

/-- **Local Lipschitzness of a viscosity solution of `σ₂ = 1` with `Δu ≥ 0`**, from Trudinger--Wang's
weighted interior gradient estimate: for every compact `K ⊆ ball 0 3` there is an open
`U ⊇ K`, `U ⊆ ball 0 3`, on which `g` is Lipschitz. -/
theorem exists_lipschitzOn_of_gradientEstimate (hG : GradientEstimateInput)
    {g : ℝ⁴ → ℝ} (hgcont : ContinuousOn g (closedBall 0 3))
    (hgsol : IsViscSolution (fun N => -Gop N) g (ball 0 3))
    (hgΔ : IsViscSubsolution negTrace g (ball 0 3))
    {K : Set ℝ⁴} (hK : IsCompact K) (hKsub : K ⊆ ball 0 3) :
    ∃ (U : Set ℝ⁴) (C : NNReal), IsOpen U ∧ K ⊆ U ∧ U ⊆ ball 0 3 ∧ LipschitzOnWith C g U := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hG
  obtain ⟨δ, hδpos, hδsub⟩ := hK.exists_cthickening_subset_open isOpen_ball hKsub
  have hδ4 : (0:ℝ) < δ/4 := by linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℝ⁴) 3).exists_bound_of_continuousOn hgcont
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 (by simp))
  have hInt : IntegrableOn (fun w : ℝ⁴ => |g w|) (closedBall 0 3) (volume : Measure ℝ⁴) :=
    (hgcont.integrableOn_compact (isCompact_closedBall (0:ℝ⁴) 3) (μ := volume)).abs
  set I : ℝ := ∫ w in closedBall (0:ℝ⁴) 3, |g w| with hI
  have hInn : 0 ≤ I := integral_nonneg fun w => abs_nonneg _
  have hgcont' : ContinuousOn g (ball 0 3) := hgcont.mono ball_subset_closedBall
  set C' : ℝ := max (C₀ * I / (δ/4)^5) (8*M/δ) with hC'
  have hC'nn : 0 ≤ C' := le_max_of_le_left (div_nonneg (mul_nonneg hC₀pos.le hInn) (by positivity))
  refine ⟨thickening (δ/4) K, Real.toNNReal C', isOpen_thickening, ?_, ?_, ?_⟩
  · exact self_subset_thickening hδ4 K
  · intro y hy
    exact hδsub (cthickening_mono (by linarith : δ/4 ≤ δ) K
      (thickening_subset_cthickening (δ/4) K hy))
  · refine LipschitzOnWith.of_dist_le_mul ?_
    intro y hy z hz
    rw [Real.dist_eq, Real.coe_toNNReal C' hC'nn]
    rcases eq_or_ne y z with rfl | hyz
    · simp
    rcases le_or_gt (dist y z) (δ/4) with hle | hgt
    · obtain ⟨k, hkK, hyk⟩ := (mem_thickening_iff.mp hy)
      have hball : closedBall y (2*(δ/4)) ⊆ ball 0 3 := by
        intro w hw
        rw [mem_closedBall] at hw
        have hlt : dist w k < δ := by
          have h1 : dist w y ≤ δ/2 := by linarith [hw, hδpos]
          linarith [dist_triangle w y k, hyk]
        exact hδsub (thickening_subset_cthickening δ K (by
          rw [mem_thickening_iff]; exact ⟨k, hkK, hlt⟩))
      have hIle : ∫ w in ball y (2*(δ/4)), |g w| ≤ I := by
        rw [hI]
        refine setIntegral_mono_set hInt (Eventually.of_forall fun w => abs_nonneg _) ?_
        filter_upwards with w hw
        exact ball_subset_closedBall (hball (ball_subset_closedBall hw))
      have hzy : dist z y ≤ δ/4 := by rwa [dist_comm]
      have hz' : z ∈ closedBall y (δ/4) := by rw [mem_closedBall]; exact hzy
      have hy' : y ∈ closedBall y (δ/4) := by rw [mem_closedBall, dist_self]; exact hδ4.le
      have hineq := hC₀ g (ball 0 3) isOpen_ball hgcont' hgsol hgΔ y (δ/4) hδ4 hball y hy' z hz' hyz
      have hineq2 : (δ/4)^5 * |g y - g z| / dist y z ≤ C₀ * I :=
        le_trans hineq (mul_le_mul_of_nonneg_left hIle hC₀pos.le)
      have hd : 0 < dist y z := dist_pos.mpr hyz
      have h5 : 0 < (δ/4)^5 := by positivity
      rw [div_le_iff₀ hd] at hineq2
      have hstep : |g y - g z| ≤ C₀ * I * dist y z / (δ/4)^5 := by
        rw [le_div_iff₀ h5]; linarith
      calc |g y - g z| ≤ C₀ * I * dist y z / (δ/4)^5 := hstep
        _ = (C₀ * I / (δ/4)^5) * dist y z := by ring
        _ ≤ C' * dist y z :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    · have hy3 : y ∈ closedBall 0 3 := ball_subset_closedBall
        (hδsub (cthickening_mono (by linarith : δ/4 ≤ δ) K
          (thickening_subset_cthickening (δ/4) K hy)))
      have hz3 : z ∈ closedBall 0 3 := ball_subset_closedBall
        (hδsub (cthickening_mono (by linarith : δ/4 ≤ δ) K
          (thickening_subset_cthickening (δ/4) K hz)))
      have h1 : |g y| ≤ M := by simpa [Real.norm_eq_abs] using hM y hy3
      have h2 : |g z| ≤ M := by simpa [Real.norm_eq_abs] using hM z hz3
      have h3 : |g y - g z| ≤ 2 * M := by
        calc |g y - g z| = |g y + (-g z)| := by rw [sub_eq_add_neg]
          _ ≤ |g y| + |-g z| := abs_add_le _ _
          _ = |g y| + |g z| := by rw [abs_neg]
          _ ≤ M + M := add_le_add h1 h2
          _ = 2 * M := by ring
      have h4 : 2 * M ≤ (8*M/δ) * dist y z := by
        have hdeq : (8*M/δ) * (δ/4) = 2 * M := by field_simp; ring
        rw [← hdeq]
        exact mul_le_mul_of_nonneg_left hgt.le (div_nonneg (by linarith) hδpos.le)
      exact le_trans h3 (le_trans h4 (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))

/-- Convenience form of `exists_lipschitzOn_of_gradientEstimate` with the hypotheses bundled. -/
theorem exists_lipschitzOn_of_gradientEstimate' {g : ℝ⁴ → ℝ} (hG : GradientEstimateInput)
    (hgcont : ContinuousOn g (closedBall 0 3))
    (hgsol : IsViscSolution (fun N => -Gop N) g (ball 0 3))
    (hgΔ : IsViscSubsolution negTrace g (ball 0 3)) :
    ∀ K : Set ℝ⁴, IsCompact K → K ⊆ ball 0 3 →
      ∃ (U : Set ℝ⁴) (C : NNReal), IsOpen U ∧ K ⊆ U ∧ U ⊆ ball 0 3 ∧ LipschitzOnWith C g U :=
  fun K hK hKsub => exists_lipschitzOn_of_gradientEstimate hG hgcont hgsol hgΔ hK hKsub

/-- The truncated a.e. derivative `(ball 0 (1/2)).indicator (gradOf g)` is locally integrable,
provided `g` is locally Lipschitz on `ball 0 3`. -/
theorem locallyIntegrable_gradOf_indicator {g : ℝ⁴ → ℝ}
    (hLip : ∀ K : Set ℝ⁴, IsCompact K → K ⊆ ball 0 3 →
      ∃ (U : Set ℝ⁴) (C : NNReal), IsOpen U ∧ K ⊆ U ∧ U ⊆ ball 0 3 ∧ LipschitzOnWith C g U) :
    LocallyIntegrable ((ball 0 (1/2)).indicator (gradOf g)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hK' : IsCompact (K ∩ closedBall (0:ℝ⁴) (1/2)) :=
    hK.inter (isCompact_closedBall _ _)
  have hK'sub : K ∩ closedBall (0:ℝ⁴) (1/2) ⊆ ball 0 3 := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    have h1 : ‖x‖ ≤ 1/2 := by
      have h2 := hx.2
      rw [mem_closedBall, dist_zero_right] at h2
      exact h2
    linarith
  obtain ⟨U, C, hUopen, hK'U, hUsub, hLipU⟩ := hLip _ hK' hK'sub
  have hbdd : ∀ x ∈ K, ‖(ball (0:ℝ⁴) (1/2)).indicator (gradOf g) x‖ ≤ (C : ℝ) := by
    intro x hx
    by_cases hxball : x ∈ ball (0:ℝ⁴) (1/2)
    · rw [Set.indicator_of_mem hxball, norm_gradOf]
      exact norm_fderiv_le_of_lipschitzOn ℝ
        (hUopen.mem_nhds (hK'U ⟨hx, ball_subset_closedBall hxball⟩)) hLipU
    · rw [Set.indicator_of_notMem hxball, norm_zero]
      exact C.2
  have hmeas : Measurable ((ball (0:ℝ⁴) (1/2)).indicator (gradOf g)) :=
    (measurable_gradOf g).indicator measurableSet_ball
  refine IntegrableOn.of_bound (hK.measure_lt_top) hmeas.aestronglyMeasurable (C : ℝ) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hbdd x hx

/-- The truncated a.e. derivative is a weak gradient of `g` on `ball 0 (1/2)`. -/
theorem hasWeakGradient_gradOf_indicator {g : ℝ⁴ → ℝ}
    (hLip : ∀ K : Set ℝ⁴, IsCompact K → K ⊆ ball 0 3 →
      ∃ (U : Set ℝ⁴) (C : NNReal), IsOpen U ∧ K ⊆ U ∧ U ⊆ ball 0 3 ∧ LipschitzOnWith C g U) :
    HasWeakGradient g (ball 0 (1/2)) ((ball 0 (1/2)).indicator (gradOf g)) := by
  intro φ hφ hsupp v
  have hKsub : tsupport φ ⊆ ball 0 3 := fun x hx => by
    have h1 : x ∈ ball (0:ℝ⁴) (1/2) := hsupp hx
    rw [mem_ball, dist_zero_right] at h1 ⊢
    linarith
  have hφc : HasCompactSupport φ := by
    rw [HasCompactSupport]
    exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, isBounded_ball.subset hKsub⟩
  obtain ⟨U, C, hUopen, hKU, hUsub, hLipU⟩ := hLip _ hφc hKsub
  have hbddU : Bornology.IsBounded U := isBounded_ball.subset hUsub
  have hmain := HasWeakGradient.of_lipschitzOn (u := g) (s := U) hUopen hbddU hLipU φ hφ hKU v
  rw [hmain]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show φ x * ⟪(InnerProductSpace.toDual ℝ ℝ⁴).symm (fderiv ℝ g x), v⟫
      = φ x * ⟪(ball (0:ℝ⁴) (1/2)).indicator (gradOf g) x, v⟫
  by_cases hx : x ∈ tsupport φ
  · rw [Set.indicator_of_mem (hsupp hx)]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

end Submission
