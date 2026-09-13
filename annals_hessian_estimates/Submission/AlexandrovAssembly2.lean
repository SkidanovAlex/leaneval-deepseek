/-
Proposition 3.1 of Shankar--Yuan, with the Chaudhuri--Trudinger input weakened to the **Hessian
measure only** (`Submission.HessianMeasureInput`): the weak gradient is derived from
Trudinger--Wang's gradient estimate (`Submission.GradientEstimateInput`) in
`Submission.GradFromGradient`.

This matches the paper exactly: `[CT]` supplies the Hessian measure, `[TW]` supplies the gradient
bound (hence, via Rademacher and integration by parts along lines, the weak gradient).
-/
import Mathlib
import Submission.HessianMeasureInput
import Submission.GradFromGradient
import Submission.AlexandrovAssembly

open HessianEstimates
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- **Proposition 3.1 of Shankar--Yuan**, with the second input weakened to the Hessian measure.

Proof: `hHM` gives `M, σ` on `ball 0 3` (the `2`-convexity hypothesis is
`isTwoConvexOn_of_viscSolution`).  The weak gradient on the smaller ball `ball 0 (1/2)` is the
truncated a.e. derivative `G = 1_{ball 0 (1/2)} gradOf g`, which is `L¹_loc` because `g` is
Lipschitz on compact subsets of `ball 0 3` (`exists_lipschitzOn_of_gradientEstimate`, from `[TW]`),
and is a weak gradient by integration by parts for Lipschitz functions
(`hasWeakGradient_gradOf_indicator`).  From there the proof is the one of
`Submission.alexandrovInput_holds`: the a.e. conditions, the slope estimate `(point)`
(`Submission.point_estimate`), the analytic core `lem:o(r²)` (`hT`) and the maximum principle
`lem:pto(r²)`. -/
theorem alexandrovInput_holds' (hG : GradientEstimateInput) (hHM : HessianMeasureInput)
    (hT : TaylorCoreInput) : AlexandrovInput := by
  intro g hgcont hgsol hgΔ
  have hc : (1:ℝ)/2 < 3 := by norm_num
  have hsub : ball (0:ℝ⁴) (1/2) ⊆ ball 0 3 := ball_subset_ball hc.le
  have hgcont3 : ContinuousOn g (ball 0 3) := hgcont.mono ball_subset_closedBall
  have h2cv : IsTwoConvexOn g (ball 0 3) := isTwoConvexOn_of_viscSolution isOpen_ball hgsol.1 hgΔ
  have hclB : closure (ball (0 : ℝ⁴) (1/2)) ⊆ ball 0 3 := by
    intro x hx
    rw [closure_ball (0 : ℝ⁴) (by norm_num), Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  obtain ⟨M, σ, hMli, hσsing, hwh⟩ :=
    hHM g (ball 0 3) isOpen_ball (isBounded_ball) hgcont3 h2cv (ball 0 (1/2)) isOpen_ball hclB
  have hLip := exists_lipschitzOn_of_gradientEstimate' hG hgcont hgsol hgΔ
  set G : ℝ⁴ → ℝ⁴ := (ball (0:ℝ⁴) (1/2)).indicator (gradOf g) with hGdef
  have hGli : LocallyIntegrable G volume := by
    rw [hGdef]; exact locallyIntegrable_gradOf_indicator hLip
  have hwg : HasWeakGradient g (ball 0 (1/2)) G := by
    rw [hGdef]; exact hasWeakGradient_gradOf_indicator hLip
  -- ## the three a.e. conditions
  have hae : ∀ᵐ x ∂(volume : Measure ℝ⁴), IsLebesguePointVec G x
      ∧ (∀ i j, IsLebesguePoint (M i j) x)
      ∧ (∀ i j, IsVanishingPoint (σ i j).totalVariation x) := by
    filter_upwards [Commons.Measure.Lebesgue.ae_isLebesguePoint_vec hGli,
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
        Commons.Measure.Lebesgue.ae_isLebesguePoint (hMli i j),
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
        Commons.Measure.Lebesgue.ae_isVanishingPoint (hσsing i j)]
      with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hpos : (volume : Measure ℝ⁴) (ball (0 : ℝ⁴) (1 / 3)) ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos volume 0 (by norm_num))
  obtain ⟨x₀, hx₀ball, hx₀⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (MeasureTheory.ae_mono Measure.restrict_le_self hae)
  obtain ⟨hGleb, hMleb, hσvan⟩ := hx₀
  have hx₀norm : ‖x₀‖ < 1 / 3 := by
    have h := hx₀ball
    rw [mem_ball, dist_zero_right] at h
    exact h
  have hx₀s : x₀ ∈ ball (0:ℝ⁴) (1/2) := by rw [mem_ball, dist_zero_right]; linarith
  have hx₀3 : x₀ ∈ ball (0:ℝ⁴) 3 := by rw [mem_ball, dist_zero_right]; linarith
  -- ## the pointwise slope estimate
  obtain ⟨A, hApos, hA⟩ := point_estimate hG hgcont hgsol hgΔ x₀
  have hR : 0 < 3 - ‖x₀‖ := by linarith
  -- ## the `L¹` average bound (the analytic core)
  set g₁ : ℝ⁴ → ℝ := (Metric.closedBall (0 : ℝ⁴) 3).indicator g with hg₁
  have hg₁g : ∀ x ∈ Metric.closedBall (0 : ℝ⁴) 3, g₁ x = g x := by
    intro x hx
    rw [hg₁]
    exact Set.indicator_of_mem hx g
  have hg₁int : Integrable g₁ volume := by
    rw [hg₁]
    exact (integrable_indicator_iff measurableSet_closedBall).mpr
      (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ⁴) 3) hgcont)
  have hg₁li : LocallyIntegrable g₁ volume := hg₁int.locallyIntegrable
  have hg₁cont : ContinuousOn g₁ (ball (0:ℝ⁴) (1/2)) :=
    hgcont3.congr_mono (fun x hx => hg₁g x (ball_subset_closedBall (hsub hx))) hsub
  have hwg₁ : HasWeakGradient g₁ (ball (0:ℝ⁴) (1/2)) G :=
    HasWeakGradient.congr_of_eqOn hwg (fun x hx => (hg₁g x (ball_subset_closedBall (hsub hx))).symm)
  have hwh₁ : HasWeakHessian g₁ (ball (0:ℝ⁴) (1/2)) M σ :=
    HasWeakHessian.congr_of_eqOn hwh (fun x hx => (hg₁g x (ball_subset_closedBall (hsub hx))).symm)
  have hTay₁ := hT g₁ (ball (0:ℝ⁴) (1/2)) x₀ isOpen_ball hx₀s hg₁cont hg₁li G M σ hGli hMli
    hwg₁ hwh₁ hGleb hMleb hσvan
  have hx₀cl : x₀ ∈ Metric.closedBall (0 : ℝ⁴) 3 := ball_subset_closedBall hx₀3
  have hTay : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫ y in ball x₀ r, |taylorRemainder g G M x₀ y|) / (volume (ball x₀ r)).toReal
        ≤ ε * r ^ 2 := by
    intro ε hε
    filter_upwards [hTay₁ ε hε, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr hrlt
    refine le_of_eq_of_le ?_ hr
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hy3 : y ∈ Metric.closedBall (0 : ℝ⁴) 3 := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have h1 : ‖y‖ ≤ ‖y - x₀‖ + ‖x₀‖ := by
        calc ‖y‖ = ‖(y - x₀) + x₀‖ := congrArg (fun u => ‖u‖) (by abel)
          _ ≤ _ := norm_add_le _ _
      rw [dist_zero_right]
      linarith [hy, hx₀norm, hrlt.2]
    show |taylorRemainder g G M x₀ y| = |taylorRemainder g₁ G M x₀ y|
    simp only [taylorRemainder, hg₁g y hy3, hg₁g x₀ hx₀cl]
  -- ## the maximum principle `lem:pto(r^2)`
  have hsup := Commons.Measure.Lebesgue.sup_le_of_average_and_slope
    (h := fun y : ℝ⁴ => taylorRemainder g G M x₀ y) (R := 3 - ‖x₀‖)
    hApos.le hR hTay (fun r hr hrR y hy z hz hyz => hA r hr hrR y hy z hz hyz)
  -- ## rescale `r ↦ 2r` to match the form of the little-o statement
  have hsup2 : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y ∈ ball x₀ r,
      |taylorRemainder g G M x₀ y| ≤ ε * r ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp (hsup (ε / 4) (by positivity))
    have hδ' : ∀ r : ℝ, r ∈ Ioo (0 : ℝ) δ → ∀ y : ℝ⁴, y ∈ ball x₀ (r / 2) →
        |taylorRemainder g G M x₀ y| ≤ (ε / 4) * r ^ 2 := hδ
    refine (nhdsGT_basis (0 : ℝ)).eventually_iff.mpr ⟨δ / 2, by positivity, ?_⟩
    intro r hr y hy
    obtain ⟨hrpos, hrδ⟩ := hr
    have h1 : 2 * r ∈ Ioo (0 : ℝ) δ := ⟨by linarith, by linarith⟩
    have hball : (2 * r) / 2 = r := by ring
    have hmem : y ∈ ball x₀ ((2 * r) / 2) := by rwa [hball]
    have h2 := hδ' (2 * r) h1 y hmem
    have he : ε / 4 * (2 * r) ^ 2 = ε * r ^ 2 := by ring
    rwa [he] at h2
  -- ## conclusion
  refine ⟨x₀, hx₀ball, innerSL ℝ (G x₀), quadM M x₀, ?_⟩
  have hEq : (fun z : ℝ⁴ => g z - g x₀ - (innerSL ℝ (G x₀)) (z - x₀)
      - quadM M x₀ (z - x₀) (z - x₀)) = fun z => taylorRemainder g G M x₀ z := by
    funext z
    rw [taylorRemainder_eq]
  rw [hEq]
  exact Commons.Analysis.Asymptotics.isLittleO_of_sup_ball_bound
    (taylorRemainder_self g G M x₀) hsup2

end Submission
