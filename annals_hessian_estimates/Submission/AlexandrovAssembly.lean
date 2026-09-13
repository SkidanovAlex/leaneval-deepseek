/-
Proposition 3.1 of Shankar--Yuan: the assembly of the Alexandrov regularity statement from its
three inputs (`Submission.AlexandrovInputs`) and the pointwise slope estimate `(point)`
(`Submission.AlexandrovSlope`).
-/
import Mathlib
import Submission.AlexandrovInputs
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


/-- **Proposition 3.1 of Shankar--Yuan**, reduced to the three inputs above.

Proof (all ingredients proved in this repository):
1. `hH` applied to `g` on `s = ball 0 3` gives `G, M, σ` with `HasWeakGradient`/`HasWeakHessian`
   and `(σ i j).totalVariation ⟂ volume`; the `2`-convexity hypothesis is
   `isTwoConvexOn_of_viscSolution`.
2. The a.e. conditions (Lebesgue points of `G` and of the `M i j`, vanishing of the density of
   `(σ i j).totalVariation`) hold almost everywhere, by
   `Commons.Measure.Lebesgue.ae_isLebesguePoint`, `...ae_isLebesguePoint_vec` and
   `...ae_isVanishingPoint`; since `ball 0 (1/3)` has positive volume,
   `Measure.exists_mem_of_measure_ne_zero_of_ae` produces `x₀` in it where all of them hold.
3. The pointwise slope estimate `(point)` of the paper for `h := taylorRemainder g G M x₀` is
   `Submission.point_estimate`: it applies the gradient estimate `hG` to
   `g - (fun y => g x₀ + ⟪G x₀, y - x₀⟫)` (a viscosity solution by
   `Submission.isViscSolution_sub_affine`), uses that this function equals `h + q` with `q` the
   quadratic form `quadM M x₀` of the matrix `M x₀`, and bounds the difference of two values of
   `q` by `‖quadM M x₀‖ (‖y-x₀‖+‖z-x₀‖) ‖y-z‖`.
4. `hT` gives the average bound `⨍_{ball x₀ r} |h| = o(r²)`.
5. `Commons.Measure.Lebesgue.sup_le_of_average_and_slope` turns 3 and 4 into
   `∀ᶠ r in 𝓝[>] 0, ∀ y ∈ ball x₀ (r/2), |h y| ≤ ε r²`; after the change of variable `r ↦ 2r`
   this is `∀ᶠ r, ∀ y ∈ ball x₀ r, |h y| ≤ ε r²`, which
   `Commons.Analysis.Asymptotics.isLittleO_of_sup_ball_bound` (together with `h x₀ = 0`) converts
   into `h = o(‖· - x₀‖²)`, i.e. `IsTwiceDiffAt g x₀` with `L := ⟪G x₀, ·⟫` and
   `Q := quadM M x₀`. -/
theorem alexandrovInput_holds (hG : GradientEstimateInput) (hH : WeakHessianMeasureInput)
    (hT : TaylorCoreInput) : AlexandrovInput := by
  intro g hgcont hgsol hgΔ
  have hgcont' : ContinuousOn g (ball 0 3) := hgcont.mono ball_subset_closedBall
  have h2cv : IsTwoConvexOn g (ball 0 3) := isTwoConvexOn_of_viscSolution isOpen_ball hgsol.1 hgΔ
  obtain ⟨G, M, σ, hGli, hMli, hσsing, hwg, hwh⟩ :=
    hH g (ball 0 3) isOpen_ball hgcont' h2cv
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
  have hx₀3 : x₀ ∈ ball (0 : ℝ⁴) 3 := by
    rw [mem_ball, dist_zero_right]
    linarith
  -- ## the pointwise slope estimate
  obtain ⟨A, hApos, hA⟩ := point_estimate hG hgcont hgsol hgΔ x₀
  have hR : 0 < 3 - ‖x₀‖ := by linarith
  -- ## the `L¹` average bound (the analytic core)
  -- the analytic core needs `g` to be locally integrable on all of `ℝ⁴`, which a function that is
  -- only known to be continuous on `closedBall 0 3` need not be; we therefore apply it to the
  -- truncation `g₁ = g · 1_{closedBall 0 3}`, which has the same values as `g` on `ball 0 3`
  -- (where the weak derivative identities are tested).
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
  have hg₁cont : ContinuousOn g₁ (ball (0 : ℝ⁴) 3) :=
    hgcont'.congr (fun x hx => hg₁g x (ball_subset_closedBall hx))
  have hwg₁ : HasWeakGradient g₁ (ball (0 : ℝ⁴) 3) G :=
    HasWeakGradient.congr_of_eqOn hwg (fun x hx => (hg₁g x (ball_subset_closedBall hx)).symm)
  have hwh₁ : HasWeakHessian g₁ (ball (0 : ℝ⁴) 3) M σ :=
    HasWeakHessian.congr_of_eqOn hwh (fun x hx => (hg₁g x (ball_subset_closedBall hx)).symm)
  have hTay₁ := hT g₁ (ball (0 : ℝ⁴) 3) x₀ isOpen_ball hx₀3 hg₁cont hg₁li G M σ hGli hMli
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

/-- **The analytic core** `TaylorCoreInput` (the paper's Lemma `lem:o(r²)`), now a theorem:
the proof is `Submission.taylorCore` in `Submission/TaylorCore.lean`. -/
theorem taylorCoreInput_holds : TaylorCoreInput :=
  fun u s x₀ hs hx₀ hcont hu G M σ hGli hMli hwg hwh hGleb hMleb hσvan =>
    taylorCore u s x₀ hs hx₀ hcont hu G M σ hGli hMli hwg hwh hGleb hMleb hσvan

end Submission
