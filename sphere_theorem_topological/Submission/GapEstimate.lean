import Submission.HopfRinow2
import Submission.ChartBounds
import Submission.BonnetMyers
import Submission.Commons.Analysis.Calculus.taylor_second_order_cubic_rem
import Submission.Minimal
import Submission.GeodesicSpeed
import Submission.Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
import Submission.EDist

/-!
# The distance between two points of a chart is bounded by their coordinate distance

For two coordinate vectors `p, q` in the chart at `x₀` whose connecting segment stays in a set on
which the chart metric is bounded by `Λ`, the Riemannian distance between the corresponding points
is at most `√Λ ‖p - q‖`.  The proof bounds the length of the straight chart segment with the help of
`chartGram` and the bridge between `pathELength` and the integral of the speed.

Main result: `riemannianEDist_chart_le`.  It is the tool that turns an `O(s³)` bound on coordinate
differences (Taylor's theorem, `Commons.Analysis.Calculus.taylor_second_order_cubic_rem`) into an
`O(s³)` bound on the gaps between the pieces of a piecewise geodesic variation.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Length
open Submission.ChartBounds
open Submission.BonnetMyers
open Submission.ChartConnection
open Submission.HopfRinow

namespace Submission.GapEstimate

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

/-- The straight segment in the chart, as a curve in the manifold. -/
def chartSeg (x₀ : M) (p q : E) : ℝ → M := fun t => (extChartAt I x₀).symm (p + t • (q - p))

lemma chartSeg_zero (x₀ : M) (p q : E) : chartSeg (I := I) x₀ p q 0 = (extChartAt I x₀).symm p := by
  simp [chartSeg]

lemma chartSeg_one (x₀ : M) (p q : E) : chartSeg (I := I) x₀ p q 1 = (extChartAt I x₀).symm q := by
  simp [chartSeg]

/-- **The coordinate distance bounds the Riemannian distance in a chart.** -/
theorem riemannianEDist_chart_le {x₀ : M} {K : Set E} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hbound : ∀ z ∈ K, ∀ a : E,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm z) a a ≤ Λ * ‖a‖ ^ 2)
    (hKt : ∀ z ∈ K, z ∈ (extChartAt I x₀).target)
    {p q : E} (hp : p ∈ K)
    (hconv : ∀ t ∈ Icc (0:ℝ) 1, p + t • (q - p) ∈ K) :
    Manifold.riemannianEDist I ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm q)
      ≤ ENNReal.ofReal (Real.sqrt Λ * ‖q - p‖) := by
  have hσderiv : ∀ t : ℝ, HasDerivAt (fun r : ℝ => p + r • (q - p)) (q - p) t := by
    intro t
    have h1 : HasDerivAt (fun r : ℝ => r • (q - p)) ((1 : ℝ) • (q - p)) t :=
      (hasDerivAt_id t).smul_const (q - p)
    have h2 : HasDerivAt (fun r : ℝ => p + r • (q - p)) (q - p) t := by
      have h := (hasDerivAt_const (x := t) (c := p)).add h1
      have hfun : ((fun _ : ℝ => p) + fun r : ℝ => r • (q - p))
          = fun r : ℝ => p + r • (q - p) := by funext r; rfl
      rw [hfun] at h
      simpa using h
    exact h2
  have hσmem : ∀ t ∈ Icc (0:ℝ) 1, (fun r : ℝ => p + r • (q - p)) t ∈ (extChartAt I x₀).target :=
    fun t ht => hKt ((fun r : ℝ => p + r • (q - p)) t) (hconv t ht)
  have hσcont : ContinuousOn (fun r : ℝ => p + r • (q - p)) (Icc (0:ℝ) 1) :=
    fun t ht => (hσderiv t).continuousAt.continuousWithinAt
  -- the curve is `C¹`
  have hγ : CMDiff[Icc (0:ℝ) 1] 1 (chartSeg (I := I) x₀ p q) := by
    have hs : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
    have hdiff : DifferentiableOn ℝ (fun r : ℝ => p + r • (q - p)) (Icc (0:ℝ) 1) :=
      fun t ht => (hσderiv t).differentiableAt.differentiableWithinAt
    have hderiv : EqOn (derivWithin (fun r : ℝ => p + r • (q - p)) (Icc (0:ℝ) 1))
        (fun _ => q - p) (Icc (0:ℝ) 1) :=
      fun t ht => (hσderiv t).hasDerivWithinAt.derivWithin (hs t ht)
    have hcont : ContinuousOn (derivWithin (fun r : ℝ => p + r • (q - p)) (Icc (0:ℝ) 1))
        (Icc (0:ℝ) 1) :=
      ContinuousOn.congr continuousOn_const hderiv
    have hσ' : ContDiffOn ℝ (1 : ℕ∞ω) (fun r : ℝ => p + r • (q - p)) (Icc (0:ℝ) 1) :=
      (contDiffOn_one_iff_derivWithin hs).mpr ⟨hdiff, hcont⟩
    have hσ'' : CMDiff[Icc (0:ℝ) 1] 1 (fun r : ℝ => p + r • (q - p)) :=
      contMDiffOn_iff_contDiffOn.mpr hσ'
    have hmaps : MapsTo (fun r : ℝ => p + r • (q - p)) (Icc (0:ℝ) 1) (extChartAt I x₀).target :=
      hσmem
    have h := (contMDiffOn_extChartAt_symm (I := I) x₀).comp hσ'' hmaps
    have hfun : (chartSeg (I := I) x₀ p q) = ((extChartAt I x₀).symm) ∘
        (fun r : ℝ => p + r • (q - p)) := rfl
    rw [hfun]
    exact h
  -- the speed is bounded
  have hspeed : ∀ t ∈ Icc (0:ℝ) 1,
      curveSpeed (I := I) (chartSeg (I := I) x₀ p q) t ≤ Real.sqrt Λ * ‖q - p‖ := by
    intro t ht
    have htgt : (fun r : ℝ => p + r • (q - p)) t ∈ (extChartAt I x₀).target := hσmem t ht
    have hstayn : ∀ᶠ r in 𝓝 t, (fun r : ℝ => p + r • (q - p)) r
        ∈ (extChartAt I x₀).target :=
      (hσderiv t).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds htgt)
    change curveSpeed (I := I) (fun s : ℝ => (extChartAt I x₀).symm (p + s • (q - p))) t
      ≤ Real.sqrt Λ * ‖q - p‖
    rw [curveSpeed_chartCurve (I := I) (u := fun r : ℝ => p + r • (q - p)) (v := q - p)
      (t := t) (hσderiv t) htgt hstayn]
    have hb := hbound ((fun r : ℝ => p + r • (q - p)) t) (hconv t ht) (q - p)
    calc Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm
          ((fun r : ℝ => p + r • (q - p)) t)) (q - p) (q - p))
        ≤ Real.sqrt (Λ * ‖q - p‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt Λ * ‖q - p‖ := by
          rw [Real.sqrt_mul hΛ, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  -- the length of the segment
  have hspeed2 : ∀ t ∈ Icc (0:ℝ) 1,
      curveSpeed (I := I) (chartSeg (I := I) x₀ p q) t
        = Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (p + t • (q - p)))
            (q - p) (q - p)) := by
    intro t ht
    change curveSpeed (I := I) (fun s : ℝ => (extChartAt I x₀).symm (p + s • (q - p))) t
      = Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm
          ((fun r : ℝ => p + r • (q - p)) t)) (q - p) (q - p))
    rw [curveSpeed_chartCurve (I := I) (u := fun r : ℝ => p + r • (q - p)) (v := q - p)
      (t := t) (hσderiv t) (hσmem t ht) ((hσderiv t).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hσmem t ht)))]
  have hGramCont : ContinuousOn (fun t : ℝ => chartGram (I := I) x₀
      ((extChartAt I x₀).symm (p + t • (q - p))) (q - p) (q - p)) (Icc (0:ℝ) 1) :=
    continuousOn_chartGram_curve (I := I)
      ((contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) x₀).continuousOn.comp
        hσcont hσmem)
      continuousOn_const continuousOn_const
      (fun t ht => mem_source_chartCurve (I := I) (x₀ := x₀)
        (u := fun r : ℝ => p + r • (q - p)) (t := t) (hσmem t ht))
  have hcont : ContinuousOn (fun t : ℝ => curveSpeed (I := I) (chartSeg (I := I) x₀ p q) t)
      (Icc (0:ℝ) 1) :=
    ContinuousOn.congr hGramCont.sqrt (fun t ht => hspeed2 t ht)
  have hnn : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ curveSpeed (I := I) (chartSeg (I := I) x₀ p q) t :=
    fun t ht => curveSpeed_nonneg (I := I) _ t
  have hPL := Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
    (I := I) (γ := chartSeg (I := I) x₀ p q) (a := 0) (b := 1) zero_le_one
    (hcont.integrableOn_Icc) hnn ?_
  · have hlen : Manifold.pathELength I (chartSeg (I := I) x₀ p q) 0 1
        ≤ ENNReal.ofReal (Real.sqrt Λ * ‖q - p‖) := by
      rw [hPL]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ∫ t in (0:ℝ)..1, curveSpeed (I := I) (chartSeg (I := I) x₀ p q) t
          ≤ ∫ t in (0:ℝ)..1, Real.sqrt Λ * ‖q - p‖ := by
            refine intervalIntegral.integral_mono_on zero_le_one
              (by rwa [uIcc_of_le zero_le_one] : ContinuousOn
                (fun t : ℝ => curveSpeed (I := I) (chartSeg (I := I) x₀ p q) t)
                (uIcc (0:ℝ) 1)).intervalIntegrable
              intervalIntegrable_const hspeed
        _ = Real.sqrt Λ * ‖q - p‖ := by
            rw [intervalIntegral.integral_const, sub_zero]
            simp
    exact (Manifold.riemannianEDist_le_pathELength hγ (chartSeg_zero x₀ p q)
      (chartSeg_one x₀ p q) zero_le_one).trans hlen
  · intro t ht
    show ‖curveVelocity (I := I) (chartSeg (I := I) x₀ p q) t‖ₑ
      = ENNReal.ofReal (curveSpeed (I := I) (chartSeg (I := I) x₀ p q) t)
    rw [Submission.Minimal.enorm_eq_ofReal_norm,
      Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) (chartSeg (I := I) x₀ p q) t]


/-- **The gap between two curves with the same 2-jet is `O(s³)`.**  If `V` and `V + g` are two
coordinate curves in the chart at `x₀` whose difference `g` vanishes to second order at `0`
(`g 0 = g' 0 = g'' 0 = 0`) with `‖g'''‖ ≤ M₀` and both curves stay in a ball on which the chart
metric is bounded by `Λ`, then the Riemannian distance between the corresponding points is at most
`√Λ * (M₀ / 6) * |s|³` for small `s`. -/
theorem riemannianEDist_le_cube_of_gap {x₀ : M} {V g g' g'' g''' : ℝ → E} {K : Set E}
    {c : E} {r Λ M₀ ρ : ℝ} (hK : K = Metric.ball c r) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ)
    (hg0 : g 0 = 0) (hg'0 : g' 0 = 0) (hg''0 : g'' 0 = 0)
    (h1 : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g (g' s) s)
    (h2 : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g' (g'' s) s)
    (h3 : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g'' (g''' s) s)
    (hbd : ∀ s ∈ Ioo (-ρ) ρ, ‖g''' s‖ ≤ M₀)
    (hbound : ∀ z ∈ K, ∀ a : E,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm z) a a ≤ Λ * ‖a‖ ^ 2)
    (hKt : ∀ z ∈ K, z ∈ (extChartAt I x₀).target)
    (hVin : ∀ s ∈ Ioo (-ρ) ρ, V s ∈ K) (hUVin : ∀ s ∈ Ioo (-ρ) ρ, V s + g s ∈ K) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ s : ℝ, |s| < ρ' →
      Manifold.riemannianEDist I ((extChartAt I x₀).symm (V s + g s)) ((extChartAt I x₀).symm (V s))
        ≤ ENNReal.ofReal (Real.sqrt Λ * (M₀ / 6 * |s| ^ 3)) := by
  have hMnn : 0 ≤ M₀ := le_trans (norm_nonneg _) (hbd 0 ⟨by linarith, by linarith⟩)
  refine ⟨ρ, hρ, le_rfl, fun s hs => ?_⟩
  have hsI : s ∈ Ioo (-ρ) ρ := ⟨by linarith [abs_lt.mp hs], by linarith [abs_lt.mp hs]⟩
  -- the norm bound on the difference
  have hgnorm : ‖g s‖ ≤ M₀ / 6 * |s| ^ 3 := by
    have h := Commons.Analysis.Calculus.taylor_second_order_cubic_rem
      (f := g) (f' := g') (f'' := g'') (f''' := g''') (M := M₀) (r := ρ) hρ h1 h2 h3 hbd s hsI
    simpa [hg0, hg'0, hg''0] using h
  -- the segment between the two points stays in the ball
  have hconv : ∀ t ∈ Icc (0:ℝ) 1, V s + g s + t • (V s - (V s + g s)) ∈ K := by
    intro t ht
    rw [hK]
    exact (convex_ball c r).add_smul_sub_mem (hK ▸ hUVin s hsI) (hK ▸ hVin s hsI) ht
  have h := riemannianEDist_chart_le (x₀ := x₀) (K := K) (Λ := Λ) hΛ hbound hKt
    (hUVin s hsI) hconv
  -- replace the coordinate distance by the cubic bound
  refine h.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt Λ * ‖V s - (V s + g s)‖ ≤ Real.sqrt Λ * (M₀ / 6 * |s| ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg Λ)
        rw [show V s - (V s + g s) = -g s by abel, norm_neg]
        exact hgnorm
    _ = Real.sqrt Λ * (M₀ / 6 * |s| ^ 3) := rfl

end

end Submission.GapEstimate
