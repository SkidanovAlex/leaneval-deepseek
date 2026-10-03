import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn
import Submission.Lib.Unif2.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
import Submission.Lib.Unif2.Work.Analysis.Complex.integral_conformal_change_of_variables
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.chart_transition_analytic
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.exists_chartBall_smoothPartitionOfUnity
import Submission.Lib.Unif2.Work.Drive.greenEnergyChart
import Submission.Lib.Unif2.ChartBallBarrier
import Submission.Lib.Unif2.Work.Jordan.dirichlet_integral
import Submission.Lib.Unif2.Work.Analysis.Complex.conformal_dirichlet_integrand
import Submission.Lib.Unif2.Work.Analysis.integrable_inv_norm_mul

/-!
# The chart-wise Dirichlet pairing: the "energy" route to the symmetry of the Green function
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## 1. The pairing and its elementary algebra -/

/-- The chart-local Dirichlet pairing term.  The weight `ψ` is clamped at the radius `σ`, the two
differentiated functions at the (larger) radius `ρ`. -/
def pairTerm (x : X) (ρ σ : ℝ) (ψ f χ : X → ℝ) : ℝ :=
  ∫ z : ℂ, clampedPullback x σ ψ z *
    inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ χ) z)

/-- The finite sum of chart-local Dirichlet pairing terms attached to a chart-ball cover. -/
def pairing {ι : Type*} [Fintype ι] (x : ι → X) (ρ σ : ι → ℝ) (ψ : ι → X → ℝ)
    (f χ : X → ℝ) : ℝ :=
  ∑ i, pairTerm (x i) (ρ i) (σ i) (ψ i) f χ

/-- The pairing integrand is integrable. -/
def PairIntegrable (x : X) (ρ σ : ℝ) (ψ f χ : X → ℝ) : Prop :=
  Integrable (fun z : ℂ => clampedPullback x σ ψ z *
    inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ χ) z))

theorem clampedPullback_add (x : X) (ρ : ℝ) (u v : X → ℝ) :
    clampedPullback x ρ (u + v) = clampedPullback x ρ u + clampedPullback x ρ v := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · simp only [Pi.add_apply, clampedPullback, Set.indicator_of_mem hz]
  · simp only [Pi.add_apply, clampedPullback, Set.indicator_of_notMem hz, add_zero]

theorem clampedPullback_sub (x : X) (ρ : ℝ) (u v : X → ℝ) :
    clampedPullback x ρ (u - v) = clampedPullback x ρ u - clampedPullback x ρ v := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · simp only [Pi.sub_apply, clampedPullback, Set.indicator_of_mem hz]
  · simp only [Pi.sub_apply, clampedPullback, Set.indicator_of_notMem hz, sub_zero]

theorem clampedPullback_smul (x : X) (ρ : ℝ) (c : ℝ) (u : X → ℝ) :
    clampedPullback x ρ (c • u) = c • clampedPullback x ρ u := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · simp only [Pi.smul_apply, clampedPullback, Set.indicator_of_mem hz]
  · simp only [Pi.smul_apply, clampedPullback, Set.indicator_of_notMem hz, smul_zero]

theorem clampedPullback_congr {x : X} {ρ : ℝ} {u v : X → ℝ}
    (h : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
      u ((chartAt ℂ x).symm z) = v ((chartAt ℂ x).symm z)) :
    clampedPullback x ρ u = clampedPullback x ρ v := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · simp only [clampedPullback, Set.indicator_of_mem hz]; exact h z hz
  · simp only [clampedPullback, Set.indicator_of_notMem hz]

theorem clampedPullback_zero (x : X) (ρ : ℝ) : clampedPullback x ρ (0 : X → ℝ) = 0 := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · simp [clampedPullback, Set.indicator_of_mem hz]
  · simp [clampedPullback, Set.indicator_of_notMem hz]

/-- The clamped pullback vanishes away from the open ball of its radius. -/
theorem clampedPullback_eq_zero_of_notMem_ball {x : X} {ρ : ℝ} {u : X → ℝ} {z : ℂ}
    (hz : z ∉ Metric.ball ((chartAt ℂ x) x) ρ) : clampedPullback x ρ u z = 0 :=
  Set.indicator_of_notMem hz _

/-- A clamped pullback with the support of `u` inside the smaller ball is exactly the chart pullback
there. -/
theorem clampedPullback_eq_of_mem_ball {x : X} {ρ σ : ℝ} {u : X → ℝ} (hσρ : σ ≤ ρ)
    {z : ℂ} (hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ) :
    clampedPullback x ρ u z = u ((chartAt ℂ x).symm z) := by
  rw [clampedPullback_apply_of_mem (Metric.ball_subset_ball hσρ hz)]

/-- A clamped pullback with the support of `u` inside the smaller ball vanishes off that ball. -/
theorem clampedPullback_eq_zero_of_notMem_smaller {x : X} {ρ σ : ℝ} {u : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hsupp : tsupport u ⊆ (chartAt ℂ x) ⁻¹' (Metric.ball ((chartAt ℂ x) x) σ))
    {z : ℂ} (hz : z ∉ Metric.ball ((chartAt ℂ x) x) σ) : clampedPullback x ρ u z = 0 := by
  by_cases hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · rw [clampedPullback_apply_of_mem hzρ]
    by_contra hne
    have hmem : (chartAt ℂ x).symm z ∈ tsupport u := subset_tsupport _ (Function.mem_support.mpr hne)
    have hthis := hsupp hmem
    rw [Set.mem_preimage, (chartAt ℂ x).right_inv (htgt hzρ)] at hthis
    exact hz hthis
  · exact clampedPullback_eq_zero_of_notMem_ball hzρ

/-! ## 2. Linearity.  The gradient is additive at every point where both functions are
differentiable, hence the pairing is additive as soon as the two integrands are integrable. -/

theorem gradient_add_of_differentiableAt {u v : ℂ → ℝ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    gradient (u + v) z = gradient u z + gradient v z := by
  simp only [gradient]
  rw [fderiv_add hu hv, map_add]

theorem gradient_const_smul (c : ℝ) (u : ℂ → ℝ) (z : ℂ) :
    gradient (c • u) z = c • gradient u z := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [gradient]
  · by_cases hu : DifferentiableAt ℝ u z
    · simp only [gradient]
      rw [fderiv_const_smul hu c, map_smul]
    · have hcu : ¬ DifferentiableAt ℝ (c • u) z := by
        intro h
        have h' : DifferentiableAt ℝ (fun z => c⁻¹ • (c • u z)) z := h.const_smul c⁻¹
        have heq : (fun z => c⁻¹ • (c • u z)) = u := by
          funext w; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [heq] at h'
        exact hu h'
      rw [gradient, gradient, fderiv_zero_of_not_differentiableAt hcu,
        fderiv_zero_of_not_differentiableAt hu]
      simp

theorem pairTerm_add {x : X} {ρ σ : ℝ} {ψ f χ₁ χ₂ : X → ℝ}
    (h₁ : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ χ₁) z)
    (h₂ : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ χ₂) z)
    (hi₁ : PairIntegrable x ρ σ ψ f χ₁) (hi₂ : PairIntegrable x ρ σ ψ f χ₂) :
    pairTerm x ρ σ ψ f (χ₁ + χ₂) = pairTerm x ρ σ ψ f χ₁ + pairTerm x ρ σ ψ f χ₂ := by
  rw [pairTerm, pairTerm, pairTerm]
  rw [← integral_add hi₁ hi₂]
  refine integral_congr_ae ?_
  filter_upwards [h₁, h₂] with z hz1 hz2
  rw [clampedPullback_add, gradient_add_of_differentiableAt hz1 hz2, inner_add_right, mul_add]

theorem pairTerm_smul {x : X} {ρ σ : ℝ} {ψ f χ : X → ℝ} (c : ℝ) :
    pairTerm x ρ σ ψ f (c • χ) = c * pairTerm x ρ σ ψ f χ := by
  have hfun : (fun z : ℂ => clampedPullback x σ ψ z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ (c • χ)) z))
      = fun z : ℂ => c * (clampedPullback x σ ψ z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ χ) z)) := by
    funext z
    rw [clampedPullback_smul]
    rw [gradient_const_smul]
    rw [inner_smul_right]
    ring
  rw [pairTerm, pairTerm, hfun, integral_const_mul]


/-- **Integrability of a pairing integrand with a `1/‖z - p‖` growth bound.**  If the weight is a
bounded continuous compactly supported function and the Dirichlet pairing of the two differentiated
functions grows at most like the inverse distance to `p`, then the integrand is integrable. -/
theorem pairIntegrable_of_growth {x : X} {ρ σ : ℝ} {ψ f χ : X → ℝ} {p : ℂ} {C : ℝ}
    (hcont : Continuous (clampedPullback x σ ψ)) (hcs : HasCompactSupport (clampedPullback x σ ψ))
    (hgrad : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ χ) z)‖
        ≤ C / ‖z - p‖)
    (hmeas : AEStronglyMeasurable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ χ) z)) volume) :
    PairIntegrable x ρ σ ψ f χ := by
  have hmaj : Integrable (fun z : ℂ => C * ((‖z - p‖)⁻¹ * |clampedPullback x σ ψ z|)) :=
    (Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport p _
      hcont.abs hcs.abs).const_mul C
  refine Integrable.mono' hmaj (hcont.aestronglyMeasurable.mul hmeas) ?_
  filter_upwards [hgrad] with z hz
  rw [norm_mul, Real.norm_eq_abs]
  calc |clampedPullback x σ ψ z| *
        ‖inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ χ) z)‖
      ≤ |clampedPullback x σ ψ z| * (C / ‖z - p‖) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = C * ((‖z - p‖)⁻¹ * |clampedPullback x σ ψ z|) := by
        rw [div_eq_mul_inv]; ring

/-! ## 3. Chart transfer

The pairing is unchanged if the term at the index `i` is evaluated in another chart through which
the same function can be read: the conformal invariance of the Dirichlet integrand
(`Work.Analysis.Complex.conformal_dirichlet_integrand`).  This is what makes the pairing a
chart-independent object. -/


/-- **Almost-everywhere differentiability of the clamped chart pullback.**  If `u` vanishes outside
the chart preimage of the ball of radius `σ < ρ`, then the clamped pullback at radius `ρ` is
differentiable at every point at distance `> σ` from the centre (where it vanishes identically),
and inside the ball of radius `σ` wherever the honest chart pullback is differentiable.  The
exceptional set is contained in the centre together with the sphere of radius `σ`, hence is null. -/
theorem clampedPullback_differentiableAt_ae {x : X} {ρ σ : ℝ} {u : X → ℝ} (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hsupp : tsupport u ⊆ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) σ)
    (hu : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) σ, z ≠ (chartAt ℂ x) x →
      DifferentiableAt ℝ (fun w : ℂ => u ((chartAt ℂ x).symm w)) z) :
    ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ u) z := by
  rw [ae_iff]
  have hnull : volume ({(chartAt ℂ x) x} ∪ Metric.sphere ((chartAt ℂ x) x) σ) = 0 :=
    measure_union_null (measure_singleton _)
      (MeasureTheory.Measure.addHaar_sphere volume _ σ)
  refine measure_mono_null (fun z hz => ?_) hnull
  by_cases h1 : dist z ((chartAt ℂ x) x) = σ
  · exact Or.inr (Metric.mem_sphere.mpr h1)
  · refine Or.inl ?_
    by_contra hne
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hzσ : z ∈ Metric.ball ((chartAt ℂ x) x) σ := Metric.mem_ball.mpr hlt
      have hdiff := hu z hzσ (by simpa using hne)
      have hev : (fun w : ℂ => u ((chartAt ℂ x).symm w)) =ᶠ[𝓝 z] clampedPullback x ρ u := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hσρ.le hzσ)] with w hw
        exact (clampedPullback_apply_of_mem (x₀ := x) (ρ := ρ) (u := u) hw).symm
      exact hz ((hev.differentiableAt_iff).mp hdiff)
    · have hopen : {w : ℂ | σ < dist w ((chartAt ℂ x) x)} ∈ 𝓝 z :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hgt
      have hev : clampedPullback x ρ u =ᶠ[𝓝 z] 0 := by
        filter_upwards [hopen] with w hw
        by_cases hb : w ∈ Metric.ball ((chartAt ℂ x) x) ρ
        · rw [clampedPullback_apply_of_mem hb]
          by_contra hne2
          have hmem : (chartAt ℂ x).symm w ∈ tsupport u :=
            subset_tsupport _ (Function.mem_support.mpr hne2)
          have hthis := hsupp hmem
          rw [Set.mem_preimage, (chartAt ℂ x).right_inv (htgt hb)] at hthis
          exact absurd hthis (not_lt.mpr hw.le)
        · rw [clampedPullback_eq_zero_of_notMem_ball hb]
          simp
      exact hz ((hev.differentiableAt_iff).mpr (differentiableAt_const 0))


/-- The pairing term only depends on the chart pullbacks of the two functions inside the ball. -/
theorem pairTerm_congr {x : X} {ρ σ : ℝ} {ψ f g f' g' : X → ℝ}
    (hf : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
      f ((chartAt ℂ x).symm z) = f' ((chartAt ℂ x).symm z))
    (hg : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
      g ((chartAt ℂ x).symm z) = g' ((chartAt ℂ x).symm z)) :
    pairTerm x ρ σ ψ f g = pairTerm x ρ σ ψ f' g' := by
  have hfun : (fun z : ℂ => clampedPullback x σ ψ z *
      inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z))
    = fun z : ℂ => clampedPullback x σ ψ z *
      inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f') z) (gradient (clampedPullback x ρ g') z) := by
    rw [clampedPullback_congr hf, clampedPullback_congr hg]
  rw [pairTerm, pairTerm, hfun]

/-- Linearity of the pairing term in the weight. -/
theorem pairTerm_weight_add {x : X} {ρ σ : ℝ} {ψ₁ ψ₂ f g : X → ℝ}
    (hi₁ : PairIntegrable x ρ σ ψ₁ f g) (hi₂ : PairIntegrable x ρ σ ψ₂ f g) :
    pairTerm x ρ σ (ψ₁ + ψ₂) f g = pairTerm x ρ σ ψ₁ f g + pairTerm x ρ σ ψ₂ f g := by
  rw [pairTerm, pairTerm, pairTerm, clampedPullback_add]
  rw [← integral_add hi₁ hi₂]
  refine integral_congr_ae ?_
  filter_upwards with z
  simp only [Pi.add_apply]
  ring

/-- Linearity of the pairing term in the weight (scalars). -/
theorem pairTerm_weight_smul {x : X} {ρ σ : ℝ} {ψ f g : X → ℝ} (c : ℝ) :
    pairTerm x ρ σ (c • ψ) f g = c * pairTerm x ρ σ ψ f g := by
  rw [pairTerm, pairTerm, clampedPullback_smul]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem pairTerm_transfer [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x x' : X} {ρ σ ρ' σ' : ℝ} {V : Set X} (hV : IsOpen V)
    (hVx : V ⊆ (chartAt ℂ x).source) (hVx' : V ⊆ (chartAt ℂ x').source)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (htgt' : Metric.ball ((chartAt ℂ x') x') ρ' ⊆ (chartAt ℂ x').target)
    {ψ f g : X → ℝ}
    (hsuppV : tsupport ψ ⊆ V)
    (hσρ : σ < ρ) (hσ'ρ' : σ' < ρ')
    (hballx : tsupport ψ ⊆ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) σ)
    (hballx' : tsupport ψ ⊆ (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') σ')
    (hf₂ : ∀ y ∈ V, DifferentiableAt ℝ (fun w : ℂ => f ((chartAt ℂ x').symm w)) ((chartAt ℂ x') y))
    (hg₂ : ∀ y ∈ V, DifferentiableAt ℝ (fun w : ℂ => g ((chartAt ℂ x').symm w)) ((chartAt ℂ x') y)) :
    pairTerm x ρ σ ψ f g = pairTerm x' ρ' σ' ψ f g := by
  classical
  set τ : ℂ → ℂ := fun z => (chartAt ℂ x') ((chartAt ℂ x).symm z) with hτ
  set s : Set ℂ := (chartAt ℂ x) '' V with hs
  have hτan : ∀ z ∈ s, DifferentiableAt ℂ τ z := by
    rintro z ⟨y, hyV, rfl⟩
    exact (Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ x')
      (chart_mem_atlas ℂ x) ((chartAt ℂ x) y) ((chartAt ℂ x).map_source (hVx hyV))
      (by rw [(chartAt ℂ x).left_inv (hVx hyV)]; exact hVx' hyV)).differentiableAt
  have hτinj : Set.InjOn τ s := by
    rintro z ⟨y, hyV, rfl⟩ z' ⟨y', hy'V, rfl⟩ h
    simp only [hτ, (chartAt ℂ x).left_inv (hVx hyV), (chartAt ℂ x).left_inv (hVx hy'V)] at h
    rw [(chartAt ℂ x').injOn (hVx' hyV) (hVx' hy'V) h]
  have hso : IsOpen s := (chartAt ℂ x).isOpen_image_of_subset_source hV hVx
  have hs_meas : MeasurableSet s := hso.measurableSet
  rw [pairTerm, pairTerm]
  set W : ℂ → ℝ := fun z => clampedPullback x σ ψ z *
    inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z) with hWdef
  set W' : ℂ → ℝ := fun w => clampedPullback x' σ' ψ w *
    inner (𝕜 := ℝ) (gradient (clampedPullback x' ρ' f) w) (gradient (clampedPullback x' ρ' g) w)
    with hW'def
  change ∫ z, W z = ∫ w, W' w
  have hWzero : ∀ z ∉ s, W z = 0 := by
    intro z hz
    by_cases hb : z ∈ Metric.ball ((chartAt ℂ x) x) σ
    · have hψ0 : ψ ((chartAt ℂ x).symm z) = 0 := by
        by_contra hne
        exact hz ⟨(chartAt ℂ x).symm z, hsuppV (subset_tsupport _ (Function.mem_support.mpr hne)),
          (chartAt ℂ x).right_inv (htgt (Metric.ball_subset_ball hσρ.le hb))⟩
      simp only [hWdef, clampedPullback_apply_of_mem hb, hψ0, zero_mul]
    · simp only [hWdef, clampedPullback_eq_zero_of_notMem_ball hb, zero_mul]
  have hW'zero : ∀ w ∉ τ '' s, W' w = 0 := by
    intro w hw
    by_cases hb : w ∈ Metric.ball ((chartAt ℂ x') x') σ'
    · have hψ0 : ψ ((chartAt ℂ x').symm w) = 0 := by
        by_contra hne
        have hmem : (chartAt ℂ x').symm w ∈ tsupport ψ :=
          subset_tsupport _ (Function.mem_support.mpr hne)
        have hyV : (chartAt ℂ x').symm w ∈ V := hsuppV hmem
        refine hw ⟨(chartAt ℂ x) ((chartAt ℂ x').symm w), ⟨(chartAt ℂ x').symm w, hyV, rfl⟩, ?_⟩
        simp only [hτ, (chartAt ℂ x).left_inv (hVx hyV),
          (chartAt ℂ x').right_inv (htgt' (Metric.ball_subset_ball hσ'ρ'.le hb))]
      simp only [hW'def, clampedPullback_apply_of_mem hb, hψ0, zero_mul]
    · simp only [hW'def, clampedPullback_eq_zero_of_notMem_ball hb, zero_mul]
  rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hWzero).symm,
    (setIntegral_eq_integral_of_forall_compl_eq_zero hW'zero).symm]
  have hcov : ∫ w in τ '' s, W' w = ∫ z in s, ‖deriv τ z‖ ^ 2 * W' (τ z) := by
    have hf' : ∀ z ∈ s, HasFDerivWithinAt τ (fderiv ℝ τ z) s z := fun z hz =>
      ((hτan z hz).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
    have hmain := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hs_meas hf' hτinj W'
    rw [hmain]
    refine setIntegral_congr_fun hs_meas (fun z hz => ?_)
    have hdet : (fderiv ℝ τ z).det = ‖deriv τ z‖ ^ 2 := by
      rw [Work.Jordan.fderiv_eq_smul_one (hτan z hz), Work.Jordan.det_smul_one_complex]
    rw [hdet, abs_of_nonneg (by positivity), smul_eq_mul]
  rw [hcov]
  refine setIntegral_congr_fun hs_meas (fun z hz => ?_)
  obtain ⟨y, hyV, rfl⟩ := hz
  have hysym : (chartAt ℂ x).symm ((chartAt ℂ x) y) = y := (chartAt ℂ x).left_inv (hVx hyV)
  by_cases hz0 : y ∈ tsupport ψ
  · have hzσ : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) σ :=
      Set.mem_preimage.mp (hballx hz0)
    have hzρ : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
      Metric.ball_subset_ball hσρ.le hzσ
    have hτval : τ ((chartAt ℂ x) y) = (chartAt ℂ x') y := by
      simp only [hτ, hysym]
    have htσ' : τ ((chartAt ℂ x) y) ∈ Metric.ball ((chartAt ℂ x') x') σ' := by
      rw [hτval]; exact Set.mem_preimage.mp (hballx' hz0)
    have htρ' : τ ((chartAt ℂ x) y) ∈ Metric.ball ((chartAt ℂ x') x') ρ' :=
      Metric.ball_subset_ball hσ'ρ'.le htσ'
    have hw : clampedPullback x σ ψ ((chartAt ℂ x) y) = clampedPullback x' σ' ψ (τ ((chartAt ℂ x) y)) := by
      rw [clampedPullback_apply_of_mem hzσ, clampedPullback_apply_of_mem htσ', hτval, hysym,
        (chartAt ℂ x').left_inv (hVx' hyV)]
    have hgx : gradient (clampedPullback x ρ f) ((chartAt ℂ x) y)
        = gradient (fun w : ℂ => f ((chartAt ℂ x).symm w)) ((chartAt ℂ x) y) :=
      Filter.EventuallyEq.gradient_eq (by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzρ] with w hw2
        exact clampedPullback_apply_of_mem (x₀ := x) (ρ := ρ) (u := f) hw2)
    have hgx' : gradient (clampedPullback x' ρ' f) (τ ((chartAt ℂ x) y))
        = gradient (fun w : ℂ => f ((chartAt ℂ x').symm w)) (τ ((chartAt ℂ x) y)) :=
      Filter.EventuallyEq.gradient_eq (by
        filter_upwards [Metric.isOpen_ball.mem_nhds htρ'] with w hw2
        exact clampedPullback_apply_of_mem (x₀ := x') (ρ := ρ') (u := f) hw2)
    have hgy : gradient (clampedPullback x ρ g) ((chartAt ℂ x) y)
        = gradient (fun w : ℂ => g ((chartAt ℂ x).symm w)) ((chartAt ℂ x) y) :=
      Filter.EventuallyEq.gradient_eq (by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzρ] with w hw2
        exact clampedPullback_apply_of_mem (x₀ := x) (ρ := ρ) (u := g) hw2)
    have hgy' : gradient (clampedPullback x' ρ' g) (τ ((chartAt ℂ x) y))
        = gradient (fun w : ℂ => g ((chartAt ℂ x').symm w)) (τ ((chartAt ℂ x) y)) :=
      Filter.EventuallyEq.gradient_eq (by
        filter_upwards [Metric.isOpen_ball.mem_nhds htρ'] with w hw2
        exact clampedPullback_apply_of_mem (x₀ := x') (ρ := ρ') (u := g) hw2)
    have hfcomp : (fun w : ℂ => f ((chartAt ℂ x').symm (τ w)))
        =ᶠ[𝓝 ((chartAt ℂ x) y)] (fun w : ℂ => f ((chartAt ℂ x).symm w)) := by
      filter_upwards [hso.mem_nhds ⟨y, hyV, rfl⟩] with w hw2
      obtain ⟨y', hy'V, rfl⟩ := hw2
      simp only [hτ, (chartAt ℂ x).left_inv (hVx hy'V),
        (chartAt ℂ x').left_inv (hVx' hy'V)]
    have hgcomp : (fun w : ℂ => g ((chartAt ℂ x').symm (τ w)))
        =ᶠ[𝓝 ((chartAt ℂ x) y)] (fun w : ℂ => g ((chartAt ℂ x).symm w)) := by
      filter_upwards [hso.mem_nhds ⟨y, hyV, rfl⟩] with w hw2
      obtain ⟨y', hy'V, rfl⟩ := hw2
      simp only [hτ, (chartAt ℂ x).left_inv (hVx hy'V),
        (chartAt ℂ x').left_inv (hVx' hy'V)]
    have hconf := Work.Analysis.Complex.conformal_dirichlet_integrand (τ := τ) (z := (chartAt ℂ x) y)
      (u := fun w : ℂ => f ((chartAt ℂ x').symm w))
      (v := fun w : ℂ => g ((chartAt ℂ x').symm w))
      (hτan ((chartAt ℂ x) y) ⟨y, hyV, rfl⟩)
      (by rw [hτval]; exact hf₂ y hyV)
      (by rw [hτval]; exact hg₂ y hyV)
    rw [Filter.EventuallyEq.gradient_eq hfcomp, Filter.EventuallyEq.gradient_eq hgcomp] at hconf
    simp only [hWdef, hW'def, hw, hgx, hgx', hgy, hgy']
    rw [hconf]
    ring
  · have hW0 : W ((chartAt ℂ x) y) = 0 := by
      by_cases hb : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) σ
      · have hψ0 : ψ ((chartAt ℂ x).symm ((chartAt ℂ x) y)) = 0 := by
          rw [hysym]; exact image_eq_zero_of_notMem_tsupport hz0
        simp only [hWdef, clampedPullback_apply_of_mem hb, hψ0, zero_mul]
      · simp only [hWdef, clampedPullback_eq_zero_of_notMem_ball hb, zero_mul]
    have hW'0 : W' (τ ((chartAt ℂ x) y)) = 0 := by
      by_cases hb : τ ((chartAt ℂ x) y) ∈ Metric.ball ((chartAt ℂ x') x') σ'
      · have hsym : (chartAt ℂ x').symm (τ ((chartAt ℂ x) y)) = y := by
          rw [hτ]; simp only [hysym, (chartAt ℂ x').left_inv (hVx' hyV)]
        have hψ0 : ψ ((chartAt ℂ x').symm (τ ((chartAt ℂ x) y))) = 0 := by
          rw [hsym]; exact image_eq_zero_of_notMem_tsupport hz0
        simp only [hW'def, clampedPullback_apply_of_mem hb, hψ0, zero_mul]
      · simp only [hW'def, clampedPullback_eq_zero_of_notMem_ball hb, zero_mul]
    rw [hW0, hW'0, mul_zero]


end Work.Drive
