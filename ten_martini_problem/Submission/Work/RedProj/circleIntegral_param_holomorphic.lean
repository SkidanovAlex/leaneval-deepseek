import Mathlib
import Submission.Work.TMComp.MAnalytic.deriv_bound
import Submission.Work.TMComp.MAnalytic.measurable_deriv_param

/-!
# Holomorphy of a parametric circle integral

Let `G : ℂ → ℂ → ℂ` be jointly continuous on `U ×ˢ V`, holomorphic in its first variable on the
open set `U`, and let `C(c, R) ⊆ V` be a circle.  Then the parametric circle integral

  `z ↦ ∮ w in C(c, R), ((w - c)⁻¹)^n * (w - c)⁻¹ * G z w`

is holomorphic on `U`.

The proof is differentiation under the integral sign: after unfolding `circleIntegral` the integral
is `∫ θ in 0..2π, (deriv (circleMap c R) θ) • (kernel θ * G z (circleMap c R θ))`, a parameter
integral with a continuous integrand whose `z`-slices are holomorphic.  The two inputs needed by
the parametric interval-integral theorem are

* a uniform bound on the slice derivatives (`deriv_bound_compact`, Cauchy's estimate), and
* measurability of the parameterized derivative (`measurable_deriv_param`).
-/

open Set Metric Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace Work.RedProj

noncomputable section

/-- **Uniform bound on slice derivatives** (Cauchy's estimate), over an arbitrary *compact*
parameter set.  This is `Work.TMComp.MAnalytic.deriv_bound` with `[0,1]` replaced by an arbitrary
compact `S ⊆ ℝ`; the proof is identical. -/
lemma deriv_bound_compact {W : Set ℂ} (hWo : IsOpen W) {g : ℂ → ℝ → ℂ}
    (hg : ContinuousOn (fun p : ℂ × ℝ => g p.1 p.2) (W ×ˢ Set.univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => g z x) W) {z₀ : ℂ} (hz₀ : z₀ ∈ W)
    {S : Set ℝ} (hS : IsCompact S) :
    ∃ r > 0, Metric.closedBall z₀ r ⊆ W ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ S, ∀ z ∈ Metric.closedBall z₀ (r / 2), ‖deriv (fun w => g w x) z‖ ≤ K := by
  obtain ⟨ε, hεpos, hεW⟩ := (Metric.isOpen_iff.mp hWo) z₀ hz₀
  set r : ℝ := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hsub : Metric.closedBall z₀ r ⊆ W :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεW
  refine ⟨r, hrpos, hsub, ?_⟩
  have hcomp : IsCompact (Metric.closedBall z₀ r ×ˢ S) :=
    (isCompact_closedBall z₀ r).prod hS
  have hcont : ContinuousOn (fun p : ℂ × ℝ => g p.1 p.2)
      (Metric.closedBall z₀ r ×ˢ S) :=
    hg.mono (Set.prod_mono hsub (Set.subset_univ _))
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max 0 (M / (r / 2)), le_max_left _ _, ?_⟩
  intro x hx z hz
  have hR : 0 < r / 2 := by positivity
  have hcb_sub : Metric.closedBall z (r / 2) ⊆ Metric.closedBall z₀ r := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    have h2 : dist z z₀ ≤ r / 2 := Metric.mem_closedBall.mp hz
    linarith [dist_triangle w z z₀]
  have hball_sub : Metric.ball z (r / 2) ⊆ W :=
    (Metric.ball_subset_closedBall.trans hcb_sub).trans hsub
  have hsphere_sub : Metric.sphere z (r / 2) ⊆ Metric.closedBall z₀ r :=
    Metric.sphere_subset_closedBall.trans hcb_sub
  have hdiff : DiffContOnCl ℂ (fun w => g w x) (Metric.ball z (r / 2)) := by
    refine ⟨(hhol x).mono hball_sub, ?_⟩
    rw [closure_ball z (by positivity : (r / 2 : ℝ) ≠ 0)]
    have hmaps : Set.MapsTo (fun w : ℂ => (w, x)) (Metric.closedBall z (r / 2))
        (W ×ˢ Set.univ) := by
      intro w hw
      exact ⟨hsub (hcb_sub hw), Set.mem_univ x⟩
    exact hg.comp ((continuous_id.prodMk continuous_const).continuousOn) hmaps
  have hC : ∀ w ∈ Metric.sphere z (r / 2), ‖g w x‖ ≤ M := by
    intro w hw
    exact hM (w, x) ⟨hsphere_sub hw, hx⟩
  exact (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff hC).trans (le_max_right _ _)

/-- **Differentiation under the integral sign**, interval version with arbitrary endpoints.
If `g : ℂ → ℝ → ℂ` is jointly continuous on `W ×ˢ univ` with `W` open and every slice
`z ↦ g z x` is holomorphic on `W`, then `z ↦ ∫ x in a..b, g z x` is holomorphic on `W`. -/
theorem intervalIntegral_param_holomorphic {W : Set ℂ} (hWo : IsOpen W) {g : ℂ → ℝ → ℂ}
    (hg : ContinuousOn (fun p : ℂ × ℝ => g p.1 p.2) (W ×ˢ Set.univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => g z x) W)
    {a b : ℝ} (hab : a ≤ b) :
    DifferentiableOn ℂ (fun z => ∫ x in a..b, g z x) W := by
  intro z₀ hz₀
  obtain ⟨r, hr, hsub, K, _hKnn, hboundK⟩ :=
    deriv_bound_compact hWo hg hhol hz₀ (isCompact_Icc (a := a) (b := b))
  have hs : Metric.closedBall z₀ (r / 2) ∈ 𝓝 z₀ := Metric.closedBall_mem_nhds z₀ (by linarith)
  have hcont_g : ∀ w ∈ W, Continuous (fun t : ℝ => g w t) := fun w hw =>
    hg.comp_continuous (continuous_const.prodMk continuous_id) (fun t => by simp [hw])
  have h1 : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t : ℝ => g z t) (volume.restrict (Ι a b)) := by
    filter_upwards [hWo.mem_nhds hz₀] with z hz
    exact (hcont_g z hz).aestronglyMeasurable
  have h2 : IntervalIntegrable (fun t : ℝ => g z₀ t) volume a b :=
    (hcont_g z₀ hz₀).intervalIntegrable a b
  have h3 : AEStronglyMeasurable (fun t : ℝ => deriv (fun w => g w t) z₀)
      (volume.restrict (Ι a b)) :=
    (Work.TMComp.MAnalytic.measurable_deriv_param hWo hg hhol hz₀).aestronglyMeasurable
  have h4 : ∀ᵐ t ∂volume, t ∈ Ι a b →
      ∀ z ∈ Metric.closedBall z₀ (r / 2), ‖deriv (fun w => g w t) z‖ ≤ (fun _ : ℝ => K) t := by
    filter_upwards with t ht z hz
    rw [Set.uIoc_of_le hab] at ht
    exact hboundK t ⟨ht.1.le, ht.2⟩ z hz
  have h5 : ∀ᵐ t ∂volume, t ∈ Ι a b →
      ∀ z ∈ Metric.closedBall z₀ (r / 2),
        HasDerivAt (fun z => g z t) (deriv (fun w => g w t) z) z := by
    filter_upwards with t _ht z hz
    exact ((hhol t).differentiableAt
      (hWo.mem_nhds (hsub (Metric.closedBall_subset_closedBall (by linarith) hz)))).hasDerivAt
  have key := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume) (E := ℂ) (a := a) (b := b)
    (bound := fun _ : ℝ => K) (F := fun z x => g z x)
    (F' := fun z x => deriv (fun w => g w x) z)
    (x₀ := z₀) (s := Metric.closedBall z₀ (r / 2))
    hs h1 h2 h3 h4 intervalIntegrable_const h5).2
  exact key.differentiableAt.differentiableWithinAt

/-- **The circle integral of a holomorphic family is holomorphic.** -/
theorem circleIntegral_param_holomorphic {U V : Set ℂ} (hU : IsOpen U)
    {G : ℂ → ℂ → ℂ} (hcont : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (U ×ˢ V))
    (hhol : ∀ w ∈ V, DifferentiableOn ℂ (fun z => G z w) U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hsphere : Metric.sphere c R ⊆ V) (n : ℕ) :
    DifferentiableOn ℂ (fun z => ∮ w in C(c, R), ((w - c)⁻¹)^n * (w - c)⁻¹ * G z w) U := by
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ V :=
    fun θ => hsphere (circleMap_mem_sphere c hR.le θ)
  -- continuity of the kernel `θ ↦ ((circleMap c R θ - c)⁻¹)^n * (circleMap c R θ - c)⁻¹`
  have hne : ∀ θ : ℝ, circleMap c R θ - c ≠ 0 :=
    fun θ => sub_ne_zero.mpr (circleMap_ne_center hR.ne' (θ := θ))
  have hk : Continuous
      (fun θ : ℝ => ((circleMap c R θ - c)⁻¹)^n * (circleMap c R θ - c)⁻¹) := by
    have h1 : Continuous (fun θ : ℝ => (circleMap c R θ - c)⁻¹) :=
      ((continuous_circleMap c R).sub continuous_const).inv₀ hne
    exact (h1.pow n).mul h1
  have hderiv : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  -- joint continuity of the integrand
  have hcm : Continuous (fun p : ℂ × ℝ => (p.1, circleMap c R p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hmap : Set.MapsTo (fun p : ℂ × ℝ => (p.1, circleMap c R p.2))
      (U ×ˢ Set.univ) (U ×ˢ V) := fun p hp => ⟨hp.1, hmem p.2⟩
  have hGcomp : ContinuousOn (fun p : ℂ × ℝ => G p.1 (circleMap c R p.2)) (U ×ˢ Set.univ) :=
    hcont.comp hcm.continuousOn hmap
  have hcont_int : ContinuousOn (fun p : ℂ × ℝ =>
      deriv (circleMap c R) p.2 *
        (((circleMap c R p.2 - c)⁻¹)^n * (circleMap c R p.2 - c)⁻¹ * G p.1 (circleMap c R p.2)))
      (U ×ˢ Set.univ) :=
    ((hderiv.comp continuous_snd).continuousOn).mul (((hk.comp continuous_snd).continuousOn).mul hGcomp)
  -- holomorphy of each slice
  have hhol' : ∀ θ : ℝ, DifferentiableOn ℂ (fun z => deriv (circleMap c R) θ *
      (((circleMap c R θ - c)⁻¹)^n * (circleMap c R θ - c)⁻¹ * G z (circleMap c R θ))) U := by
    intro θ
    have hbase : DifferentiableOn ℂ (fun z => G z (circleMap c R θ)) U := hhol _ (hmem θ)
    exact (hbase.const_mul _).const_mul (deriv (circleMap c R) θ)
  have hmain := intervalIntegral_param_holomorphic (W := U) hU
    (g := fun z θ => deriv (circleMap c R) θ *
      (((circleMap c R θ - c)⁻¹)^n * (circleMap c R θ - c)⁻¹ * G z (circleMap c R θ)))
    hcont_int hhol'
    (a := (0 : ℝ)) (b := 2 * Real.pi) Real.two_pi_pos.le
  simpa only [circleIntegral, smul_eq_mul] using hmain

end

end Work.RedProj
