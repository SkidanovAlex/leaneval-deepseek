import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Submission.Commons.Analysis.Convolution.fderiv_moll_weakGrad

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace

/-- If the weak gradient of a locally integrable function `g` vanishes, then its mollification by
any smooth compactly supported kernel is constant. -/
theorem mollification_const_of_forall_deriv_integral_zero {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (h : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, (fderiv ℝ ψ x) v * g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0)
    (k : EuclideanSpace ℝ (Fin n) → ℝ) (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k) :
    ∀ y y' : EuclideanSpace ℝ (Fin n),
      (∫ t, g t * k (y - t)) = (∫ t, g t * k (y' - t)) := by
  classical
  have hderiv : ∀ y, fderiv ℝ (fun y => ∫ t, g t * k (y - t)) y = 0 := by
    intro y
    refine ContinuousLinearMap.ext (fun v => ?_)
    have hs : ∀ z ∈ tsupport k,
        (y - z) ∈ (fun z : EuclideanSpace ℝ (Fin n) => y - z) '' tsupport k :=
      fun z hz => Set.mem_image_of_mem _ hz
    have hG : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
        tsupport φ ⊆ (fun z : EuclideanSpace ℝ (Fin n) => y - z) '' tsupport k →
        ∀ v' : EuclideanSpace ℝ (Fin n),
        ∫ x, g x * (fderiv ℝ φ x) v' = - ∫ x, φ x * ⟪(0 : EuclideanSpace ℝ (Fin n)), v'⟫_ℝ := by
      intro φ hφ hsub v'
      have hs_cpt : IsCompact ((fun z : EuclideanSpace ℝ (Fin n) => y - z) '' tsupport k) :=
        hkc.image (continuous_const.sub continuous_id)
      have hcomp : HasCompactSupport φ :=
        hs_cpt.of_isClosed_subset (isClosed_tsupport φ) hsub
      have hzero := h φ v' hφ hcomp
      have hcomm : ∫ x, g x * (fderiv ℝ φ x) v' = ∫ x, (fderiv ℝ φ x) v' * g x :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      rw [hcomm, hzero]
      simp
    have hkey := Commons.Analysis.Convolution.fderiv_moll_weakGrad k g (fun _ => 0)
        ((fun z : EuclideanSpace ℝ (Fin n) => y - z) '' tsupport k) y hk hkc hg
        (MeasureTheory.locallyIntegrable_zero) hs hG v
    rw [hkey]
    simp
  have hdiff : Differentiable ℝ (fun y => ∫ t, g t * k (y - t)) := by
    have hF_eq : MeasureTheory.convolution (𝕜 := ℝ) g k (ContinuousLinearMap.mul ℝ ℝ) volume
        = (fun y => ∫ t, g t * k (y - t)) := by
      funext z
      rw [MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.mul_apply']
    rw [← hF_eq]
    intro z
    exact (hkc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ) hg
      (hk.of_le (by simp)) z).differentiableAt
  intro y y'
  exact is_const_of_fderiv_eq_zero hdiff hderiv y y'

theorem ae_const_of_forall_deriv_integral_zero {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : MeasureTheory.LocallyIntegrable g (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (h : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, (fderiv ℝ ψ x) v * g x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) = 0) :
    ∃ c : ℝ, g =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))] fun _ => c := by
  classical
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun i =>
    ⟨((i : ℝ) + 1)⁻¹, 2 * ((i : ℝ) + 1)⁻¹,
      inv_pos.mpr (by positivity),
      by have hpos : (0:ℝ) < ((i:ℝ)+1)⁻¹ := inv_pos.mpr (by positivity); linarith⟩
  have hφ_tendsto : Tendsto (fun i => (φ i).rOut) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ => ((i:ℝ)+1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h2 := h1.const_mul 2
    simpa [φ] using h2
  have hφ_bound : ∀ᶠ i in atTop, (φ i).rOut ≤ 2 * (φ i).rIn :=
    Eventually.of_forall (fun i => le_of_eq (by simp [φ]))
  let F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i => MeasureTheory.convolution (𝕜 := ℝ)
      ((φ i).normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) g (lsmul ℝ ℝ) volume
  have hF_eq : ∀ i, F i = fun y =>
      ∫ t, g t * (φ i).normed (volume : Measure (EuclideanSpace ℝ (Fin n))) (y - t) := by
    intro i
    funext x
    dsimp only [F]
    rw [convolution_lsmul_swap]
    simp only [smul_eq_mul]
    exact integral_congr_ae (Eventually.of_forall (fun t => by ring))
  have hFconst : ∀ i y y', F i y = F i y' := by
    intro i y y'
    rw [hF_eq i]
    exact mollification_const_of_forall_deriv_integral_zero g hg h _
      (ContDiffBump.contDiff_normed (f := φ i) (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
      (ContDiffBump.hasCompactSupport_normed (f := φ i) (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
      y y'
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun i => F i x) atTop (𝓝 (g x)) := by
    have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (φ := φ) (l := atTop)
      (K := 2) hφ_tendsto hφ_bound hg
    simpa [F] using hconv
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ ≠ 0 := by
    have hpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1) := by
      apply Metric.measure_ball_pos; norm_num
    exact ne_of_gt (lt_of_lt_of_le hpos (measure_mono (Set.subset_univ _)))
  have hae' : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Set.univ),
      Tendsto (fun i => F i x) atTop (𝓝 (g x)) := by
    rw [Measure.restrict_univ]; exact hae
  obtain ⟨x₀, -, hx₀⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (s := Set.univ) hvol hae'
  refine ⟨g x₀, ?_⟩
  have hfin : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), g x = g x₀ := by
    filter_upwards [hae] with x hx
    have h2 : Tendsto (fun i => F i x) atTop (𝓝 (g x₀)) := by
      rw [show (fun i => F i x) = (fun i => F i x₀) from funext (fun i => hFconst i x x₀)]
      exact hx₀
    exact tendsto_nhds_unique hx h2
  exact hfin

end Commons.Analysis.GaussianMeasure