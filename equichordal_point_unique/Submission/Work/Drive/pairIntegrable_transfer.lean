import Mathlib
import Submission.Work.Drive.greenEnergyPairing
import Submission.Work.Drive.energyGreenRung

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Drive

theorem pairIntegrable_transfer {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
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
    (hg₂ : ∀ y ∈ V, DifferentiableAt ℝ (fun w : ℂ => g ((chartAt ℂ x').symm w)) ((chartAt ℂ x') y))
    (h : Work.Drive.PairIntegrable x ρ σ ψ f g) : Work.Drive.PairIntegrable x' ρ' σ' ψ f g := by
  classical
  -- The conformal chart transition from the chart at `x` to the chart at `x'`.
  set τ : ℂ → ℂ := fun z => (chartAt ℂ x') ((chartAt ℂ x).symm z) with hτ
  -- Its source: the image of `V` under the chart at `x`.
  set s : Set ℂ := (chartAt ℂ x) '' V with hs
  have hτan : ∀ z ∈ s, DifferentiableAt ℂ τ z := by
    rintro z ⟨y, hyV, rfl⟩
    exact (Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ x')
      (chart_mem_atlas ℂ x) ((chartAt ℂ x) y) ((chartAt ℂ x).map_source (hVx hyV))
      (by rw [(chartAt ℂ x).left_inv (hVx hyV)]; exact hVx' hyV)).differentiableAt
  have hτinj : Set.InjOn τ s := by
    rintro z ⟨y, hyV, rfl⟩ z' ⟨y', hy'V, rfl⟩ hh
    simp only [hτ, (chartAt ℂ x).left_inv (hVx hyV), (chartAt ℂ x).left_inv (hVx hy'V)] at hh
    rw [(chartAt ℂ x').injOn (hVx' hyV) (hVx' hy'V) hh]
  have hso : IsOpen s := (chartAt ℂ x).isOpen_image_of_subset_source hV hVx
  have hs_meas : MeasurableSet s := hso.measurableSet
  -- The image of `s` under `τ` is the image of `V` under the chart at `x'`, hence open.
  have hsf' : τ '' s = (chartAt ℂ x') '' V := by
    ext w
    constructor
    · rintro ⟨z, ⟨y, hyV, rfl⟩, rfl⟩
      exact ⟨y, hyV, by simp only [hτ, (chartAt ℂ x).left_inv (hVx hyV)]⟩
    · rintro ⟨y, hyV, rfl⟩
      exact ⟨(chartAt ℂ x) y, ⟨y, hyV, rfl⟩,
        by simp only [hτ, (chartAt ℂ x).left_inv (hVx hyV)]⟩
  have hImo : IsOpen (τ '' s) := by
    rw [hsf']
    exact (chartAt ℂ x').isOpen_image_of_subset_source hV hVx'
  have hIm_meas : MeasurableSet (τ '' s) := hImo.measurableSet
  -- Unfold the two integrands.
  rw [PairIntegrable]
  set W' : ℂ → ℝ := fun w => clampedPullback x' σ' ψ w *
    inner (𝕜 := ℝ) (gradient (clampedPullback x' ρ' f) w) (gradient (clampedPullback x' ρ' g) w)
    with hW'def
  set W : ℂ → ℝ := fun z => clampedPullback x σ ψ z *
    inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z)
    with hWdef
  change Integrable W' volume
  rw [PairIntegrable] at h
  change Integrable W volume at h
  -- The integrand in the chart at `x` vanishes off `s`.
  have hWzero : ∀ z ∉ s, W z = 0 := by
    intro z hz
    by_cases hb : z ∈ Metric.ball ((chartAt ℂ x) x) σ
    · have hψ0 : ψ ((chartAt ℂ x).symm z) = 0 := by
        by_contra hne
        exact hz ⟨(chartAt ℂ x).symm z,
          hsuppV (subset_tsupport _ (Function.mem_support.mpr hne)),
          (chartAt ℂ x).right_inv (htgt (Metric.ball_subset_ball hσρ.le hb))⟩
      simp only [hWdef, clampedPullback_apply_of_mem hb, hψ0, zero_mul]
    · simp only [hWdef, clampedPullback_eq_zero_of_notMem_ball hb, zero_mul]
  -- The integrand in the chart at `x'` vanishes off `τ '' s`.
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
  -- The two integrands are related by the conformal factor of the chart transition, on `s`.
  have hpoint : ∀ z ∈ s, W z = ‖deriv τ z‖ ^ 2 * W' (τ z) := by
    intro z hz
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
      have hw : clampedPullback x σ ψ ((chartAt ℂ x) y)
          = clampedPullback x' σ' ψ (τ ((chartAt ℂ x) y)) := by
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
  -- Version with the honest Jacobian determinant.
  have hpoint' : ∀ z ∈ s, |(fderiv ℝ τ z).det| • W' (τ z) = W z := by
    intro z hz
    rw [Work.Jordan.fderiv_eq_smul_one (hτan z hz), Work.Jordan.det_smul_one_complex,
      abs_of_nonneg (sq_nonneg _), smul_eq_mul]
    exact (hpoint z hz).symm
  -- Integrability transfers across the chart transition.
  have hA : IntegrableOn W s volume :=
    (integrableOn_iff_integrable_of_support_subset (f := W) (s := s)
      (fun u hu => by
        by_contra hus
        exact (Function.mem_support.mp hu) (hWzero u hus))).mpr h
  have hB : IntegrableOn (fun z => |(fderiv ℝ τ z).det| • W' (τ z)) s volume :=
    hA.congr_fun_ae (by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hs_meas]
      exact Filter.Eventually.of_forall fun z hz => (hpoint' z hz).symm)
  have hC : IntegrableOn W' (τ '' s) volume :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      (f := τ) (f' := fun z => fderiv ℝ τ z) (s := s) (g := W') hs_meas
      (fun z hz => ((hτan z hz).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
      hτinj).mpr hB
  exact (integrableOn_iff_integrable_of_support_subset (f := W') (s := τ '' s)
    (fun u hu => by
      by_contra hus
      exact (Function.mem_support.mp hu) (hW'zero u hus))).mp hC

end Work.Drive
