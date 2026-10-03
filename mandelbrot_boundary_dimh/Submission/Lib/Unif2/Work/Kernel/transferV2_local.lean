import Mathlib
import Submission.Lib.Unif2.Work.Drive.energyGreenRung
import Submission.Lib.Unif2.Work.Drive.greenEnergyPairing

/-!
# A local copy of `Work.Drive.pairTerm_transfer_v2`

The file `Submission/Work/Drive/energyTransferV2.lean` is temporarily broken (its four references to
`notMem_tsupport_clampedPullback` / `symm_mem_tsupport_of_mem_tsupport_clampedPullback` are
unqualified, but those lemmas now live in the namespace `Work.Drive.GreenRung`).  To stay
independent of that file this module carries its own copy of the single lemma, under a fresh
namespace.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

namespace Work.Kernel.TransferLocal

open Work.Drive
open Work.Drive.GreenRung

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
/-- **Generalized chart transfer for the Dirichlet pairing.** -/
theorem pairTerm_transfer_v2 [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x x' : X} {ρ σ ρ' σ' : ℝ} {V : Set X} (hV : IsOpen V)
    (hVx : V ⊆ (chartAt ℂ x).source) (hVx' : V ⊆ (chartAt ℂ x').source)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (htgt' : Metric.ball ((chartAt ℂ x') x') ρ' ⊆ (chartAt ℂ x').target)
    {ψ f g : X → ℝ}
    (hσρ : σ < ρ) (hσ'ρ' : σ' < ρ')
    (hsupx : ∀ y ∈ tsupport ψ, y ∈ tsupport g → (chartAt ℂ x) y ∈
      Metric.ball ((chartAt ℂ x) x) σ → y ∈ V)
    (hsupx' : ∀ y ∈ tsupport ψ, y ∈ tsupport g → (chartAt ℂ x') y ∈
      Metric.ball ((chartAt ℂ x') x') σ' → y ∈ V)
    (hVσ : ∀ y ∈ V, (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) σ)
    (hVσ' : ∀ y ∈ V, (chartAt ℂ x') y ∈ Metric.ball ((chartAt ℂ x') x') σ')
    (hf₂ : ∀ y ∈ V, DifferentiableAt ℝ (fun w : ℂ => f ((chartAt ℂ x').symm w))
      ((chartAt ℂ x') y))
    (hg₂ : ∀ y ∈ V, DifferentiableAt ℝ (fun w : ℂ => g ((chartAt ℂ x').symm w))
      ((chartAt ℂ x') y)) :
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
    inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z)
    with hWdef
  set W' : ℂ → ℝ := fun w => clampedPullback x' σ' ψ w *
    inner (𝕜 := ℝ) (gradient (clampedPullback x' ρ' f) w) (gradient (clampedPullback x' ρ' g) w)
    with hW'def
  change ∫ z, W z = ∫ w, W' w
  have hy_mem_s : ∀ z : ℂ, W z ≠ 0 → z ∈ s := by
    intro z hz
    have hb : z ∈ Metric.ball ((chartAt ℂ x) x) σ := by
      by_contra hb
      exact hz (by simp only [hWdef, clampedPullback_eq_zero_of_notMem_ball hb, zero_mul])
    have hbρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ := Metric.ball_subset_ball hσρ.le hb
    have hψne : clampedPullback x σ ψ z ≠ 0 := fun h0 =>
      hz (by simp only [hWdef, h0, zero_mul])
    have hyψ : (chartAt ℂ x).symm z ∈ tsupport ψ :=
      subset_tsupport _ (Function.mem_support.mpr (by
        rw [clampedPullback_apply_of_mem hb] at hψne; exact hψne))
    have hgne : gradient (clampedPullback x ρ g) z ≠ 0 :=
      fun h0 => hz (by simp only [hWdef, h0, inner_zero_right, mul_zero])
    have hyg : (chartAt ℂ x).symm z ∈ tsupport g :=
      symm_mem_tsupport_of_mem_tsupport_clampedPullback htgt (Metric.mem_ball.mp hbρ)
        (Work.Analysis.Harmonic.tsupport_gradient_subset (clampedPullback x ρ g)
          (subset_tsupport (gradient (clampedPullback x ρ g)) (Function.mem_support.mpr hgne)))
    have hyV : (chartAt ℂ x).symm z ∈ V :=
      hsupx _ hyψ hyg (by rw [(chartAt ℂ x).right_inv (htgt hbρ)]; exact hb)
    exact ⟨(chartAt ℂ x).symm z, hyV, (chartAt ℂ x).right_inv (htgt hbρ)⟩
  have hy'_mem_s : ∀ w : ℂ, W' w ≠ 0 → w ∈ τ '' s := by
    intro w hw
    have hb : w ∈ Metric.ball ((chartAt ℂ x') x') σ' := by
      by_contra hb
      exact hw (by simp only [hW'def, clampedPullback_eq_zero_of_notMem_ball hb, zero_mul])
    have hbρ : w ∈ Metric.ball ((chartAt ℂ x') x') ρ' := Metric.ball_subset_ball hσ'ρ'.le hb
    have hψne : clampedPullback x' σ' ψ w ≠ 0 := fun h0 =>
      hw (by simp only [hW'def, h0, zero_mul])
    have hyψ : (chartAt ℂ x').symm w ∈ tsupport ψ :=
      subset_tsupport _ (Function.mem_support.mpr (by
        rw [clampedPullback_apply_of_mem hb] at hψne; exact hψne))
    have hgne : gradient (clampedPullback x' ρ' g) w ≠ 0 :=
      fun h0 => hw (by simp only [hW'def, h0, inner_zero_right, mul_zero])
    have hyg : (chartAt ℂ x').symm w ∈ tsupport g :=
      symm_mem_tsupport_of_mem_tsupport_clampedPullback htgt' (Metric.mem_ball.mp hbρ)
        (Work.Analysis.Harmonic.tsupport_gradient_subset (clampedPullback x' ρ' g)
          (subset_tsupport (gradient (clampedPullback x' ρ' g)) (Function.mem_support.mpr hgne)))
    have hyV : (chartAt ℂ x').symm w ∈ V :=
      hsupx' _ hyψ hyg (by rw [(chartAt ℂ x').right_inv (htgt' hbρ)]; exact hb)
    exact ⟨(chartAt ℂ x) ((chartAt ℂ x').symm w), ⟨(chartAt ℂ x').symm w, hyV, rfl⟩, by
      simp only [hτ, (chartAt ℂ x).left_inv (hVx hyV),
        (chartAt ℂ x').right_inv (htgt' hbρ)]⟩
  have hWzero : ∀ z ∉ s, W z = 0 := fun z hz => by
    by_contra h
    exact hz (hy_mem_s z h)
  have hW'zero : ∀ w ∉ τ '' s, W' w = 0 := fun w hw => by
    by_contra h
    exact hw (hy'_mem_s w h)
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
  by_cases hz0 : y ∈ tsupport ψ ∧ y ∈ tsupport g
  · obtain ⟨hyψ, hyg⟩ := hz0
    have hzσ : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) σ := hVσ y hyV
    have hzρ : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
      Metric.ball_subset_ball hσρ.le hzσ
    have hτval : τ ((chartAt ℂ x) y) = (chartAt ℂ x') y := by
      simp only [hτ, hysym]
    have htσ' : τ ((chartAt ℂ x) y) ∈ Metric.ball ((chartAt ℂ x') x') σ' := by
      rw [hτval]; exact hVσ' y hyV
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
      by_cases hyψ : y ∈ tsupport ψ
      · have hyg : y ∉ tsupport g := fun h => hz0 ⟨hyψ, h⟩
        have hcy : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
          Metric.ball_subset_ball hσρ.le (hVσ y hyV)
        have hg0 : gradient (clampedPullback x ρ g) ((chartAt ℂ x) y) = 0 :=
          Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport
            (notMem_tsupport_clampedPullback (htgt hcy)
              (by rw [(chartAt ℂ x).left_inv (hVx hyV)]; exact hyg))
        simp only [hWdef, hg0, inner_zero_right, mul_zero]
      · have hψ0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hyψ
        simp only [hWdef, clampedPullback_apply_of_mem (hVσ y hyV), hysym, hψ0, zero_mul]
    have hW'0 : W' (τ ((chartAt ℂ x) y)) = 0 := by
      have hτval : τ ((chartAt ℂ x) y) = (chartAt ℂ x') y := by simp only [hτ, hysym]
      rw [hτval]
      by_cases hyψ : y ∈ tsupport ψ
      · have hyg : y ∉ tsupport g := fun h => hz0 ⟨hyψ, h⟩
        have hcy : (chartAt ℂ x') y ∈ Metric.ball ((chartAt ℂ x') x') ρ' :=
          Metric.ball_subset_ball hσ'ρ'.le (hVσ' y hyV)
        have hg0 : gradient (clampedPullback x' ρ' g) ((chartAt ℂ x') y) = 0 :=
          Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport
            (notMem_tsupport_clampedPullback (htgt' hcy)
              (by rw [(chartAt ℂ x').left_inv (hVx' hyV)]; exact hyg))
        simp only [hW'def, hg0, inner_zero_right, mul_zero]
      · have hψ0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hyψ
        have hleft : (chartAt ℂ x').symm ((chartAt ℂ x') y) = y :=
          (chartAt ℂ x').left_inv (hVx' hyV)
        simp only [hW'def, clampedPullback_apply_of_mem (hVσ' y hyV), hleft, hψ0, zero_mul]
    rw [hW0, hW'0, mul_zero]

end Work.Kernel.TransferLocal
