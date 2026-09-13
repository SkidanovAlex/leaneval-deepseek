import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

set_option maxHeartbeats 1600000

namespace Commons.Analysis.Convolution

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution in
theorem fderiv_fderiv_moll_apply {n : ℕ} (k u : EuclideanSpace ℝ (Fin n) → ℝ)
    (y v w : EuclideanSpace ℝ (Fin n))
    (hk : HasCompactSupport k) (hku : ContDiff ℝ (⊤ : ℕ∞) k) (hu : LocallyIntegrable u volume) :
    (fderiv ℝ (fderiv ℝ (fun y => ∫ t, u t * k (y - t) ∂volume)) y) v w
      = ∫ t, u t * ((fderiv ℝ (fderiv ℝ k) (y - t)) v w) ∂volume := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ∫ t, u t * k (z - t) ∂volume
  let D1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fderiv ℝ k
  let D2 : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fderiv ℝ (fderiv ℝ k)
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun a => D1 a w
  have hk1 : ContDiff ℝ (1 : WithTop ℕ∞) k := hku.of_le (by simp)
  have hD1_inf : ContDiff ℝ (⊤ : ℕ∞) D1 := (contDiff_infty_iff_fderiv.mp hku).2
  have hD1_cs : HasCompactSupport D1 := hk.fderiv ℝ
  have hD1_cont : Continuous D1 := hD1_inf.continuous
  have hg_inf : ContDiff ℝ (⊤ : ℕ∞) g := hD1_inf.clm_apply contDiff_const
  have hg1 : ContDiff ℝ (1 : WithTop ℕ∞) g := hg_inf.of_le (by simp)
  have hg_cs : HasCompactSupport g := by
    exact hD1_cs.comp_left
      (g := fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A w) (by simp)
  have hF_eq : MeasureTheory.convolution (𝕜 := ℝ) u k (ContinuousLinearMap.mul ℝ ℝ) volume = F := by
    funext z
    simp only [F]
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
  have hF_deriv (z : EuclideanSpace ℝ (Fin n)) : fderiv ℝ F z =
      MeasureTheory.convolution (𝕜 := ℝ) u D1
        (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
          (ContinuousLinearMap.mul ℝ ℝ)) volume z := by
    have h := hk.hasFDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ) hu hk1 z
    rw [hF_eq] at h
    exact h.fderiv
  have hfderivF_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := by
    have hEq : fderiv ℝ F = MeasureTheory.convolution (𝕜 := ℝ) u D1
        (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
          (ContinuousLinearMap.mul ℝ ℝ)) volume := funext hF_deriv
    rw [hEq]
    exact hD1_cs.contDiff_convolution_right
      (L := ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
        (ContinuousLinearMap.mul ℝ ℝ)) hu hD1_inf
  have hP_eq : (fun z => (fderiv ℝ F z) w)
      = MeasureTheory.convolution (𝕜 := ℝ) u g (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext z
    rw [hF_deriv z]
    exact convolution_precompR_apply (L := ContinuousLinearMap.mul ℝ ℝ)
      (f := u) (g := D1) (μ := volume) hu hD1_cs hD1_cont z w
  have hP_deriv : HasFDerivAt (fun z => (fderiv ℝ F z) w)
      (MeasureTheory.convolution (𝕜 := ℝ) u (fderiv ℝ g)
        (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
          (ContinuousLinearMap.mul ℝ ℝ)) volume y) y := by
    rw [hP_eq]
    exact hg_cs.hasFDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ) hu hg1 y
  have hg_deriv (a : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ g a = (ContinuousLinearMap.apply ℝ ℝ w).comp (D2 a) := by
    have hD1_hfd : HasFDerivAt D1 (D2 a) a := by
      have hd : DifferentiableAt ℝ D1 a := (hD1_inf.differentiable (by simp)).differentiableAt
      simpa [D2] using hd.hasFDerivAt
    have he : HasFDerivAt (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A w)
        (ContinuousLinearMap.apply ℝ ℝ w) (D1 a) :=
      (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt
    have hcomp := he.comp a hD1_hfd
    have h := hcomp.fderiv
    change fderiv ℝ (fun x => (D1 x) w) a =
      (ContinuousLinearMap.apply ℝ ℝ w).comp (D2 a)
    exact h
  have hfinal : (fderiv ℝ (fun z => (fderiv ℝ F z) w) y) v
      = ∫ t, u t * (D2 (y - t) v w) ∂volume := by
    rw [hP_deriv.fderiv]
    have hfderiv_g_cs : HasCompactSupport (fderiv ℝ g) := hg_cs.fderiv ℝ
    have hfderiv_g_cont : Continuous (fderiv ℝ g) := hg_inf.continuous_fderiv (by simp)
    rw [convolution_precompR_apply (L := ContinuousLinearMap.mul ℝ ℝ)
      (f := u) (g := fderiv ℝ g) (μ := volume) hu hfderiv_g_cs hfderiv_g_cont y v]
    rw [MeasureTheory.convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    congr 1
    rw [hg_deriv (y - t)]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have hchain : (fderiv ℝ (fun z => (fderiv ℝ F z) w) y) v
      = (fderiv ℝ (fderiv ℝ F) y) v w := by
    have hf : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y := by
      have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
        (hfderivF_smooth.differentiable (by simp)).differentiableAt
      exact hd.hasFDerivAt
    have he : HasFDerivAt (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A w)
        (ContinuousLinearMap.apply ℝ ℝ w) (fderiv ℝ F y) :=
      (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt
    have hcomp := he.comp y hf
    have hEq : fderiv ℝ (fun z => (fderiv ℝ F z) w) y
        = (ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ F) y) := hcomp.fderiv
    rw [hEq]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  change (fderiv ℝ (fderiv ℝ F) y) v w = ∫ t, u t * (D2 (y - t) v w) ∂volume
  rw [← hchain]
  exact hfinal

end Commons.Analysis.Convolution