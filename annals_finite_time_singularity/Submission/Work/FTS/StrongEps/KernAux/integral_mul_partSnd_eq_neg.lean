import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.KernAux

open MeasureTheory Filter

/-- The derivative of the second-coordinate slice of a function of two variables is the
Fréchet derivative applied to the direction `(0,1)`. -/
private lemma deriv_slice_snd_eq_fderiv {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    deriv (fun θ' : ℝ => F (z, θ')) θ = fderiv ℝ F (z, θ) (0, 1) := by
  have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun t : ℝ => F (z, t))
      ((fderiv ℝ F (z, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
    (h.hasFDerivAt.comp θ h2).hasDerivAt
  rw [h3.deriv]; simp

/-- The second-coordinate slice of a `C¹` function is `C¹`. -/
private lemma contDiff_slice_snd {w : ℝ × ℝ → ℝ} (hw : ContDiff ℝ 1 w) (x : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => w (x, t)) :=
  hw.comp (contDiff_const.prodMk contDiff_id)

/-- The second-coordinate slice of a compactly supported function is compactly supported. -/
private lemma hasCompactSupport_slice_snd {w : ℝ × ℝ → ℝ} (hw : HasCompactSupport w)
    (x : ℝ) : HasCompactSupport (fun y : ℝ => w (x, y)) := by
  refine IsCompact.of_isClosed_subset (hw.isCompact.image continuous_snd) (isClosed_tsupport _)
    ?_
  refine closure_minimal ?_ (hw.isCompact.image continuous_snd).isClosed
  intro y hy
  exact ⟨(x, y), subset_closure (by simpa [Function.mem_support] using hy), rfl⟩

/-- **Integration by parts on `ℝ`, compactly supported case.**  For `a` of class `C¹` with
compact support and `b` of class `C¹`, we have `∫ a · b' = - ∫ a' · b`. -/
private lemma integral_mul_deriv_eq_neg_of_hasCompactSupport {a b : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hca : HasCompactSupport a) (hb : ContDiff ℝ 1 b) :
    ∫ y : ℝ, a y * deriv b y = - ∫ y : ℝ, deriv a y * b y := by
  have hDa : Continuous (deriv a) := ha.continuous_deriv le_rfl
  have hDb : Continuous (deriv b) := hb.continuous_deriv le_rfl
  have hda : ∀ y : ℝ, HasDerivAt a (deriv a y) y := fun y =>
    (ha.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdb : ∀ y : ℝ, HasDerivAt b (deriv b y) y := fun y =>
    (hb.differentiable (by norm_num)).differentiableAt.hasDerivAt
  refine MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := a) (v := b) (u' := deriv a) (v' := deriv b)
    (fun y _ => hda y) (fun y _ => hdb y) ?_ ?_ ?_
  · exact (ha.continuous.mul hDb).integrable_of_hasCompactSupport (hca.mul_right (f' := deriv b))
  · exact (hDa.mul hb.continuous).integrable_of_hasCompactSupport (hca.deriv.mul_right (f' := b))
  · exact (ha.continuous.mul hb.continuous).integrable_of_hasCompactSupport (hca.mul_right (f' := b))

/-- **Integration by parts in the second variable on `ℝ × ℝ`.**  If `u` is `C¹` with compact
support and `v` is `C¹`, then `∫ u ∂₂v = - ∫ (∂₂u) v`, where `∂₂` is the derivative of the
second-coordinate slice. -/
theorem integral_mul_partSnd_eq_neg {u v : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hus : HasCompactSupport u) (hv : ContDiff ℝ 1 v) :
    ∫ p : ℝ × ℝ, u p * deriv (fun t : ℝ => v (p.1, t)) p.2
      = - ∫ p : ℝ × ℝ, deriv (fun t : ℝ => u (p.1, t)) p.2 * v p := by
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdv : Differentiable ℝ v := hv.differentiable (by norm_num)
  -- Step 1: identify the slice derivatives with Fréchet derivatives
  have hstep1 : (∫ p : ℝ × ℝ, u p * deriv (fun t : ℝ => v (p.1, t)) p.2)
      = ∫ p : ℝ × ℝ, u p * fderiv ℝ v p (0, 1) :=
    integral_congr_ae (Eventually.of_forall fun p =>
      congrArg (fun c => u p * c) (deriv_slice_snd_eq_fderiv hdv.differentiableAt))
  have hstep2 : (∫ p : ℝ × ℝ, deriv (fun t : ℝ => u (p.1, t)) p.2 * v p)
      = ∫ p : ℝ × ℝ, fderiv ℝ u p (0, 1) * v p :=
    integral_congr_ae (Eventually.of_forall fun p =>
      congrArg (fun c => c * v p) (deriv_slice_snd_eq_fderiv hdu.differentiableAt))
  rw [hstep1, hstep2]
  -- Step 2: both integrands are continuous with compact support
  have hFint : Integrable (fun p : ℝ × ℝ => u p * fderiv ℝ v p (0, 1)) :=
    (hu.continuous.mul ((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport
        (hus.mul_right (f' := fun p : ℝ × ℝ => fderiv ℝ v p (0, 1)))
  have hGint : Integrable (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1) * v p) :=
    (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hv.continuous)
      |>.integrable_of_hasCompactSupport
        ((HasCompactSupport.fderiv_apply ℝ hus (0, 1)).mul_right (f' := v))
  -- Step 3: Fubini
  have hFub1 : (∫ p : ℝ × ℝ, u p * fderiv ℝ v p (0, 1))
      = ∫ x : ℝ, ∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1) := by
    have h : Integrable (fun p : ℝ × ℝ => u p * fderiv ℝ v p (0, 1)) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hFint
    have h2 := MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * fderiv ℝ v p (0, 1)) h
    rw [← Measure.volume_eq_prod] at h2
    exact h2
  have hFub2 : (∫ p : ℝ × ℝ, fderiv ℝ u p (0, 1) * v p)
      = ∫ x : ℝ, ∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y) := by
    have h : Integrable (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1) * v p) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hGint
    have h2 := MeasureTheory.integral_prod (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1) * v p) h
    rw [← Measure.volume_eq_prod] at h2
    exact h2
  rw [hFub1, hFub2]
  -- Step 4: the one-dimensional identity, slice by slice
  have hslice : ∀ x : ℝ, (∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1))
      = - ∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y) := by
    intro x
    have key := integral_mul_deriv_eq_neg_of_hasCompactSupport
      (contDiff_slice_snd hu x) (hasCompactSupport_slice_snd hus x) (contDiff_slice_snd hv x)
    have e1 : (∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1))
        = ∫ y : ℝ, u (x, y) * deriv (fun t : ℝ => v (x, t)) y :=
      integral_congr_ae (Eventually.of_forall fun y =>
        congrArg (fun c => u (x, y) * c)
          (deriv_slice_snd_eq_fderiv hdv.differentiableAt).symm)
    have e2 : (∫ y : ℝ, deriv (fun t : ℝ => u (x, t)) y * v (x, y))
        = ∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y) :=
      integral_congr_ae (Eventually.of_forall fun y =>
        congrArg (fun c => c * v (x, y))
          (deriv_slice_snd_eq_fderiv hdu.differentiableAt))
    rw [e1, key, e2]
  -- Step 5: integrate the slicewise identity
  rw [show (∫ x : ℝ, ∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1))
      = ∫ x : ℝ, -(∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y)) from
    integral_congr_ae (Eventually.of_forall hslice)]
  rw [integral_neg]

end Work.FTS.StrongEps.KernAux
