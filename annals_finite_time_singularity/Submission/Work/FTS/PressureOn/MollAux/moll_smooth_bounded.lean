/-
Auxiliary facts about the mollifiers of `Work.FTS.PressureOn.weyl_pair`: `moll n g` and
`mollV n G` are smooth (all finite orders), they preserve the sup-norm bound of the mollified
function, and the scalar mollification has a bounded gradient.  The last point is what makes the
mollification usable as a smooth approximation in the Weyl/Liouville argument of `weyl_pair`.

All the work is done by the fact that `moll`/`mollV` are convolutions with the smooth compactly
supported `rho n`, together with the elementary integral representation
`moll n g x = ∫ t, rho n t * g (x - t)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

namespace MollSB

/-- The normalised bump `rho n` is nonnegative. -/
theorem nonneg_rho (n : ℕ) (t : R3) : 0 ≤ rho n t :=
  ContDiffBump.nonneg_normed (bump n) (μ := volume) t

/-- The normalised bump `rho n` is smooth. -/
theorem contDiff_rho (n : ℕ) (m : ℕ∞) : ContDiff ℝ (m : ℕ∞) (rho n) :=
  ContDiffBump.contDiff_normed (bump n) (μ := volume)

/-- The normalised bump `rho n` has compact support. -/
theorem hasCompactSupport_rho (n : ℕ) : HasCompactSupport (rho n) :=
  ContDiffBump.hasCompactSupport_normed (bump n) (μ := volume)

/-- The normalised bump `rho n` is integrable. -/
theorem integrable_rho (n : ℕ) : Integrable (rho n) volume :=
  ContDiffBump.integrable_normed (bump n) (μ := volume)

/-- The normalised bump `rho n` has integral one. -/
theorem integral_rho (n : ℕ) : ∫ t, rho n t = 1 :=
  ContDiffBump.integral_normed (bump n) (μ := volume)

/-- The scalar mollification as an integral against `rho n`. -/
theorem moll_eq_integral_rho (n : ℕ) (g : R3 → ℝ) (x : R3) :
    moll n g x = ∫ t, rho n t * g (x - t) := by
  simp only [moll, MeasureTheory.convolution]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The vector mollification as an integral against `rho n`. -/
theorem mollV_eq_integral_rho (n : ℕ) (G : R3 → R3) (x : R3) :
    mollV n G x = ∫ t, rho n t • G (x - t) := by
  simp only [mollV, MeasureTheory.convolution]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [ContinuousLinearMap.lsmul_apply]

/-- The scalar mollification of a continuous function is smooth. -/
theorem contDiff_moll (n : ℕ) (g : R3 → ℝ) (hg : Continuous g) :
    ∀ m : ℕ, ContDiff ℝ m (moll n g) := fun m =>
  (hasCompactSupport_rho n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_rho n (m : ℕ∞)) hg.locallyIntegrable

/-- The vector mollification of a continuous function is smooth. -/
theorem contDiff_mollV (n : ℕ) (G : R3 → R3) (hG : Continuous G) :
    ∀ m : ℕ, ContDiff ℝ m (mollV n G) := fun m =>
  (hasCompactSupport_rho n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_rho n (m : ℕ∞)) hG.locallyIntegrable

/-- The scalar mollification does not increase the sup-norm. -/
theorem abs_moll_le (n : ℕ) (g : R3 → ℝ) (C : ℝ) (hC : ∀ x, |g x| ≤ C) (x : R3) :
    |moll n g x| ≤ C := by
  have hφ0 : ∀ t, 0 ≤ rho n t := nonneg_rho n
  rw [moll_eq_integral_rho]
  rw [← Real.norm_eq_abs]
  calc ‖∫ t, rho n t * g (x - t)‖
      ≤ ∫ t, ‖rho n t * g (x - t)‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t, rho n t * |g (x - t)| := by
        refine integral_congr_ae ?_
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 t)]
    _ ≤ ∫ t, rho n t * C := by
        refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun t => ?_)
          ((integrable_rho n).mul_const C) (ae_of_all _ fun t => ?_)
        · exact mul_nonneg (hφ0 t) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left (hC (x - t)) (hφ0 t)
    _ = (∫ t, rho n t) * C := MeasureTheory.integral_mul_const C _
    _ = C := by rw [integral_rho n, one_mul]

/-- The vector mollification does not increase the sup-norm. -/
theorem norm_mollV_le (n : ℕ) (G : R3 → R3) (D : ℝ) (hD : ∀ x, ‖G x‖ ≤ D) (x : R3) :
    ‖mollV n G x‖ ≤ D := by
  have hφ0 : ∀ t, 0 ≤ rho n t := nonneg_rho n
  rw [mollV_eq_integral_rho]
  calc ‖∫ t, rho n t • G (x - t)‖
      ≤ ∫ t, ‖rho n t • G (x - t)‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t, rho n t * ‖G (x - t)‖ := by
        refine integral_congr_ae ?_
        filter_upwards with t
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ0 t)]
    _ ≤ ∫ t, rho n t * D := by
        refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun t => ?_)
          ((integrable_rho n).mul_const D) (ae_of_all _ fun t => ?_)
        · exact mul_nonneg (hφ0 t) (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left (hD (x - t)) (hφ0 t)
    _ = (∫ t, rho n t) * D := MeasureTheory.integral_mul_const D _
    _ = D := by rw [integral_rho n, one_mul]

/-- The total derivative of the scalar mollification, evaluated at `x`, is the convolution of
`fderiv ℝ (rho n)` with `g` under `ContinuousLinearMap.precompL R3 (lsmul ℝ ℝ)`. -/
theorem hasFDerivAt_moll (n : ℕ) (g : R3 → ℝ) (hg : Continuous g) (x : R3) :
    HasFDerivAt (moll n g)
      (MeasureTheory.convolution (fderiv ℝ (rho n)) g
        (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) volume x) x :=
  (hasCompactSupport_rho n).hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_rho n 1) hg.locallyIntegrable x

/-- `precompL R3 (lsmul ℝ ℝ)` applied to `u : R3 →L[ℝ] ℝ` and `c : ℝ` is the map `v ↦ c * u v`,
i.e. the scalar multiple `c • u`. -/
theorem precompL_lsmul_apply (u : R3 →L[ℝ] ℝ) (c : ℝ) :
    (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) u c = c • u := by
  ext v
  rw [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_apply,
    smul_eq_mul, smul_eq_mul, mul_comm]

/-- The gradient of the scalar mollification is bounded by `C ∫ ‖fderiv ℝ (rho n)‖` whenever
`|g| ≤ C`. -/
theorem norm_fderiv_moll_le (n : ℕ) (g : R3 → ℝ) (hg : Continuous g) (C : ℝ)
    (hC : ∀ x, |g x| ≤ C) (x : R3) :
    ‖fderiv ℝ (moll n g) x‖ ≤ C * ∫ t, ‖fderiv ℝ (rho n) t‖ := by
  have hcs : HasCompactSupport (rho n) := hasCompactSupport_rho n
  have hcont' : Continuous (fderiv ℝ (rho n)) :=
    (contDiff_rho n 2).continuous_fderiv (by norm_num)
  have hint : Integrable (fun t => ‖fderiv ℝ (rho n) t‖) volume :=
    (hcont'.integrable_of_hasCompactSupport (hcs.fderiv ℝ)).norm
  have hterm : ∀ t, ‖(ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ))
      (fderiv ℝ (rho n) t) (g (x - t))‖ ≤ C * ‖fderiv ℝ (rho n) t‖ := by
    intro t
    rw [precompL_lsmul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC (x - t)) (norm_nonneg _)
  rw [HasFDerivAt.fderiv (hasFDerivAt_moll n g hg x)]
  simp only [MeasureTheory.convolution]
  calc ‖∫ t, (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ))
        (fderiv ℝ (rho n) t) (g (x - t))‖
      ≤ ∫ t, ‖(ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ))
        (fderiv ℝ (rho n) t) (g (x - t))‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, C * ‖fderiv ℝ (rho n) t‖ := by
        refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _)
          (hint.const_mul C) (ae_of_all _ fun t => hterm t)
    _ = C * ∫ t, ‖fderiv ℝ (rho n) t‖ := MeasureTheory.integral_const_mul C _

end MollSB

theorem moll_smooth_bounded (n : ℕ) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hg : Continuous g) (hG : Continuous G) (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (D : ℝ) (hD : ∀ x, ‖G x‖ ≤ D) :
    (∀ m : ℕ, ContDiff ℝ m (Work.FTS.PressureOn.moll n g)) ∧
    (∀ m : ℕ, ContDiff ℝ m (Work.FTS.PressureOn.mollV n G)) ∧
    (∀ x, |Work.FTS.PressureOn.moll n g x| ≤ C) ∧
    (∀ x, ‖Work.FTS.PressureOn.mollV n G x‖ ≤ D) ∧
    (∃ C' : ℝ, ∀ x, ‖fderiv ℝ (Work.FTS.PressureOn.moll n g) x‖ ≤ C') :=
  ⟨MollSB.contDiff_moll n g hg, MollSB.contDiff_mollV n G hG,
    fun x => MollSB.abs_moll_le n g C hC x, fun x => MollSB.norm_mollV_le n G D hD x,
    ⟨C * ∫ t, ‖fderiv ℝ (Work.FTS.PressureOn.rho n) t‖,
      fun x => MollSB.norm_fderiv_moll_le n g hg C hC x⟩⟩

end Work.FTS.PressureOn.MollAux
