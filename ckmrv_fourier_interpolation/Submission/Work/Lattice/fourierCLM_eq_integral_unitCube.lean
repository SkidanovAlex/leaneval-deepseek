import Submission.Work.Lattice.poissonTorus
import Submission.Work.Lattice.integral_eq_tsum_intVec
import Submission.Work.Lattice.fourierCLM_apply_eq_integral
import Submission.Work.Lattice.summable_integral_norm_schwartz_add_intVec

/-!
# The Fourier transform as an integral over the unit cube

For a Schwartz function `f` on `ℝⁿ` and `w ∈ ℤⁿ`, the Fourier transform `𝓕 f (w)` is the
integral over the unit cube `(0,1]ⁿ` of the periodization `∑_{v ∈ ℤⁿ} f (x + v)` twisted by
the character `mFourier (-w)`.  This is the key step in Poisson summation: it identifies the
Fourier coefficients of the periodization with the Fourier transform of `f`.
-/

namespace Work.Lattice

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

set_option maxHeartbeats 800000 in
/-- **The Fourier transform as a twisted integral over the unit cube.** -/
theorem fourierCLM_eq_integral_unitCube {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (w : Fin n → ℤ) :
    (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
        (WithLp.toLp 2 (intVecToReal w))
      = ∫ x in unitCube n,
          UnitAddTorus.mFourier (-w) (fun i => (x i : UnitAddCircle)) • periodization f x := by
  have hD6 : Summable fun v : Fin n → ℤ =>
      ∫ x in unitCube n, ‖f (WithLp.toLp 2 (x + intVecToReal v))‖ :=
    summable_integral_norm_schwartz_add_intVec f
  have hfi : Integrable (fun y : Fin n → ℝ => f (WithLp.toLp 2 y)) :=
    ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding).mpr f.integrable
  rw [fourierCLM_apply_eq_integral]
  change (∫ y : Fin n → ℝ, UnitAddTorus.mFourier (-w) (fun i => (y i : UnitAddCircle))
        * f (WithLp.toLp 2 y))
      = ∫ x in unitCube n, UnitAddTorus.mFourier (-w) (fun i => (x i : UnitAddCircle))
          • periodization f x
  have hgnorm : ∀ v : Fin n → ℤ, Integrable (fun x : Fin n → ℝ =>
      ‖f (WithLp.toLp 2 (x + intVecToReal v))‖) (volume.restrict (unitCube n)) := fun v =>
    ((hfi.comp_add_right (intVecToReal v)).mono_measure Measure.restrict_le_self).norm
  have hGint : Integrable (fun y : Fin n → ℝ =>
      UnitAddTorus.mFourier (-w) (fun i => (y i : UnitAddCircle)) * f (WithLp.toLp 2 y)) := by
    refine Integrable.mono' hfi.norm ?_ ?_
    · fun_prop
    · filter_upwards with y
      simpa using norm_mFourier_mul_le w _ _
  rw [integral_eq_tsum_intVec _ hGint]
  have hInt : ∀ v : Fin n → ℤ, Integrable (fun x : Fin n → ℝ =>
      UnitAddTorus.mFourier (-w) (fun i => (x i : UnitAddCircle))
        * f (WithLp.toLp 2 (x + intVecToReal v))) (volume.restrict (unitCube n)) := by
    intro v
    refine Integrable.mono' (hgnorm v) ?_ ?_
    · fun_prop
    · filter_upwards with x
      simpa using norm_mFourier_mul_le w _ _
  have hsum : Summable fun v : Fin n → ℤ => ∫ x in unitCube n, ‖UnitAddTorus.mFourier (-w)
      (fun i => (x i : UnitAddCircle))
        * f (WithLp.toLp 2 (x + intVecToReal v))‖ := by
    refine Summable.of_nonneg_of_le (fun v => integral_nonneg fun x => norm_nonneg _) (fun v => ?_) hD6
    refine integral_mono ?_ (hgnorm v) (fun x => ?_)
    · refine Integrable.mono' (hgnorm v) ?_ ?_
      · fun_prop
      · filter_upwards with x
        simpa using norm_mFourier_mul_le w _ _
    · simpa using norm_mFourier_mul_le w _ _
  rw [show (∑' v : Fin n → ℤ, ∫ x in unitCube n,
      UnitAddTorus.mFourier (-w) (fun i => ((x + intVecToReal v) i : UnitAddCircle))
        * f (WithLp.toLp 2 (x + intVecToReal v)))
      = ∑' v : Fin n → ℤ, ∫ x in unitCube n,
        UnitAddTorus.mFourier (-w) (fun i => (x i : UnitAddCircle))
          * f (WithLp.toLp 2 (x + intVecToReal v)) from by
      refine tsum_congr fun v => ?_
      refine integral_congr_ae ?_
      filter_upwards with x
      simp only [Pi.add_apply, intVecToReal_apply]
      rw [mFourier_add_intVec]]
  rw [integral_tsum_of_summable_integral_norm hInt hsum]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [tsum_mul_left, smul_eq_mul]
  rfl

end Work.Lattice
