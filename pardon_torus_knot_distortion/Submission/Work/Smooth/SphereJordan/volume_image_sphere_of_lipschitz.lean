import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# A Lipschitz image of a circle in the plane has measure zero

The round circle `Metric.sphere c R ⊆ ℂ` is the image of `ℝ` under the `2π`-periodic Lipschitz
parametrisation `circleMap c R = fun θ ↦ c + R * exp (θ * I)`.  Hence its Hausdorff dimension is
at most `1`.  A map which is Lipschitz on the circle does not increase Hausdorff dimension, so the
image of the circle has Hausdorff dimension `< 2 = finrank ℝ ℂ`; since `volume` on `ℂ` is
absolutely continuous with respect to the `2`-dimensional Hausdorff measure, that image is
Lebesgue-null.
-/

namespace Work.Smooth.SphereJordan

open scoped NNReal ENNReal
open Complex

/-- The norm of a real number seen as a complex number. -/
private lemma norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simp

/-- The parametrisation `θ ↦ exp (θ * I)` of the unit circle is `2`-Lipschitz. -/
private lemma norm_exp_mul_I_sub_le (θ φ : ℝ) :
    ‖Complex.exp (θ * I) - Complex.exp (φ * I)‖ ≤ 2 * |θ - φ| := by
  have h : Complex.exp (θ * I) - Complex.exp (φ * I)
      = ((Real.cos θ - Real.cos φ : ℝ) : ℂ) + ((Real.sin θ - Real.sin φ : ℝ) : ℂ) * I := by
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_ofReal_complex, norm_mul, norm_ofReal_complex, Complex.norm_I, mul_one]
  have hc : |Real.cos θ - Real.cos φ| ≤ |θ - φ| := by
    simpa [Real.dist_eq] using Real.lipschitzWith_cos.dist_le_mul θ φ
  have hs : |Real.sin θ - Real.sin φ| ≤ |θ - φ| := by
    simpa [Real.dist_eq] using Real.lipschitzWith_sin.dist_le_mul θ φ
  linarith

/-- `circleMap c R` is Lipschitz on `ℝ`. -/
private lemma lipschitzWith_circleMap (c : ℂ) (R : ℝ) :
    LipschitzWith (2 * |R|).toNNReal (circleMap c R) := by
  refine LipschitzWith.of_dist_le_mul fun θ φ => ?_
  have h : circleMap c R θ - circleMap c R φ
      = (R : ℂ) * (Complex.exp (θ * I) - Complex.exp (φ * I)) := by
    simp only [circleMap]; ring
  rw [dist_eq_norm, dist_eq_norm, h, norm_mul, norm_ofReal_complex, Real.norm_eq_abs]
  rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 2 * |R|)]
  calc |R| * ‖Complex.exp (θ * I) - Complex.exp (φ * I)‖
      ≤ |R| * (2 * |θ - φ|) :=
        mul_le_mul_of_nonneg_left (norm_exp_mul_I_sub_le θ φ) (abs_nonneg R)
    _ = 2 * |R| * |θ - φ| := by ring

/-- Every point of the circle `Metric.sphere c R` is of the form `circleMap c R θ`. -/
private lemma exists_circleMap_eq_of_mem_sphere {c z : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ Metric.sphere c R) : ∃ θ : ℝ, circleMap c R θ = z := by
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · refine ⟨0, ?_⟩
    have hzc : z = c := sub_eq_zero.mp (norm_eq_zero.mp (by
      rw [Metric.mem_sphere, dist_eq_norm] at hz; exact hz))
    rw [circleMap_zero_radius]
    exact hzc.symm
  · have hzR : ‖z - c‖ = R := by
      rwa [Metric.mem_sphere, dist_eq_norm] at hz
    have hRu : (R : ℂ) ≠ 0 := by
      simpa using hRpos.ne'
    set u : ℂ := (z - c) / (R : ℂ) with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_div, norm_ofReal_complex, abs_of_nonneg hR, hzR, div_self hRpos.ne']
    have harg : Complex.exp ((u.arg : ℂ) * I) = u := by
      have h := Complex.norm_mul_exp_arg_mul_I u
      rw [hunorm] at h
      simpa using h
    refine ⟨u.arg, ?_⟩
    rw [circleMap, harg, hu]
    field_simp
    ring

/-- The circle of radius `R ≥ 0` around `c` is the image of `ℝ` under `circleMap c R`. -/
private lemma sphere_eq_image_circleMap {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    Metric.sphere c R = circleMap c R '' Set.univ := by
  ext z
  constructor
  · intro hz
    obtain ⟨θ, hθ⟩ := exists_circleMap_eq_of_mem_sphere hR hz
    exact ⟨θ, trivial, hθ⟩
  · rintro ⟨θ, -, rfl⟩
    exact circleMap_mem_sphere c hR θ

theorem volume_image_sphere_of_lipschitz {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ} {L : NNReal}
    (hf : LipschitzOnWith L f (Metric.sphere c R)) :
    MeasureTheory.volume (f '' Metric.sphere c R) = 0 := by
  -- the circle has Hausdorff dimension at most `1`
  have hdimH : dimH (Metric.sphere c R) ≤ 1 := by
    calc dimH (Metric.sphere c R) = dimH (circleMap c R '' Set.univ) := by
          rw [sphere_eq_image_circleMap hR]
      _ ≤ dimH (Set.univ : Set ℝ) := (lipschitzWith_circleMap c R).dimH_image_le _
      _ = 1 := Real.dimH_univ
  -- so the Lipschitz image of the circle has Hausdorff dimension `< 2 = finrank ℝ ℂ`
  have hlt : dimH (f '' Metric.sphere c R) < ((Module.finrank ℝ ℂ : ℝ≥0) : ℝ≥0∞) := by
    refine lt_of_le_of_lt (le_trans hf.dimH_image_le hdimH) ?_
    rw [Complex.finrank_real_complex]
    norm_num
  -- and `volume` on `ℂ` is absolutely continuous with respect to `μH[2]`
  haveI : (MeasureTheory.Measure.hausdorffMeasure
      (((Module.finrank ℝ ℂ : ℝ≥0) : ℝ)) : MeasureTheory.Measure ℂ).IsAddHaarMeasure :=
    MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := ℂ)
  exact measure_zero_of_dimH_lt (d := (Module.finrank ℝ ℂ : ℝ≥0))
    (MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      (MeasureTheory.Measure.hausdorffMeasure
        (((Module.finrank ℝ ℂ : ℝ≥0) : ℝ)) : MeasureTheory.Measure ℂ)) hlt

end Work.Smooth.SphereJordan
