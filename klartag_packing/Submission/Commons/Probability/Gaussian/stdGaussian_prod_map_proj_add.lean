import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Commons.Probability.Gaussian

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For an orthogonal projection `p`, the decomposition `t = p t + (1 - p) t` is orthogonal, so
the squared norms add up. -/
private lemma norm_sq_eq_proj (p : E →L[ℝ] E)
    (hp : p.comp p = p) (hsym : ∀ x y : E, inner ℝ (p x) y = inner ℝ x (p y)) (t : E) :
    ‖t‖ ^ 2 = ‖p t‖ ^ 2 + ‖(ContinuousLinearMap.id ℝ E - p) t‖ ^ 2 := by
  have h1 : p (p t) = p t := by
    have h := DFunLike.congr_fun hp t
    rwa [ContinuousLinearMap.comp_apply] at h
  have hq : (ContinuousLinearMap.id ℝ E - p) t = t - p t := by
    simp
  have hinner : inner ℝ (p t) ((ContinuousLinearMap.id ℝ E - p) t) = 0 := by
    rw [hq, inner_sub_right, ← hsym (p t) t, h1, sub_self]
  have hx : t = p t + (ContinuousLinearMap.id ℝ E - p) t := by
    rw [hq]; abel
  calc ‖t‖ ^ 2 = ‖p t + (ContinuousLinearMap.id ℝ E - p) t‖ ^ 2 := by rw [← hx]
    _ = ‖p t‖ ^ 2 + ‖(ContinuousLinearMap.id ℝ E - p) t‖ ^ 2 := by
        rw [pow_two, pow_two, pow_two,
          norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, hinner]

/-- Adjointness of the complementary projection `1 - p` of an orthogonal projection. -/
private lemma inner_sub_proj (p : E →L[ℝ] E)
    (hsym : ∀ x y : E, inner ℝ (p x) y = inner ℝ x (p y)) (x y : E) :
    inner ℝ ((ContinuousLinearMap.id ℝ E - p) x) y
      = inner ℝ x ((ContinuousLinearMap.id ℝ E - p) y) := by
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right, hsym]

/-- The inner product of `p z + (1 - p) w` with `t`. -/
private lemma inner_proj_add (p : E →L[ℝ] E)
    (hsym : ∀ x y : E, inner ℝ (p x) y = inner ℝ x (p y)) (z w t : E) :
    inner ℝ (p z + (ContinuousLinearMap.id ℝ E - p) w) t
      = inner ℝ z (p t) + inner ℝ w ((ContinuousLinearMap.id ℝ E - p) t) := by
  rw [inner_add_left, hsym z t, inner_sub_proj p hsym w t]

/-- **Klartag's Gaussian projection identity.** If `p` is an orthogonal projection on a
finite-dimensional real inner product space `E`, then `p X + (1 - p) Y` is a standard Gaussian
whenever `X` and `Y` are independent standard Gaussians. -/
theorem stdGaussian_prod_map_proj_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (p : E →L[ℝ] E)
    (hp : p.comp p = p) (hsym : ∀ x y : E, inner ℝ (p x) y = inner ℝ x (p y)) :
    ((ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E)).map
        (fun z : E × E => p z.1 + (ContinuousLinearMap.id ℝ E - p) z.2)
      = ProbabilityTheory.stdGaussian E := by
  set q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - p with hq
  have key : ∀ t : E, ‖t‖ ^ 2 = ‖p t‖ ^ 2 + ‖q t‖ ^ 2 := by
    intro t
    have h := norm_sq_eq_proj p hp hsym t
    rwa [← hq] at h
  have hinnerq : ∀ x y : E, inner ℝ (q x) y = inner ℝ x (q y) := by
    intro x y
    have h := inner_sub_proj p hsym x y
    rwa [← hq] at h
  have hinneradd : ∀ z : E × E, ∀ t : E,
      inner ℝ (p z.1 + q z.2) t = inner ℝ z.1 (p t) + inner ℝ z.2 (q t) := by
    intro z t
    have h := inner_proj_add p hsym z.1 z.2 t
    rwa [← hq] at h
  have hAmeas : AEMeasurable (fun z : E × E => p z.1 + q z.2)
      ((ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E)) := by
    fun_prop
  have : IsProbabilityMeasure (((ProbabilityTheory.stdGaussian E).prod
      (ProbabilityTheory.stdGaussian E)).map (fun z : E × E => p z.1 + q z.2)) :=
    inferInstance
  apply MeasureTheory.Measure.ext_of_charFun
  funext t
  have hf : AEStronglyMeasurable (fun y : E => Complex.exp (↑(inner ℝ y t) * Complex.I))
      (((ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E)).map
        (fun z : E × E => p z.1 + q z.2)) := by
    fun_prop
  rw [MeasureTheory.charFun_apply,
    MeasureTheory.integral_map hAmeas (f := fun y : E => Complex.exp (↑(inner ℝ y t) * Complex.I)) hf]
  have hexp : ∀ z : E × E,
      Complex.exp (↑(inner ℝ (p z.1 + q z.2) t) * Complex.I)
        = Complex.exp (↑(inner ℝ z.1 (p t)) * Complex.I)
          * Complex.exp (↑(inner ℝ z.2 (q t)) * Complex.I) := by
    intro z
    rw [hinneradd z t, Complex.ofReal_add, add_mul, Complex.exp_add]
  simp_rw [hexp]
  rw [MeasureTheory.integral_prod_mul (f := fun x : E => Complex.exp (↑(inner ℝ x (p t)) * Complex.I))
    (g := fun y : E => Complex.exp (↑(inner ℝ y (q t)) * Complex.I))]
  rw [← MeasureTheory.charFun_apply, ← MeasureTheory.charFun_apply]
  rw [ProbabilityTheory.charFun_stdGaussian, ProbabilityTheory.charFun_stdGaussian,
    ProbabilityTheory.charFun_stdGaussian]
  rw [← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  rw [key t, Complex.ofReal_add]
  ring

end Commons.Probability.Gaussian