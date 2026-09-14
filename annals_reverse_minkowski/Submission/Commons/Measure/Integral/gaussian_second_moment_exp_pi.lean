import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

noncomputable section
open MeasureTheory
open scoped Real

namespace Commons.Measure.Integral


private lemma mul_exp_neg_le_exp_neg_half {b : ℝ} (hb : 0 < b) (s : ℝ) :
    s * Real.exp (-b * s) ≤ (2 / (b * Real.exp 1)) * Real.exp (-(b / 2) * s) := by
  have ha : 0 < b / 2 := by linarith
  have h := Real.mul_exp_neg_le_exp_neg_one ((b / 2) * s)
  have key : s * Real.exp (-(b / 2) * s) ≤ Real.exp (-1) / (b / 2) := by
    rw [le_div_iff₀ ha]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc s * Real.exp (-b * s)
      = s * (Real.exp (-(b / 2) * s) * Real.exp (-(b / 2) * s)) := by
        rw [← Real.exp_add]; ring_nf
    _ = (s * Real.exp (-(b / 2) * s)) * Real.exp (-(b / 2) * s) := by ring
    _ ≤ (Real.exp (-1) / (b / 2)) * Real.exp (-(b / 2) * s) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = (2 / (b * Real.exp 1)) * Real.exp (-(b / 2) * s) := by
        rw [Real.exp_neg]
        field_simp

private lemma integrable_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2)) := by
  have hb2 : 0 < b / 2 := by linarith
  refine Integrable.mono' ((integrable_exp_neg_mul_sq hb2).const_mul (2 / (b * Real.exp 1))) ?_ ?_
  · fun_prop
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_exp_neg_le_exp_neg_half hb (t ^ 2)

private lemma integral_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ, t ^ 2 * Real.exp (-b * t ^ 2)) = √(π / b) / (2 * b) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -(2 * b)⁻¹ * (t * Real.exp (-b * t ^ 2)))
      (t ^ 2 * Real.exp (-b * t ^ 2) - (2 * b)⁻¹ * Real.exp (-b * t ^ 2)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-b * t ^ 2))
        (Real.exp (-b * t ^ 2) * (-b * (2 * t))) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (-b)).exp
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => t * Real.exp (-b * t ^ 2))
        (1 * Real.exp (-b * t ^ 2) + t * (Real.exp (-b * t ^ 2) * (-b * (2 * t)))) t :=
      (hasDerivAt_id t).mul h1
    have h3 := h2.const_mul (-(2 * b)⁻¹)
    have heq : -(2 * b)⁻¹ * (1 * Real.exp (-b * t ^ 2) + t * (Real.exp (-b * t ^ 2) * (-b * (2 * t))))
        = t ^ 2 * Real.exp (-b * t ^ 2) - (2 * b)⁻¹ * Real.exp (-b * t ^ 2) := by
      field_simp
      ring
    rw [heq] at h3
    exact h3
  have hF : Integrable (fun t : ℝ => -(2 * b)⁻¹ * (t * Real.exp (-b * t ^ 2))) :=
    (integrable_mul_exp_neg_mul_sq hb).const_mul _
  have hF' : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2) - (2 * b)⁻¹ * Real.exp (-b * t ^ 2)) :=
    (integrable_sq_mul_exp_neg_mul_sq hb).sub ((integrable_exp_neg_mul_sq hb).const_mul _)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hF' hF
  rw [integral_sub (integrable_sq_mul_exp_neg_mul_sq hb) ((integrable_exp_neg_mul_sq hb).const_mul _),
    integral_const_mul, integral_gaussian] at h0
  have hval : (∫ t : ℝ, t ^ 2 * Real.exp (-b * t ^ 2)) = (2 * b)⁻¹ * √(π / b) := by linarith
  rw [hval]
  ring

private theorem integral_euclideanSpace_prod_coord_real {ι : Type*} [Fintype ι] (h : ι → ℝ → ℝ) :
    (∫ v : EuclideanSpace ℝ ι, ∏ j, h j (v j)) = ∏ j, ∫ x : ℝ, h j x := by
  have key : (∫ v : EuclideanSpace ℝ ι, ∏ j, h j (v j))
      = ∫ w : ι → ℝ, ∏ j, h j (w j) := by
    have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integral_comp'
      (fun w : ι → ℝ ↦ ∏ j, h j (w j))
    simpa using this
  rw [key]
  exact integral_fintype_prod_volume_eq_prod (fun j ↦ h j)

private lemma integrable_norm_sq_mul_exp_neg_pi (n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 * Real.exp (-π * ‖x‖ ^ 2)) := by
  have hbase : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(π/2) * ‖x‖ ^ 2)) :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin n)) (π/2)
      (by positivity)
  refine Integrable.mono' (hbase.const_mul (2 / (π * Real.exp 1))) ?_ ?_
  · fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_exp_neg_le_exp_neg_half Real.pi_pos (‖x‖ ^ 2)

private def gaussQ (t : ℝ) : ℝ := Real.exp (-π * t ^ 2)
private def gaussP (t : ℝ) : ℝ := t ^ 2 * Real.exp (-π * t ^ 2)

private lemma integral_coord_sq_exp {n : ℕ} (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 * Real.exp (-π * ‖x‖ ^ 2)) = 1 / (2 * π) := by
  set h : Fin n → ℝ → ℝ := Function.update (fun _ : Fin n => gaussQ) i gaussP with hh
  have hfun : (fun v : EuclideanSpace ℝ (Fin n) => ∏ j, h j (v j))
      = (fun v : EuclideanSpace ℝ (Fin n) => (v i) ^ 2 * Real.exp (-π * ‖v‖ ^ 2)) := by
    funext v
    rw [Finset.prod_eq_mul_prod_sdiff_singleton i (fun j => h j (v j)) (by simp)]
    have hhi : h i (v i) = (v i) ^ 2 * Real.exp (-π * (v i) ^ 2) := by
      rw [hh, Function.update_self]
      simp only [gaussP]
    have hhj : ∀ j ∈ Finset.univ \ {i}, h j (v j) = Real.exp (-π * (v j) ^ 2) := by
      intro j hj
      have hjne : j ≠ i := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
        exact hj
      rw [hh, Function.update_of_ne hjne]
      simp only [gaussQ]
    rw [hhi, Finset.prod_congr rfl hhj]
    have hQE : Real.exp (-π * ‖v‖ ^ 2) = ∏ j, Real.exp (-π * (v j) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    have hEP : Real.exp (-π * ‖v‖ ^ 2)
        = Real.exp (-π * (v i) ^ 2) * ∏ j ∈ Finset.univ \ {i}, Real.exp (-π * (v j) ^ 2) := by
      rw [hQE]
      exact Finset.prod_eq_mul_prod_sdiff_singleton i (fun j => Real.exp (-π * (v j) ^ 2)) (by simp)
    rw [hEP]
    ring
  rw [← hfun, integral_euclideanSpace_prod_coord_real h]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i (fun j => ∫ x : ℝ, h j x) (by simp)]
  have hpi : (∫ x : ℝ, h i x) = √(π / π) / (2 * π) := by
    rw [hh, Function.update_self]
    simp only [gaussP]
    exact integral_sq_mul_exp_neg_mul_sq Real.pi_pos
  have hpj : ∀ j ∈ Finset.univ \ {i}, (∫ x : ℝ, h j x) = 1 := by
    intro j hj
    have hjne : j ≠ i := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
      exact hj
    rw [hh, Function.update_of_ne hjne]
    simp only [gaussQ]
    rw [integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one]
  rw [hpi, Finset.prod_congr rfl hpj, Finset.prod_const]
  rw [div_self Real.pi_ne_zero, Real.sqrt_one, one_pow, mul_one]

private lemma integrable_coord_sq_mul_exp (n : ℕ) (i : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2 * Real.exp (-π * ‖x‖ ^ 2)) := by
  refine Integrable.mono' (integrable_norm_sq_mul_exp_neg_pi n) ?_ ?_
  · fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => (x j) ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le

theorem gaussian_second_moment_exp_pi {n : ℕ} (hn : 0 < n) :
    (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (n : ℝ) / (2 * Real.pi) := by
  have hn' : (0 : ℕ) < n := hn
  have hdecomp : (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 * Real.exp (-π * ‖x‖ ^ 2))
      = (fun x => ∑ i, (x i) ^ 2 * Real.exp (-π * ‖x‖ ^ 2)) := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
  rw [hdecomp]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_coord_sq_mul_exp n i)]
  rw [Finset.sum_congr rfl (fun i _ => integral_coord_sq_exp i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Commons.Measure.Integral
