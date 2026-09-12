import Mathlib
import Submission.LMMeas

/-!
Gaussian facts for the walk: the moment-generating function of linear functionals of the
standard Gaussian on `Vec n`, and the resulting sub-Gaussian bounds for the projected steps.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Submission.Discrepancy

/-- One-dimensional Gaussian MGF. -/
lemma gaussian_mgf_one (c t : ℝ) :
    (∫ x : ℝ, Real.exp (t * (c * x)) ∂(gaussianReal 0 1)) = Real.exp (t ^ 2 * c ^ 2 / 2) := by
  have h := congrFun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)) (t * c)
  rw [mgf] at h
  rw [show (fun x : ℝ => Real.exp (t * (c * x))) = fun x : ℝ => Real.exp ((t * c) * x) by
    funext x
    congr 1
    ring]
  rw [h]
  congr 1
  ring_nf

/-- The MGF of a linear functional of the standard Gaussian on `Vec n`. -/
lemma gauss_mgf (n : ℕ) (a : Vec n) (t : ℝ) :
    (∫ g : Vec n, Real.exp (t * vin g a) ∂(stdGaussian (Vec n))) =
      Real.exp (t ^ 2 * ‖a‖ ^ 2 / 2) := by
  have hpi := ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin n)
  rw [← hpi]
  have hφ : AEMeasurable (WithLp.toLp 2) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    exact (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.aemeasurable
  rw [MeasureTheory.integral_map hφ]
  · rw [show (fun x : Fin n → ℝ => Real.exp (t * vin (WithLp.toLp 2 x) a)) =
        fun x => ∏ i : Fin n, Real.exp (t * (x i * (ofV a) i)) by
      funext x
      congr 1
      have hbil : vin (WithLp.toLp 2 x) a = ∑ i : Fin n, x i * (ofV a) i := by
        rw [← ofV_toV a]
        rw [vin_toV x (ofV a)]
        rfl
      rw [hbil]
      rw [show t * ∑ i : Fin n, x i * (ofV a) i = ∑ i : Fin n, t * (x i * (ofV a) i) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
      rw [← Real.exp_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [MeasureTheory.integral_fintype_prod_eq_prod (fun i : Fin n => fun x : ℝ =>
      Real.exp (t * (x * (ofV a) i)))]
    rw [Real.exp_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [gaussian_mgf_one]
    ring
    -- exponent: Σ t^2 a_i^2 /2 = t²‖a‖²/2
    ring_nf
  · have hc : Continuous (fun g : Vec n => Real.exp (t * vin g a)) := by
      refine Real.continuous_exp.comp ?_
      have hv : Continuous (fun g : Vec n => vin g a) := by
        simpa [vin] using continuous_inner.comp (by fun_prop : Continuous (fun g : Vec n => (g, a)))
      exact hv.const_mul t
    exact hc.aestronglyMeasurable

/-- Sub-Gaussian bound for a linear functional. -/
lemma gauss_subGauss (n : ℕ) (a : Vec n) (t : ℝ) :
    (∫ g : Vec n, Real.exp (t * vin g a) ∂(stdGaussian (Vec n))) ≤
      Real.exp (t ^ 2 * ‖a‖ ^ 2 / 2) := by
  rw [gauss_mgf]

/-- Self-adjointness of the orthogonal projection onto the free subspace. -/
lemma proj_adjoint {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (u w : Vec n) :
    vin (walkProj v A B u) w = vin u (walkProj v A B w) := by
  unfold walkProj
  have h := Submodule.inner_starProjection_left_eq_right ((Wspan v A B)ᗮ) u w
  simpa [vin] using h

/-- Contraction property of the projection. -/
lemma proj_norm_le {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (w : Vec n) : ‖walkProj v A B w‖ ≤ ‖w‖ := by
  unfold walkProj
  exact Submodule.norm_starProjection_apply_le ((Wspan v A B)ᗮ) w

/-- Fresh-step bound: the projected Gaussian is sub-Gaussian in every direction. -/
lemma fresh_step_bound {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (lam γ : ℝ) (w : Vec n) :
    (∫ g : Vec n, Real.exp (lam * (γ * vin (walkProj v A B g) w)) ∂(stdGaussian (Vec n))) ≤
      Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2) := by
  let p := walkProj v A B w
  have hsame : (fun g : Vec n => Real.exp (lam * (γ * vin (walkProj v A B g) w))) =
      (fun g : Vec n => Real.exp (1 * vin g ((lam * γ) • p))) := by
    funext g
    congr 1
    rw [proj_adjoint v A B]
    simp [p, vin, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
  have h1 := gauss_subGauss n ((lam * γ) • p) 1
  rw [← hsame] at h1
  calc
    (∫ g : Vec n, Real.exp (lam * (γ * vin (walkProj v A B g) w)) ∂(stdGaussian (Vec n)))
        ≤ Real.exp ((lam * γ) ^ 2 * ‖p‖ ^ 2 / 2) := h1
    _ ≤ Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2) := by
            apply exp_le_exp.mpr
            have hp2 : ‖p‖ ^ 2 ≤ ‖w‖ ^ 2 := by
              exact mul_self_le_mul_self (norm_nonneg p) (norm_nonneg w) (proj_norm_le v A B w)
            nlinarith [sq_nonneg (lam * γ), hp2]

end Discrepancy

end Submission
