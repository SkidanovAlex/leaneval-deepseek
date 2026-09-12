import Mathlib
import Submission.LMAux
import Submission.LMWalk

/-!
Gaussian facts for the Lovett--Meka walk (child task).

All vectors live in `Vec n = EuclideanSpace ℝ (Fin n)` and `vin a b := ⟪a, b⟫`.
`walkProj v A B g` is `((Wspan v A B)ᗮ).starProjection g` where `Wspan v A B` is the span of
`{basis n i | i ∈ A}` and `{v j | j ∈ B}` (see `Submission.LMWalk`).
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Submission.Discrepancy

/-- One-dimensional Gaussian MGF: for c t : ℝ,
∫ x, exp (t * (c * x)) d(gaussianReal 0 1) = exp (t^2 * c^2 / 2). -/
lemma gaussian_mgf_one (c t : ℝ) :
    (∫ x : ℝ, Real.exp (t * (c * x)) ∂(gaussianReal 0 1)) = Real.exp (t ^ 2 * c ^ 2 / 2) := by
  have h := congrFun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)) (t * c)
  rw [mgf] at h
  have hf : (fun x : ℝ => Real.exp (t * (c * x))) = fun x : ℝ => Real.exp ((t * c) * x) := by
    funext x
    congr 1
    ring
  rw [hf, h]
  congr 1
  norm_num
  ring

/-- The MGF of a linear functional of the standard Gaussian on `Vec n`:
∫ over g of exp (t * vin g a) = exp (t^2 * ‖a‖^2 / 2). -/
lemma gauss_mgf (n : ℕ) (a : Vec n) (t : ℝ) :
    (∫ g : Vec n, Real.exp (t * vin g a) ∂(stdGaussian (Vec n))) =
      Real.exp (t ^ 2 * ‖a‖ ^ 2 / 2) := by
  have hpi := ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin n)
  -- hpi : Measure.map (WithLp.toLp 2) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
  --        stdGaussian (EuclideanSpace ℝ (Fin n))
  rw [← hpi]
  have hφ : AEMeasurable (WithLp.toLp 2) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    exact (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.aemeasurable
  rw [MeasureTheory.integral_map hφ]
  · -- main: integrate over x : Fin n → ℝ
    rw [show (fun x : Fin n → ℝ => Real.exp (t * vin (WithLp.toLp 2 x) a)) =
          fun x => ∏ i : Fin n, Real.exp (t * (x i * (ofV a) i)) by
      funext x
      rw [show t * vin (WithLp.toLp 2 x) a = ∑ i : Fin n, t * (x i * (ofV a) i) by
        calc t * vin (WithLp.toLp 2 x) a
            = t * (∑ i : Fin n, x i * (ofV a) i) := by
                congr 1
                rw [vin_sum]
                apply Finset.sum_congr rfl
                intro i hi
                simp [ofV_apply]
        _ = ∑ i : Fin n, t * (x i * (ofV a) i) := by rw [Finset.mul_sum]]
      rw [Real.exp_sum]]
    rw [MeasureTheory.integral_fintype_prod_eq_prod (fun i : Fin n => fun x : ℝ =>
      Real.exp (t * (x * (ofV a) i)))]
    calc
      (∏ i : Fin n, ∫ (x : ℝ), Real.exp (t * (x * (ofV a) i)) ∂(gaussianReal 0 1))
          = ∏ i : Fin n, Real.exp (t ^ 2 * ((ofV a) i) ^ 2 / 2) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [show (fun x : ℝ => Real.exp (t * (x * (ofV a) i))) =
                    fun x : ℝ => Real.exp (t * ((ofV a) i * x)) by
                funext x; congr 1; ring]
              exact gaussian_mgf_one ((ofV a) i) t
      _ = Real.exp (∑ i : Fin n, t ^ 2 * ((ofV a) i) ^ 2 / 2) := by
              rw [← Real.exp_sum]
      _ = Real.exp (t ^ 2 * (∑ i : Fin n, ((ofV a) i) ^ 2) / 2) := by
              congr 1
              rw [Finset.mul_sum, Finset.sum_div]
      _ = Real.exp (t ^ 2 * ‖a‖ ^ 2 / 2) := by
              congr 1
              congr 2
              simpa using (norm_sq_sum n a).symm
  · -- integrability side condition
    exact (Real.continuous_exp.measurable.comp ((measurable_vin n a).const_mul t)).aestronglyMeasurable

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

/-- Fresh-step bound: the projected Gaussian is sub-Gaussian in every direction:
∫ over g of exp (lam * (γ * vin (walkProj v A B g) w)) ≤ exp (lam^2 * γ^2 * ‖w‖^2 / 2). -/
lemma fresh_step_bound {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (lam γ : ℝ) (w : Vec n) :
    (∫ g : Vec n, Real.exp (lam * (γ * vin (walkProj v A B g) w)) ∂(stdGaussian (Vec n))) ≤
      Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2) := by
  let p := walkProj v A B w
  have hsame : (fun g : Vec n => Real.exp (lam * (γ * vin (walkProj v A B g) w))) =
      (fun g : Vec n => Real.exp ((lam * γ) * vin g p)) := by
    funext g
    congr 1
    rw [proj_adjoint v A B g w]
    simp [p, mul_assoc]
  calc
    (∫ g : Vec n, Real.exp (lam * (γ * vin (walkProj v A B g) w)) ∂(stdGaussian (Vec n)))
        ≤ Real.exp ((lam * γ) ^ 2 * ‖p‖ ^ 2 / 2) := by
            rw [hsame]
            exact gauss_subGauss n p (lam * γ)
    _ ≤ Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2) := by
            refine (Real.exp_le_exp.mpr ?_)
            have hp2 : ‖p‖ ^ 2 ≤ ‖w‖ ^ 2 := by
              simpa [p, pow_two] using mul_self_le_mul_self (norm_nonneg p) (proj_norm_le v A B w)
            have hmul : (lam * γ) ^ 2 * ‖p‖ ^ 2 ≤ (lam * γ) ^ 2 * ‖w‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hp2 (sq_nonneg (lam * γ))
            have hle2 : (lam * γ) ^ 2 * ‖p‖ ^ 2 / 2 ≤ (lam * γ) ^ 2 * ‖w‖ ^ 2 / 2 :=
              div_le_div_of_nonneg_right hmul (by positivity)
            calc
              (lam * γ) ^ 2 * ‖p‖ ^ 2 / 2 ≤ (lam * γ) ^ 2 * ‖w‖ ^ 2 / 2 := hle2
              _ = lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2 := by ring

end Discrepancy

end Submission
