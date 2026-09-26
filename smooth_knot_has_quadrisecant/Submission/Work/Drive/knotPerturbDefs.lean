import Mathlib
import ChallengeDeps
import Submission.Work.Drive.smallCorrectionKnot

/-!
# The perturbation family used for the endpoint-tangent transversality

Scalar basis: trigonometric polynomials of degree at most `4`, indexed by `Fin 9`
(`1, cos t, sin t, cos 2t, sin 2t, cos 3t, sin 3t, cos 4t, sin 4t`), with the explicit
derivatives `trigBasisD`.  A perturbation of `r` with coefficients `c : Fin 9 → Space` is
`perturb r c = r + perturbCorr c` with velocity `perturbVel r c = velocity r + perturbVelCorr c`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The scalar basis of the perturbation space. -/
noncomputable def trigBasis : Fin 9 → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => Real.cos
  | 2 => Real.sin
  | 3 => fun t => Real.cos (2 * t)
  | 4 => fun t => Real.sin (2 * t)
  | 5 => fun t => Real.cos (3 * t)
  | 6 => fun t => Real.sin (3 * t)
  | 7 => fun t => Real.cos (4 * t)
  | _ => fun t => Real.sin (4 * t)

/-- The derivative of the basis. -/
noncomputable def trigBasisD : Fin 9 → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun t => -Real.sin t
  | 2 => Real.cos
  | 3 => fun t => -2 * Real.sin (2 * t)
  | 4 => fun t => 2 * Real.cos (2 * t)
  | 5 => fun t => -3 * Real.sin (3 * t)
  | 6 => fun t => 3 * Real.cos (3 * t)
  | 7 => fun t => -4 * Real.sin (4 * t)
  | _ => fun t => 4 * Real.cos (4 * t)

theorem contDiff_trigBasis (j : Fin 9) : ContDiff ℝ ⊤ (trigBasis j) := by
  fin_cases j
  · show ContDiff ℝ ⊤ (fun _ : ℝ => (1:ℝ)); fun_prop
  · show ContDiff ℝ ⊤ Real.cos; fun_prop
  · show ContDiff ℝ ⊤ Real.sin; fun_prop
  · show ContDiff ℝ ⊤ (fun t : ℝ => Real.cos (2 * t)); fun_prop
  · show ContDiff ℝ ⊤ (fun t : ℝ => Real.sin (2 * t)); fun_prop
  · show ContDiff ℝ ⊤ (fun t : ℝ => Real.cos (3 * t)); fun_prop
  · show ContDiff ℝ ⊤ (fun t : ℝ => Real.sin (3 * t)); fun_prop
  · show ContDiff ℝ ⊤ (fun t : ℝ => Real.cos (4 * t)); fun_prop
  · show ContDiff ℝ ⊤ (fun t : ℝ => Real.sin (4 * t)); fun_prop

theorem periodic_trigBasis (j : Fin 9) : Function.Periodic (trigBasis j) (2 * Real.pi) := by
  intro t
  fin_cases j
  · show (1:ℝ) = 1; rfl
  · show Real.cos (t + 2 * Real.pi) = Real.cos t
    rw [show t + 2 * Real.pi = t + (1:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_add_int_mul_two_pi t 1
  · show Real.sin (t + 2 * Real.pi) = Real.sin t
    rw [show t + 2 * Real.pi = t + (1:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_int_mul_two_pi t 1
  · show Real.cos (2 * (t + 2 * Real.pi)) = Real.cos (2 * t)
    rw [show (2:ℝ) * (t + 2 * Real.pi) = 2 * t + (2:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_add_int_mul_two_pi (2 * t) 2
  · show Real.sin (2 * (t + 2 * Real.pi)) = Real.sin (2 * t)
    rw [show (2:ℝ) * (t + 2 * Real.pi) = 2 * t + (2:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_int_mul_two_pi (2 * t) 2
  · show Real.cos (3 * (t + 2 * Real.pi)) = Real.cos (3 * t)
    rw [show (3:ℝ) * (t + 2 * Real.pi) = 3 * t + (3:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_add_int_mul_two_pi (3 * t) 3
  · show Real.sin (3 * (t + 2 * Real.pi)) = Real.sin (3 * t)
    rw [show (3:ℝ) * (t + 2 * Real.pi) = 3 * t + (3:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_int_mul_two_pi (3 * t) 3
  · show Real.cos (4 * (t + 2 * Real.pi)) = Real.cos (4 * t)
    rw [show (4:ℝ) * (t + 2 * Real.pi) = 4 * t + (4:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_add_int_mul_two_pi (4 * t) 4
  · show Real.sin (4 * (t + 2 * Real.pi)) = Real.sin (4 * t)
    rw [show (4:ℝ) * (t + 2 * Real.pi) = 4 * t + (4:ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_int_mul_two_pi (4 * t) 4

private lemma deriv_cos_mul (k : ℝ) : deriv (fun t : ℝ => Real.cos (k * t)) = fun t => -k * Real.sin (k * t) := by
  funext t
  have h2 : HasDerivAt (fun t : ℝ => k * t) k t := by simpa using (hasDerivAt_id t).const_mul k
  have h : HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-Real.sin (k * t) * k) t :=
    (Real.hasDerivAt_cos (k * t)).comp t h2
  rw [h.deriv]; ring

private lemma deriv_sin_mul (k : ℝ) : deriv (fun t : ℝ => Real.sin (k * t)) = fun t => k * Real.cos (k * t) := by
  funext t
  have h2 : HasDerivAt (fun t : ℝ => k * t) k t := by simpa using (hasDerivAt_id t).const_mul k
  have h : HasDerivAt (fun t : ℝ => Real.sin (k * t)) (Real.cos (k * t) * k) t :=
    (Real.hasDerivAt_sin (k * t)).comp t h2
  rw [h.deriv]; ring

theorem deriv_trigBasis (j : Fin 9) : deriv (trigBasis j) = trigBasisD j := by
  fin_cases j
  · show deriv (fun _ : ℝ => (1:ℝ)) = fun _ => (0:ℝ)
    funext t; exact deriv_const t 1
  · show deriv Real.cos = fun t => -Real.sin t
    funext t; exact Real.deriv_cos
  · show deriv Real.sin = Real.cos
    exact Real.deriv_sin
  · show deriv (fun t : ℝ => Real.cos (2 * t)) = fun t => -2 * Real.sin (2 * t)
    exact deriv_cos_mul 2
  · show deriv (fun t : ℝ => Real.sin (2 * t)) = fun t => 2 * Real.cos (2 * t)
    exact deriv_sin_mul 2
  · show deriv (fun t : ℝ => Real.cos (3 * t)) = fun t => -3 * Real.sin (3 * t)
    exact deriv_cos_mul 3
  · show deriv (fun t : ℝ => Real.sin (3 * t)) = fun t => 3 * Real.cos (3 * t)
    exact deriv_sin_mul 3
  · show deriv (fun t : ℝ => Real.cos (4 * t)) = fun t => -4 * Real.sin (4 * t)
    exact deriv_cos_mul 4
  · show deriv (fun t : ℝ => Real.sin (4 * t)) = fun t => 4 * Real.cos (4 * t)
    exact deriv_sin_mul 4

/-- The correction to the curve. -/
noncomputable def perturbCorr (c : Fin 9 → Space) : ℝ → Space :=
  fun t => ∑ j, (trigBasis j t) • c j

/-- The velocity of the correction. -/
noncomputable def perturbVelCorr (c : Fin 9 → Space) : ℝ → Space :=
  fun t => ∑ j, (trigBasisD j t) • c j

/-- The perturbed curve. -/
noncomputable def perturb (r : ℝ → Space) (c : Fin 9 → Space) : ℝ → Space :=
  fun t => r t + perturbCorr c t

/-- The velocity of the perturbed curve. -/
noncomputable def perturbVel (r : ℝ → Space) (c : Fin 9 → Space) : ℝ → Space :=
  fun t => velocity r t + perturbVelCorr c t

theorem contDiff_perturbCorr (c : Fin 9 → Space) : ContDiff ℝ ⊤ (perturbCorr c) := by
  apply ContDiff.sum
  intro j _
  exact (contDiff_trigBasis j).smul_const (c j)

theorem periodic_perturbCorr (c : Fin 9 → Space) :
    Function.Periodic (perturbCorr c) (2 * Real.pi) := by
  intro t
  simp only [perturbCorr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [periodic_trigBasis j t]

theorem deriv_perturbCorr (c : Fin 9 → Space) : deriv (perturbCorr c) = perturbVelCorr c := by
  funext t
  change deriv (∑ j : Fin 9, fun s : ℝ => (trigBasis j s) • c j) t
      = ∑ j, (trigBasisD j t) • c j
  rw [deriv_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [deriv_smul_const]
    · rw [deriv_trigBasis]
    · exact ((contDiff_trigBasis j).differentiable (by simp)).differentiableAt
  · intro j _
    exact ((contDiff_trigBasis j).differentiable (by simp)).differentiableAt.smul_const (c j)

theorem deriv_perturb {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (c : Fin 9 → Space) :
    deriv (perturb r c) = perturbVel r c := by
  funext t
  have h1 : deriv (perturb r c) t = deriv r t + deriv (perturbCorr c) t := by
    rw [show perturb r c = r + perturbCorr c from rfl]
    exact deriv_add (hr.differentiable (by simp)).differentiableAt
      ((contDiff_perturbCorr c).differentiable (by simp)).differentiableAt
  rw [h1, deriv_perturbCorr]
  rfl

/-- Each basis function has sup norm at most one. -/
theorem abs_trigBasis_le_one (j : Fin 9) (t : ℝ) : |trigBasis j t| ≤ 1 := by
  fin_cases j
  · show |(1:ℝ)| ≤ 1; simp
  · show |Real.cos t| ≤ 1; exact Real.abs_cos_le_one t
  · show |Real.sin t| ≤ 1; exact Real.abs_sin_le_one t
  · show |Real.cos (2 * t)| ≤ 1; exact Real.abs_cos_le_one _
  · show |Real.sin (2 * t)| ≤ 1; exact Real.abs_sin_le_one _
  · show |Real.cos (3 * t)| ≤ 1; exact Real.abs_cos_le_one _
  · show |Real.sin (3 * t)| ≤ 1; exact Real.abs_sin_le_one _
  · show |Real.cos (4 * t)| ≤ 1; exact Real.abs_cos_le_one _
  · show |Real.sin (4 * t)| ≤ 1; exact Real.abs_sin_le_one _

/-- Each derivative of a basis function has sup norm at most four. -/
theorem abs_trigBasisD_le_four (j : Fin 9) (t : ℝ) : |trigBasisD j t| ≤ 4 := by
  fin_cases j
  · show |(0:ℝ)| ≤ 4; norm_num
  · show |-Real.sin t| ≤ 4
    rw [abs_neg]; linarith [Real.abs_sin_le_one t]
  · show |Real.cos t| ≤ 4; linarith [Real.abs_cos_le_one t]
  · show |-2 * Real.sin (2 * t)| ≤ 4
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [Real.abs_sin_le_one (2 * t)]
  · show |2 * Real.cos (2 * t)| ≤ 4
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [Real.abs_cos_le_one (2 * t)]
  · show |-3 * Real.sin (3 * t)| ≤ 4
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    linarith [Real.abs_sin_le_one (3 * t)]
  · show |3 * Real.cos (3 * t)| ≤ 4
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    linarith [Real.abs_cos_le_one (3 * t)]
  · show |-4 * Real.sin (4 * t)| ≤ 4
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith [Real.abs_sin_le_one (4 * t)]
  · show |4 * Real.cos (4 * t)| ≤ 4
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith [Real.abs_cos_le_one (4 * t)]

/-- Pointwise bound for the correction. -/
theorem norm_perturbCorr_le (c : Fin 9 → Space) (t : ℝ) : ‖perturbCorr c t‖ ≤ 9 * ‖c‖ := by
  have h : ‖perturbCorr c t‖ ≤ ∑ j, |trigBasis j t| * ‖c j‖ := by
    change ‖∑ j, (trigBasis j t) • c j‖ ≤ _
    calc ‖∑ j, (trigBasis j t) • c j‖ ≤ ∑ j, ‖(trigBasis j t) • c j‖ := norm_sum_le _ _
      _ = ∑ j, |trigBasis j t| * ‖c j‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_smul, Real.norm_eq_abs]
  calc ‖perturbCorr c t‖ ≤ ∑ j, |trigBasis j t| * ‖c j‖ := h
    _ ≤ ∑ j, 1 * ‖c‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 : ‖c j‖ ≤ ‖c‖ := norm_le_pi_norm c j
          have h2 : |trigBasis j t| ≤ 1 := abs_trigBasis_le_one j t
          nlinarith [abs_nonneg (trigBasis j t), norm_nonneg (c j), norm_nonneg c]
    _ = 9 * ‖c‖ := by simp

/-- Pointwise bound for the velocity of the correction. -/
theorem norm_perturbVelCorr_le (c : Fin 9 → Space) (t : ℝ) :
    ‖perturbVelCorr c t‖ ≤ 36 * ‖c‖ := by
  have h : ‖perturbVelCorr c t‖ ≤ ∑ j, |trigBasisD j t| * ‖c j‖ := by
    change ‖∑ j, (trigBasisD j t) • c j‖ ≤ _
    calc ‖∑ j, (trigBasisD j t) • c j‖ ≤ ∑ j, ‖(trigBasisD j t) • c j‖ := norm_sum_le _ _
      _ = ∑ j, |trigBasisD j t| * ‖c j‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_smul, Real.norm_eq_abs]
  calc ‖perturbVelCorr c t‖ ≤ ∑ j, |trigBasisD j t| * ‖c j‖ := h
    _ ≤ ∑ j, 4 * ‖c‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 : ‖c j‖ ≤ ‖c‖ := norm_le_pi_norm c j
          have h2 : |trigBasisD j t| ≤ 4 := abs_trigBasisD_le_four j t
          nlinarith [abs_nonneg (trigBasisD j t), norm_nonneg (c j), norm_nonneg c]
    _ = 36 * ‖c‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring

end

end Work.Drive
