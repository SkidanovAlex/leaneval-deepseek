import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.phi_conj_matrix
import Submission.Work.EKLC8Core.step10_second_choice

namespace Work.EKLC8Core

/-!
# `kappa_conj`: the invariances of `κ_a`, `κ_u`, `κ` under conjugation by the flow

The diagonal flow `φ_τ = diag(e^{-τ}, e^{τ}, 1)` rescales the `(i,j)` entry of `g` by
`e^{τ(flowExp i - flowExp j)}` (`phi_conj_matrix`).  Reading off the three relevant
entries one gets

* `(1,1)` and `(0,0)` are fixed (equal exponents), so `κ_a = |g₁₁ - g₀₀|` is invariant;
* `(1,0)` is scaled by `e^{2τ}` and `(2,0)`, `(1,2)` by `e^{τ}`; since `e^{2τ} = (e^τ)²`
  and `e^τ > 0`, the square root in the `κ_u` term turns the scale `e^{2τ}` into `e^τ`,
  so `κ_u` is multiplied by `e^τ`;
* `κ = max(κ_a, κ_u)` is then `max(κ_a g, e^τ κ_u g)`.

These are the conjugacy relations used throughout EKL §4.3–4.6.
-/

/-- `e^{2τ} = (e^τ)²`. -/
lemma exp_two_mul_eq_sq (τ : ℝ) : Real.exp (2 * τ) = Real.exp τ ^ 2 := by
  rw [show (2 : ℝ) * τ = τ + τ by ring, Real.exp_add]
  ring

/-- `√(e^{2τ} |x|) = e^τ √|x|`: the factor `e^{2τ}` under the square root of the `κ_u` term
becomes `e^τ`. -/
lemma sqrt_exp_two_mul_abs (τ x : ℝ) :
    Real.sqrt (Real.exp (2 * τ) * |x|) = Real.exp τ * Real.sqrt |x| := by
  rw [exp_two_mul_eq_sq, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (Real.exp_pos τ).le]

/-- `|e^τ x| = e^τ |x|`, `e^τ > 0`. -/
lemma abs_exp_mul' (τ x : ℝ) : |Real.exp τ * x| = Real.exp τ * |x| := by
  rw [abs_mul, abs_of_nonneg (Real.exp_pos τ).le]

/-- The `(1,1)`- and `(0,0)`-entries of the conjugated matrix: the scaling factors are `1`. -/
lemma phi_conj_diag_entries (τ : ℝ) (g : SL3) :
    ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 1
        = (g : Matrix (Fin 3) (Fin 3) ℝ) 1 1 ∧
    ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0
        = (g : Matrix (Fin 3) (Fin 3) ℝ) 0 0 := by
  constructor
  · rw [phi_conj_matrix τ g 1 1]
    simp [flowExp]
  · rw [phi_conj_matrix τ g 0 0]
    simp [flowExp]

/-- The three entries entering `κ_u`, after conjugation by `φ_τ`: `(1,0)` gains `e^{2τ}`,
`(2,0)` and `(1,2)` gain `e^τ`. -/
lemma phi_conj_kappaU_entries (τ : ℝ) (g : SL3) :
    ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 0
        = Real.exp (2 * τ) * (g : Matrix (Fin 3) (Fin 3) ℝ) 1 0 ∧
    ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 0
        = Real.exp τ * (g : Matrix (Fin 3) (Fin 3) ℝ) 2 0 ∧
    ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 2
        = Real.exp τ * (g : Matrix (Fin 3) (Fin 3) ℝ) 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phi_conj_matrix τ g 1 0,
      show (flowExp (1 : Fin 3) - flowExp 0) * τ = 2 * τ by norm_num [flowExp]]
  · rw [phi_conj_matrix τ g 2 0,
      show (flowExp (2 : Fin 3) - flowExp 0) * τ = τ by
        rw [show flowExp (2 : Fin 3) = (0 : ℝ) by simp [flowExp],
            show flowExp (0 : Fin 3) = (-1 : ℝ) by simp [flowExp]]
        ring]
  · rw [phi_conj_matrix τ g 1 2,
      show (flowExp (1 : Fin 3) - flowExp 2) * τ = τ by
        rw [show flowExp (2 : Fin 3) = (0 : ℝ) by simp [flowExp],
            show flowExp (1 : Fin 3) = (1 : ℝ) by simp [flowExp]]
        ring]

/-- `κ_a` is invariant under conjugation by the flow `φ_τ`. -/
lemma kappaA_phi_conj (τ : ℝ) (g : SL3) :
    kappaA ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = kappaA (g : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨h11, h00⟩ := phi_conj_diag_entries τ g
  simp only [kappaA]
  rw [h11, h00]

/-- `κ_u` is multiplied by `e^τ` under conjugation by the flow `φ_τ`. -/
lemma kappaU_phi_conj (τ : ℝ) (g : SL3) :
    kappaU ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = Real.exp τ * kappaU (g : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨h10, h20, h12⟩ := phi_conj_kappaU_entries τ g
  simp only [kappaU]
  rw [h10, h20, h12]
  rw [show Real.sqrt |Real.exp (2 * τ) * (g : Matrix (Fin 3) (Fin 3) ℝ) 1 0|
        = Real.exp τ * Real.sqrt |(g : Matrix (Fin 3) (Fin 3) ℝ) 1 0| by
      rw [abs_mul, abs_of_nonneg (Real.exp_pos (2 * τ)).le, exp_two_mul_eq_sq,
        Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.exp_pos τ).le]]
  rw [abs_exp_mul', abs_exp_mul']
  rw [mul_max_of_nonneg _ _ (Real.exp_pos τ).le, mul_max_of_nonneg _ _ (Real.exp_pos τ).le]

/-- `κ = max(κ_a, κ_u)` under conjugation by the flow `φ_τ`. -/
lemma kappa_phi_conj (τ : ℝ) (g : SL3) :
    kappa ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = max (kappaA (g : Matrix (Fin 3) (Fin 3) ℝ))
            (Real.exp τ * kappaU (g : Matrix (Fin 3) (Fin 3) ℝ)) := by
  rw [kappa, kappaA_phi_conj τ g, kappaU_phi_conj τ g]

theorem kappa_conj (τ : ℝ) (g : SL3) :
    kappaA ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = kappaA (g : Matrix (Fin 3) (Fin 3) ℝ) ∧
    kappaU ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = Real.exp τ * kappaU (g : Matrix (Fin 3) (Fin 3) ℝ) ∧
    kappa ((phi τ * g * (phi τ)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = max (kappaA (g : Matrix (Fin 3) (Fin 3) ℝ))
              (Real.exp τ * kappaU (g : Matrix (Fin 3) (Fin 3) ℝ)) :=
  ⟨kappaA_phi_conj τ g, kappaU_phi_conj τ g, kappa_phi_conj τ g⟩

end Work.EKLC8Core
