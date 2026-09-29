import Mathlib
import Submission.Work.TMContract.Defs

/-!
# C11 (`P_Reducibility`): basic matrix lemmas for the rotation matrices `rot`

`Work.TMContract.rot c` is AJ's rotation `R_c` (angles in turns).  This file collects the
elementary algebra needed to build reducible conjugacies: `rot` is a homomorphism
`ℝ → SL(2,ℝ)`, and multiplying an `SL(2,ℝ)`-valued loop by a 1-periodic `rot` preserves the
homotopy-class data `HasDegree _ 0` used in `Work.TMContract.RedSet`.
-/

open LeanEval.Analysis.TenMartini

set_option autoImplicit false

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-- `rot` is a homomorphism: `rot a * rot b = rot (a + b)`. -/
theorem rot_mul (a b : ℝ) : rot a * rot b = rot (a + b) := by
  have hc : 2 * Real.pi * (a + b) = 2 * Real.pi * a + 2 * Real.pi * b := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, hc, Real.cos_add, Real.sin_add] <;> ring

@[simp] theorem rot_zero : rot 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot]

theorem rot_mul_neg_self (a : ℝ) : rot a * rot (-a) = 1 := by
  rw [rot_mul]; simp

theorem rot_neg_mul_self (a : ℝ) : rot (-a) * rot a = 1 := by
  rw [rot_mul]; simp

/-- `rot a * rot (-b) = rot (a - b)`. -/
theorem rot_mul_neg (a b : ℝ) : rot a * rot (-b) = rot (a - b) := by
  rw [rot_mul, show a + -b = a - b by ring]

@[simp] theorem rot_det (a : ℝ) : (rot a).det = 1 := by
  have h := Real.cos_sq_add_sin_sq (2 * Real.pi * a)
  simp only [rot, Matrix.det_fin_two_of]
  nlinarith [h]

theorem rot_apply_00 (a : ℝ) : rot a 0 0 = Real.cos (2 * Real.pi * a) := by simp [rot]
theorem rot_apply_01 (a : ℝ) : rot a 0 1 = -Real.sin (2 * Real.pi * a) := by simp [rot]
theorem rot_apply_10 (a : ℝ) : rot a 1 0 = Real.sin (2 * Real.pi * a) := by simp [rot]
theorem rot_apply_11 (a : ℝ) : rot a 1 1 = Real.cos (2 * Real.pi * a) := by simp [rot]

theorem continuous_rot' : Continuous (rot : ℝ → Matrix (Fin 2) (Fin 2) ℝ) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [rot] <;> fun_prop

theorem continuous_rot (h : ℝ → ℝ) (hc : Continuous h) : Continuous fun x => rot (h x) :=
  continuous_rot'.comp hc

/-- The `(0,0)` entry of `rot h * B` is the first coordinate of the rotated first column. -/
theorem rot_mul_apply_00 (h : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (rot h * B) 0 0
      = Real.cos (2 * Real.pi * h) * B 0 0 - Real.sin (2 * Real.pi * h) * B 1 0 := by
  simp [rot, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem rot_mul_apply_10 (h : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (rot h * B) 1 0
      = Real.sin (2 * Real.pi * h) * B 0 0 + Real.cos (2 * Real.pi * h) * B 1 0 := by
  simp [rot, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Degree is preserved by a 1-periodic `rot` factor.** If `HasDegree B k` and `h` is
continuous and 1-periodic, then `x ↦ rot (h x) * B x` again has degree `k`: the angle
function `η` of `B` becomes `η + h`, and `h (x+1) = h x`. -/
theorem hasDegree_rot_mul {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {k : ℤ} (hB : HasDegree B k)
    {h : ℝ → ℝ} (hc : Continuous h) (hp : ∀ x, h (x + 1) = h x) :
    HasDegree (fun x => rot (h x) * B x) k := by
  obtain ⟨hBc, η, hηc, hηp, hη⟩ := hB
  refine ⟨(continuous_rot h hc).matrix_mul hBc, fun x => η x + h x, hηc.add hc, ?_, ?_⟩
  · intro x
    have h1 := hηp x
    have h2 := hp x
    push_cast
    linarith
  · intro x
    obtain ⟨r, hr, h1, h2⟩ := hη x
    refine ⟨r, hr, ?_, ?_⟩
    · change (rot (h x) * B x) 0 0 = r * Real.cos (2 * Real.pi * (η x + h x))
      rw [rot_mul_apply_00, h1, h2,
        show (2 : ℝ) * Real.pi * (η x + h x)
          = 2 * Real.pi * η x + 2 * Real.pi * h x from by ring, Real.cos_add]
      ring
    · change (rot (h x) * B x) 1 0 = r * Real.sin (2 * Real.pi * (η x + h x))
      rw [rot_mul_apply_10, h1, h2,
        show (2 : ℝ) * Real.pi * (η x + h x)
          = 2 * Real.pi * η x + 2 * Real.pi * h x from by ring, Real.sin_add]
      ring

/-- `HasDegree (fun _ => rot c) 0` for a constant angle. -/
theorem hasDegree_const_rot (c : ℝ) : HasDegree (fun _ : ℝ => rot c) 0 := by
  refine ⟨continuous_const, fun _ => c, continuous_const, ?_, ?_⟩
  · intro x; simp
  · intro x
    refine ⟨1, one_pos, ?_, ?_⟩
    · simp [rot]
    · simp [rot]

end Work.TMComp.RedProj
