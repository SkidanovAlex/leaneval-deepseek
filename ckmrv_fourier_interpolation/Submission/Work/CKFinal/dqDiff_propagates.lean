import Mathlib
import Submission.Work.CKFinal.DQDefs

noncomputable section

open UpperHalfPlane
open scoped Manifold Topology

namespace Work.CKFinal

/-! ## Linearity of the two defect operators in the function variable

`Work.Kernels.T2op` and `Work.Asymptotics.S2op k` are both finite linear combinations of
evaluations of the function at points of `ℍ` (for `S2op`, with coefficients depending on the
point but not on the function).  Consequently they commute with the operations by which
`dqDiff` is built, and the defects of a difference quotient are the difference quotients of the
defects. -/

/-- Division by a constant preserves holomorphy of a function on `ℍ`. -/
private lemma mdiff_div_const {f : ℍ → ℂ} (hf : MDiff f) (c : ℂ) : MDiff (fun τ => f τ / c) := by
  have h : (fun τ : ℍ => f τ / c) = c⁻¹ • f := by ext τ; simp [div_eq_mul_inv, mul_comm]
  rw [h]; exact hf.const_smul c⁻¹

/-- `(T-I)²` is linear in the function variable: it commutes with the difference quotients of a
one-parameter family. -/
lemma T2op_dqDiff (G : ℝ → ℍ → ℂ) (r a b : ℝ) :
    Work.Kernels.T2op (dqDiff G r a b) =
      dqDiff (fun s : ℝ => Work.Kernels.T2op (G s)) r a b := by
  ext τ
  simp only [Work.Kernels.T2op, dqDiff_apply]
  ring

/-- `S(T-I)²` is linear in the function variable: it commutes with the difference quotients of a
one-parameter family. -/
lemma S2op_dqDiff (k : ℤ) (G : ℝ → ℍ → ℂ) (r a b : ℝ) :
    Work.Asymptotics.S2op k (dqDiff G r a b) =
      dqDiff (fun s : ℝ => Work.Asymptotics.S2op k (G s)) r a b := by
  ext τ
  simp only [Work.Asymptotics.S2op_apply_eq, Work.Kernels.slash_S_apply, dqDiff_apply]
  ring

/-- The second difference of difference quotients of a family `G` of solutions of
`T2op (G s) = H s`, `S2op k (G s) = 0` satisfies the hypotheses of the propagation theorem
`Work.Asymptotics.Propagates`, with defects the corresponding second difference of difference
quotients of `H` and `0`. -/
lemma dqDiff_propagates (k : ℤ) (G H : ℝ → UpperHalfPlane → ℂ) (r a b : ℝ)
    (hG : ∀ s : ℝ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (G s))
    (hH : ∀ s : ℝ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (H s))
    (hT : ∀ (s : ℝ) (τ : UpperHalfPlane), Work.Kernels.T2op (G s) τ = H s τ)
    (hS : ∀ (s : ℝ) (τ : UpperHalfPlane), Work.Asymptotics.S2op k (G s) τ = 0) :
    Work.Asymptotics.Propagates k Set.univ (dqDiff G r a b) (dqDiff H r a b) 0 := by
  -- the defect of `dqDiff G` is `dqDiff H`
  have hTfun : (fun s : ℝ => Work.Kernels.T2op (G s)) = H :=
    funext fun s => funext (hT s)
  -- and the second defect of `dqDiff G` vanishes
  have hSfun : (fun s : ℝ => Work.Asymptotics.S2op k (G s)) = (fun _ : ℝ => 0) :=
    funext fun s => funext (hS s)
  refine ⟨isOpen_univ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `dqDiff H r a b` is holomorphic
    show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ =>
      (H (r + a) τ - H r τ) / a - (H (r + b) τ - H r τ) / b)
    exact (mdiff_div_const ((hH (r + a)).sub (hH r)) a).sub
      (mdiff_div_const ((hH (r + b)).sub (hH r)) b)
  · -- the zero defect is holomorphic
    exact mdifferentiable_const
  · -- `dqDiff G r a b` is holomorphic on `Set.univ`
    show MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ =>
      (G (r + a) τ - G r τ) / a - (G (r + b) τ - G r τ) / b) Set.univ
    exact ((mdiff_div_const ((hG (r + a)).sub (hG r)) a).sub
      (mdiff_div_const ((hG (r + b)).sub (hG r)) b)).mdifferentiableOn
  · -- the `(T-I)²` defect
    intro τ _ _ _
    rw [T2op_dqDiff, hTfun]
  · -- the `S(T-I)²` defect
    intro τ _ _ _
    rw [S2op_dqDiff, hSfun]
    simp

end Work.CKFinal
