import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# A norm bound for integer vectors through an invertible linear map

If `L` is an invertible complex `n × n` matrix (`n` nonempty), then the sup-norm of an
integer vector `y` is controlled by the `ℓ¹`-norm of the row-wise linear forms `L y`:

  `‖y‖ ≤ C * ∑ i, ‖∑ j, L i j * (y j : ℂ)‖`

This is the elementary "finite-dimensional norms are equivalent" input used to compare
the natural height `‖·‖` on integer vectors with the height coming from the forms
`∑ j, L i j * x j` appearing in Schmidt's subspace theorem.

The proof is a direct estimate: writing `M = L.det⁻¹ • L.adjugate` for the (explicit)
inverse of `L`, every coordinate `y i` is a bounded combination of the forms.
-/

open scoped BigOperators

namespace Commons.Analysis.Normed

theorem intVec_norm_le_sum_forms {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (L : Matrix n n ℂ) (hL : L.det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : n → ℤ,
      ‖y‖ ≤ C * (∑ i, ‖∑ j, L i j * (y j : ℂ)‖) := by
  classical
  -- The explicit inverse of `L`.
  set M : Matrix n n ℂ := (L.det)⁻¹ • L.adjugate with hM
  have hML : M * L = 1 := by
    rw [hM, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ hL, one_smul]
  -- The constant: the sum of the absolute values of the entries of `M`.
  set C₀ : ℝ := ∑ i, ∑ j, ‖M i j‖ with hC₀
  have hC₀_nonneg : 0 ≤ C₀ := by
    rw [hC₀]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
  have hMij : ∀ i j : n, ‖M i j‖ ≤ C₀ := by
    intro i j
    rw [hC₀]
    calc ‖M i j‖ ≤ ∑ j', ‖M i j'‖ :=
          Finset.single_le_sum (fun a _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖M i' j'‖ :=
          Finset.single_le_sum
            (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg _)) (Finset.mem_univ i)
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro y
  -- The vector of forms.
  set z : n → ℂ := L.mulVec (fun i => (y i : ℂ)) with hz
  have hzsum : ∀ i, z i = ∑ j, L i j * (y j : ℂ) := by
    intro i
    rw [hz]
    simp [Matrix.mulVec, dotProduct]
  -- `M` really inverts `L` on the vector level.
  have hyc : (fun i => (y i : ℂ)) = M.mulVec z := by
    rw [hz, Matrix.mulVec_mulVec, hML, Matrix.one_mulVec]
  have hS : 0 ≤ ∑ j : n, ‖z j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  -- Every coordinate is bounded by `C₀` times the `ℓ¹`-norm of the forms.
  have hMi : ∀ i, ‖y i‖ ≤ C₀ * ∑ j : n, ‖z j‖ := by
    intro i
    have key : ‖(y i : ℂ)‖ ≤ C₀ * ∑ j : n, ‖z j‖ := by
      calc ‖(y i : ℂ)‖ = ‖(M.mulVec z) i‖ := by rw [congrFun hyc i]
        _ = ‖∑ j, M i j * z j‖ := by
              rw [show (M.mulVec z) i = ∑ j, M i j * z j from by
                    simp [Matrix.mulVec, dotProduct]]
        _ ≤ ∑ j, ‖M i j * z j‖ := norm_sum_le _ _
        _ = ∑ j, ‖M i j‖ * ‖z j‖ := Finset.sum_congr rfl (fun j _ => norm_mul _ _)
        _ ≤ ∑ j, C₀ * ‖z j‖ :=
              Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hMij i j) (norm_nonneg _))
        _ = C₀ * ∑ j, ‖z j‖ := by rw [Finset.mul_sum]
    rw [Int.norm_eq_abs]
    simpa only [Complex.norm_intCast] using key
  -- Pass to the sup-norm on the left.
  have hbound : ‖y‖ ≤ C₀ * ∑ j : n, ‖z j‖ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC₀_nonneg hS)]
    exact hMi
  have hgoal_eq : (∑ i, ‖∑ j, L i j * (y j : ℂ)‖) = ∑ i : n, ‖z i‖ :=
    Finset.sum_congr rfl (fun i _ => by rw [hzsum i])
  rw [hgoal_eq]
  exact le_trans hbound (mul_le_mul_of_nonneg_right (by linarith) hS)

end Commons.Analysis.Normed