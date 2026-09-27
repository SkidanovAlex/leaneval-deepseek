import Mathlib
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one

namespace Work.KT.EG.KLG

/-- **A unit on a line segment of matrices over `C(X, ℂ)` can be moved slightly towards `0`.**

If `a + b` is a unit of `Matrix (Fin n) (Fin n) C(X, ℂ))` (with `X` compact Hausdorff), then the
point `1` lies in the open set of parameters `t` for which `a + t • b` is a unit, so some
`t₀ ∈ [0, 1)` works too.

The proof writes `a + t • b = (a + b) * (1 - (1 - t) • ((a + b)⁻¹ * b))`, so it suffices to find
`t` near `1` for which the second factor is a unit; this is the Neumann-series criterion
`isUnit_one_sub_of_matNorm_lt_one` applied with the scalar `1 - t` small enough that the row-sum
norm of `(1 - t) • ((a + b)⁻¹ * b)` is `< 1`. -/
theorem exists_t0_unit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (a b : Matrix (Fin n) (Fin n) C(X, ℂ))
    (hab : IsUnit (a + b)) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < 1 ∧ IsUnit (a + t₀ • b) := by
  obtain ⟨u, hu⟩ := hab
  let C : Matrix (Fin n) (Fin n) C(X, ℂ) := (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) * b
  let M : NNReal := Finset.univ.sup (fun i : Fin n => ∑ j : Fin n, ‖C i j‖₊)
  let s : ℝ := (1/2) / ((M : ℝ) + 1)
  have hs_pos : 0 < s := by
    have h1 : s = (1/2) / ((M:ℝ)+1) := rfl
    rw [h1]; positivity
  have hs_den : s * ((M : ℝ) + 1) = 1/2 := by
    have h1 : s = (1/2) / ((M:ℝ)+1) := rfl
    rw [h1]; field_simp
  have hs_half : s ≤ 1/2 := by
    have h1 : (1:ℝ) ≤ (M : ℝ) + 1 := by
      have : (0:ℝ) ≤ (M : ℝ) := M.2
      linarith
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * ((M : ℝ) + 1) := mul_le_mul_of_nonneg_left h1 hs_pos.le
      _ = 1/2 := hs_den
  have hsM : s * (M : ℝ) < 1 := by
    have hm : (M : ℝ) < (M : ℝ) + 1 := by linarith
    have h2 : s * (M : ℝ) < s * ((M : ℝ) + 1) := mul_lt_mul_of_pos_left hm hs_pos
    rw [hs_den] at h2; linarith
  have hrow : (Finset.univ.sup fun i : Fin n => ∑ j : Fin n, ‖(s • C) i j‖₊ : NNReal) < 1 := by
    have key : ∀ i : Fin n, ∑ j : Fin n, ‖(s • C) i j‖₊ ≤ ‖s‖₊ * M := by
      intro i
      have hsum : (∑ j : Fin n, ‖(s • C) i j‖₊)
          = ‖s‖₊ * ∑ j : Fin n, ‖C i j‖₊ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Matrix.smul_apply, nnnorm_smul]
      rw [hsum]
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup (f := fun i : Fin n => ∑ j : Fin n, ‖C i j‖₊) (Finset.mem_univ i))
        zero_le
    calc (Finset.univ.sup fun i : Fin n => ∑ j : Fin n, ‖(s • C) i j‖₊ : NNReal)
        ≤ ‖s‖₊ * M := Finset.sup_le (fun i _ => key i)
      _ < 1 := by
        rw [← NNReal.coe_lt_coe, NNReal.coe_mul, NNReal.coe_one, Real.nnnorm_of_nonneg hs_pos.le,
          NNReal.coe_mk]
        exact hsM
  have hunit : IsUnit (1 - s • C) := Work.KT.isUnit_one_sub_of_matNorm_lt_one (s • C) hrow
  have hfactor : (u : Matrix (Fin n) (Fin n) C(X, ℂ)) * (1 - s • C) = a + (1 - s) • b := by
    have h1 : (u : Matrix (Fin n) (Fin n) C(X, ℂ)) * (s • C) = s • b := by
      rw [show C = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) * b from rfl]
      rw [mul_smul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    rw [Matrix.mul_sub, h1, hu, mul_one]
    rw [sub_smul, one_smul]
    abel
  refine ⟨1 - s, by linarith, by linarith, ?_⟩
  rw [← hfactor]
  exact IsUnit.mul ⟨u, rfl⟩ hunit

end Work.KT.EG.KLG
