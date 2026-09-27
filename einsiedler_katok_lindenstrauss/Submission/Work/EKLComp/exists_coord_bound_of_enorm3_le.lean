import Mathlib
import Submission.Work.EKLComp.EucDefs

namespace Work.EKLComp

/-- Every coordinate of a vector is bounded by the hand-rolled Euclidean norm `enorm3`. -/
lemma abs_coord_le_enorm3 (v : Fin 3 → ℝ) (i : Fin 3) : |v i| ≤ enorm3 v := by
  rw [enorm3, dot3, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  calc (v i) ^ 2 = v i * v i := by ring
    _ ≤ ∑ j, v j * v j :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)

/-- `enorm3` is nonnegative. -/
lemma enorm3_nonneg (v : Fin 3 → ℝ) : 0 ≤ enorm3 v := by
  rw [enorm3]; exact Real.sqrt_nonneg _

/-- Auxiliary quantitative form of `exists_coord_bound_of_enorm3_le`: if `enorm3 (M *ᵥ m) ≤ C`
then every coordinate of the integer vector `m` is bounded by
`(∑ i, ∑ k, |M.adjugate i k|) * |C|`. -/
lemma coord_bound_aux (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 1) (C : ℝ)
    (m : Fin 3 → ℤ) (i : Fin 3)
    (hm : enorm3 (Matrix.mulVec M (fun j => (m j : ℝ))) ≤ C) :
    |(m i : ℝ)| ≤ (∑ i', ∑ k, |M.adjugate i' k|) * |C| := by
  have hC : 0 ≤ C := le_trans (enorm3_nonneg _) hm
  have h1 : M.adjugate * M = 1 := by rw [Matrix.adjugate_mul, hM, one_smul]
  have hadj :
      Matrix.mulVec M.adjugate (Matrix.mulVec M (fun j => (m j : ℝ))) = (fun j => (m j : ℝ)) := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hvi : (m i : ℝ)
      = ∑ k, M.adjugate i k * (Matrix.mulVec M (fun j => (m j : ℝ))) k := by
    have h := congrFun hadj i
    simpa [Matrix.mulVec, dotProduct] using h.symm
  have hrow_le : ∑ k, |M.adjugate i k| ≤ ∑ i', ∑ k, |M.adjugate i' k| :=
    Finset.single_le_sum (s := Finset.univ) (f := fun i' => ∑ k, |M.adjugate i' k|)
      (fun j _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ i)
  calc |(m i : ℝ)|
      = |∑ k, M.adjugate i k * (Matrix.mulVec M (fun j => (m j : ℝ))) k| := by rw [hvi]
    _ ≤ ∑ k, |M.adjugate i k * (Matrix.mulVec M (fun j => (m j : ℝ))) k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |M.adjugate i k| * |(Matrix.mulVec M (fun j => (m j : ℝ))) k| := by
        simp only [abs_mul]
    _ ≤ ∑ k, |M.adjugate i k| * C :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (le_trans (abs_coord_le_enorm3 _ k) hm) (abs_nonneg _))
    _ = (∑ k, |M.adjugate i k|) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i', ∑ k, |M.adjugate i' k|) * C := mul_le_mul_of_nonneg_right hrow_le hC
    _ = (∑ i', ∑ k, |M.adjugate i' k|) * |C| := by rw [abs_of_nonneg hC]

/-- If an integer vector `m` has `enorm3 (M *ᵥ m) ≤ C`, then its coordinates are bounded in terms
of `C` and the entries of `M`: since `M.adjugate * M = M.det • 1 = 1` (by `hM`),
`(m i : ℝ) = ∑ k, M.adjugate i k * (M *ᵥ m) k`, so `|(m i : ℝ)| ≤ (∑ k, |M.adjugate i k|) * C`
using `|x k| ≤ enorm3 x`.  (`C < 0` makes the hypothesis unsatisfiable; the conclusion is also true
then.) -/
theorem exists_coord_bound_of_enorm3_le (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 1) (C : ℝ) :
    ∃ K : ℕ, ∀ m : Fin 3 → ℤ,
      Work.EKLComp.enorm3 (Matrix.mulVec M (fun i => (m i : ℝ))) ≤ C → ∀ i, |(m i : ℝ)| ≤ K := by
  obtain ⟨K, hK⟩ := exists_nat_ge ((∑ i, ∑ k, |M.adjugate i k|) * |C|)
  exact ⟨K, fun m hm i => le_trans (coord_bound_aux M hM C m i hm) hK⟩

end Work.EKLComp
