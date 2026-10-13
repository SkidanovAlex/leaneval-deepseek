import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Interp.abs_eval_sub_le

namespace Work.WilkiesH.Interp

theorem abs_eval_map_sub_le_sum {n : ℕ} (P : MvPolynomial (Fin n) ℤ) {y y' : Fin n → ℝ}
    (hy : ∀ i, |y i| ≤ 1) (hy' : ∀ i, |y' i| ≤ 1) :
    |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
        - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))|
      ≤ ∑ m ∈ P.support,
          |(P.coeff m : ℝ)| * (((∑ i, m i : ℕ) : ℝ) * (∑ i, |y i - y' i|)) := by
  -- Each coordinate variation is bounded by the total variation.
  have hyρ : ∀ i, |y i - y' i| ≤ ∑ j, |y j - y' j| := fun i =>
    Finset.single_le_sum (s := Finset.univ) (f := fun j => |y j - y' j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  -- Evaluation of the (real) polynomial as its monomial sum.
  have heval : ∀ z : Fin n → ℝ,
      MvPolynomial.eval z (P.map (Int.castRingHom ℝ))
        = ∑ m ∈ P.support, (P.coeff m : ℝ) * ∏ i, z i ^ (m i) := by
    intro z
    simp only [MvPolynomial.eval_map, MvPolynomial.eval₂_eq', Int.coe_castRingHom]
  rw [heval y, heval y']
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro m _
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_prod_sub_prod_le Finset.univ (fun i => m i) y y' (∑ i, |y i - y' i|) hy hy' hyρ)
    (abs_nonneg _)

end Work.WilkiesH.Interp
