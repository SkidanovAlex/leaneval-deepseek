import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.Pieces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

open MeasureTheory

/-- The half-line integrals `∫_{(0,∞)}` and `∫_{Iz}` agree, since `Iz = [0,∞)` and `{0}` is
null. -/
private theorem integral_Ioi_eq_integral_Iz (F : ℝ → ℝ) :
    (∫ z in Set.Ioi (0 : ℝ), F z) = ∫ z in Work.Spaces.Iz, F z := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))

/-- **The `(z∂_z)`-iterates of `L₁₂ f` summed over one order.**  For `f ∈ CoerAdm α`,
`0 < α ≤ 1` and `j ≤ n ≤ 3`,

  `∑_{b ≤ j} ∫_z (D_z^{j−b}(L₁₂ f)(z))² w(z)² dz ≤ (j+1)·107·(∫_θ K_θ²)·|f|²_{ℋⁿ}`,

by applying the single-order bound `L12f_DzdIter_sq_w_sq_le` to the `j+1` values
`c = j − b ≤ j ≤ n`. -/
theorem sum_L12_iter_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} (hn : n ≤ 3)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ n) :
    (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ((j : ℝ) + 1) * (107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α n f) := by
  set C : ℝ := 107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f
    with hC
  have hB : ∀ b ∈ Finset.range (j + 1),
      (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C := by
    intro b hb
    have hb' : b ≤ j := by
      rw [Finset.mem_range] at hb
      omega
    exact (L12f_DzdIter_sq_w_sq_le α hα hα1 hn hf (j - b) (by omega)).2
  have hconst : ((j : ℝ) + 1) * C = ∑ b ∈ Finset.range (j + 1), C := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst]
  calc (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      = ∑ b ∈ Finset.range (j + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
        simp_rw [integral_Ioi_eq_integral_Iz]
    _ ≤ ∑ _b ∈ Finset.range (j + 1), C := Finset.sum_le_sum hB

end Work.FTS.CoercivityFix.Transfer.E2norm
