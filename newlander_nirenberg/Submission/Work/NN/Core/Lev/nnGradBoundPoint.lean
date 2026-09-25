import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger

/-!
# Pointwise bound of the real differential by the Wirtinger derivatives

For an arbitrary (not necessarily differentiable) map `v : ℂⁿ → ℂ` and any point `z`, the
operator norm of the real differential `fderiv ℝ v z : ℂⁿ →L[ℝ] ℂ` is controlled by the
Wirtinger derivatives `∂_j v`, `∂̄_j v`:

`‖fderiv ℝ v z‖² ≤ C · Σ_j (‖∂_j v(z)‖² + ‖∂̄_j v(z)‖²)`,

with a constant `C` depending only on `n`.  The real differential is determined by the values on
the real basis `{e_j, i·e_j}`, and `fderiv_eq_sum_wirtinger` rewrites it in terms of `∂_j v` and
`∂̄_j v`; the rest is Cauchy–Schwarz and `(a+b)² ≤ 2(a²+b²)`.

Combined with `norm_fderiv_le_sum_wirtinger` (`‖fderiv‖ ≤ 2 Σ_j (‖∂_j v‖ + ‖∂̄_j v‖)`) this gives
the constant `8n`.
-/

namespace Work.NN.Core.Lev

theorem nnGradBoundPoint {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n),
      ‖fderiv ℝ v z‖ ^ 2
        ≤ C * ∑ j, (‖Work.CR.Flat.dCoord j v z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) := by
  refine ⟨8 * (n : ℝ), ?_, ?_⟩
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    nlinarith
  · intro v z
    set T : ℝ := ∑ j, (‖Work.CR.Flat.dCoord j v z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2)
      with hT
    set S : ℝ := ∑ j, (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖)
      with hS
    have h1 : ‖fderiv ℝ v z‖ ≤ 2 * S := by
      rw [hS]
      exact Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger v z
    have h2 : ‖fderiv ℝ v z‖ ^ 2 ≤ 4 * S ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ v z)) h1 2
      nlinarith [h]
    have h4 : ∀ j : Fin n, (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖) ^ 2
        ≤ 2 * (‖Work.CR.Flat.dCoord j v z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) := by
      intro j
      nlinarith [sq_nonneg (‖Work.CR.Flat.dCoord j v z‖ - ‖Work.CR.Flat.dbarCoord j v z‖)]
    have h3 : S ^ 2 ≤ 2 * (n : ℝ) * T := by
      rw [hS, hT]
      calc (∑ j, (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖)) ^ 2
          ≤ (n : ℝ) * ∑ j,
              (‖Work.CR.Flat.dCoord j v z‖ + ‖Work.CR.Flat.dbarCoord j v z‖) ^ 2 := by
            simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
              (f := fun j : Fin n => ‖Work.CR.Flat.dCoord j v z‖
                + ‖Work.CR.Flat.dbarCoord j v z‖)
        _ ≤ (n : ℝ) * ∑ j, 2 * (‖Work.CR.Flat.dCoord j v z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h4 j) (by positivity)
        _ = 2 * (n : ℝ) * ∑ j, (‖Work.CR.Flat.dCoord j v z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j v z‖ ^ 2) := by
            rw [← Finset.mul_sum]; ring
    calc ‖fderiv ℝ v z‖ ^ 2 ≤ 4 * S ^ 2 := h2
      _ ≤ 4 * (2 * (n : ℝ) * T) := by nlinarith [h3]
      _ = (8 * (n : ℝ)) * T := by ring

end Work.NN.Core.Lev
