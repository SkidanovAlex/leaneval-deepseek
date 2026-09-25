import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Core.Lev.sharpCut_fderiv_bounds
import Submission.Work.NN.Core.Lev.finset_prod_fderiv_bounds

namespace Work.NN.Newton.FTcut

open scoped BigOperators

/-- **The product cutoff `ftCut n a b` is Lipschitz with constant `≃ 1/(b-a)`.**

`ftCut n a b z = ∏ j, sharpCut a b (z j)` is a product of `n` factors each of which is
`1`-bounded and `C₀/(b-a)`-Lipschitz on `ℂ` (`Work.NN.Core.Lev.sharpCut_fderiv_bounds`).
Telescoping the difference of the two products
(`Work.NN.Core.Lev.norm_prod_sub_prod_le`) turns the `n` individual differences into a sum,
each term of which is bounded by `C₀/(b-a) * ‖x - y‖` because `‖x j - y j‖ ≤ ‖x - y‖` in the
sup norm on `Fin n → ℂ`.  This produces the constant `max 1 (n * C₀)`, which is positive and
independent of `a`, `b`, `x`, `y` (it does depend on `n`, as it must). -/
theorem ftCut_lipschitz {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), 0 < a → a < b → ∀ (x y : Fin n → ℂ),
      ‖Work.NN.Newton.ftCut n a b x - Work.NN.Newton.ftCut n a b y‖
        ≤ C * (1 / (b - a)) * ‖x - y‖ := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.NN.Core.Lev.sharpCut_fderiv_bounds
  refine ⟨max 1 ((n : ℝ) * C₀), lt_max_of_lt_left zero_lt_one, ?_⟩
  intro a b ha hab x y
  obtain ⟨-, hlip, -⟩ := hC₀ a b ha hab
  have hbapos : 0 < b - a := by linarith
  have hL0 : 0 ≤ C₀ * (1 / (b - a)) := mul_nonneg hC₀pos.le (one_div_pos.mpr hbapos).le
  -- each individual factor changes by at most `C₀/(b-a) * ‖x - y‖`
  have hsteps : ∀ j : Fin n, ‖Work.NN.Core.sharpCut a b (x j) - Work.NN.Core.sharpCut a b (y j)‖
      ≤ (C₀ * (1 / (b - a))) * ‖x - y‖ := by
    intro j
    refine (hlip (x j) (y j)).trans ?_
    have hxy : ‖x j - y j‖ ≤ ‖x - y‖ := by
      have h := norm_le_pi_norm (x - y) j
      simpa [Pi.sub_apply] using h
    exact mul_le_mul_of_nonneg_left hxy hL0
  -- telescope the difference of the two products
  have hprod := Work.NN.Core.Lev.norm_prod_sub_prod_le (Finset.univ : Finset (Fin n))
      (fun j => Work.NN.Core.sharpCut a b (x j))
      (fun j => Work.NN.Core.sharpCut a b (y j))
      (fun _ => C₀ * (1 / (b - a)))
      (t := ‖x - y‖) (norm_nonneg _)
      (fun i _ => hL0)
      (fun i _ => Work.NN.Core.norm_sharpCut_le_one a b (x i))
      (fun i _ => Work.NN.Core.norm_sharpCut_le_one a b (y i))
      (fun i _ => hsteps i)
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin n)), (C₀ * (1 / (b - a))))
      = (n : ℝ) * C₀ * (1 / (b - a)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hbound : ‖Work.NN.Newton.ftCut n a b x - Work.NN.Newton.ftCut n a b y‖
      ≤ ((n : ℝ) * C₀ * (1 / (b - a))) * ‖x - y‖ := by
    rw [Work.NN.Newton.ftCut_apply, Work.NN.Newton.ftCut_apply]
    rw [← hsum]
    exact hprod
  calc ‖Work.NN.Newton.ftCut n a b x - Work.NN.Newton.ftCut n a b y‖
      ≤ ((n : ℝ) * C₀ * (1 / (b - a))) * ‖x - y‖ := hbound
    _ ≤ max 1 ((n : ℝ) * C₀) * (1 / (b - a)) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) ((n : ℝ) * C₀))
            (one_div_pos.mpr hbapos).le) (norm_nonneg _)

end Work.NN.Newton.FTcut
