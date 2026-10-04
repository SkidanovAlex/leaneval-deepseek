import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- The sectional curvature of an orthonormal pair is bounded by the sup-norm of the curvature
components: `|secK E u v| ≤ n⁴ · sup|E|`. With the hypothesis `|E i j k l| ≤ C σ` this gives
`|secK E u v| ≤ Cn · C · σ` for the explicit constant `Cn = n⁴`.

Since `secK E u v = ∑ᵢⱼₖₗ Eᵢⱼₖₗ uᵢ vⱼ uₖ vₗ` and each coordinate of an orthonormal vector
satisfies `|uᵢ| ≤ 1` (as `∑ᵢ uᵢ² = 1`), each of the `n⁴` summands is bounded by `C σ`. -/
theorem secK_bound_of_comp (n : ℕ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (E : Submission.Diff.Alg.Curv4 n) (σ C : ℝ), 0 ≤ C → 0 ≤ σ →
      (∀ i j k l : Fin n, |E i j k l| ≤ C * σ) →
      ∀ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v →
        |Submission.Diff.Alg.secK E u v| ≤ Cn * C * σ := by
  refine ⟨(n : ℝ) ^ 4, by positivity, ?_⟩
  intro E σ C hC hσ hE u v huv
  obtain ⟨huu, hvv, _⟩ := huv
  -- every coordinate of a unit vector is bounded by `1`
  have coord_one : ∀ (w : Fin n → ℝ) (i : Fin n), Submission.Diff.Alg.dot w w = 1 → |w i| ≤ 1 := by
    intro w i hw
    have h : w i * w i ≤ 1 := by
      rw [← hw, Submission.Diff.Alg.dot]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg (w j)) (Finset.mem_univ i)
    exact (sq_le_one_iff_abs_le_one _).mp (by simpa [pow_two] using h)
  have hu : ∀ i : Fin n, |u i| ≤ 1 := fun i => coord_one u i huu
  have hv : ∀ j : Fin n, |v j| ≤ 1 := fun j => coord_one v j hvv
  have hCσ : 0 ≤ C * σ := mul_nonneg hC hσ
  -- each of the `n⁴` summands of `secK` is bounded by `C σ`
  have hterm : ∀ i j k l : Fin n, |E i j k l * u i * v j * u k * v l| ≤ C * σ := by
    intro i j k l
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    calc |E i j k l| * |u i| * |v j| * |u k| * |v l|
        ≤ (C * σ) * 1 * 1 * 1 * 1 := by
          gcongr
          · exact hE i j k l
          · exact hu i
          · exact hv j
          · exact hu k
          · exact hv l
      _ = C * σ := by ring
  rw [Submission.Diff.Alg.secK, Submission.Diff.Alg.R4]
  calc |∑ i, ∑ j, ∑ k, ∑ l, E i j k l * u i * v j * u k * v l|
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, C * σ := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum; intro i _
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum; intro j _
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum; intro k _
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum; intro l _
        exact hterm i j k l
    _ ≤ (n : ℝ) ^ 4 * C * σ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring_nf
        exact le_refl _

end Work.Diff.Alg.Pinch
