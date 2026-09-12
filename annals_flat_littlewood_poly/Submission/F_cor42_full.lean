import Mathlib
import Submission.F_pcoloring
import Submission.F_cor42

noncomputable section
open scoped BigOperators
namespace Submission
namespace Discrepancy

/-- Corollary 4.2 specialized with the actual partial-colouring lemma (Theorem 4.1):
given `Σ_j exp(-c_j^2/196) ≤ n/16` there is a full ±1 colouring with
`|⟨x - x0, v_j⟩| ≤ (c_j + 30) * sqrt n * supAbs(v_j)` for every j. -/
theorem cor42_full (n m : ℕ) (v : Fin m → (Fin n → ℝ)) (x0 : Fin n → ℝ)
    (hx0 : ∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ j : Fin m, Real.exp (-(c j) ^ 2 / 196) ≤ (n : ℝ) / 16) :
    ∃ x : Fin n → ℝ,
      (∀ i : Fin n, x i = -1 ∨ x i = 1) ∧
      (∀ j : Fin m, |dot (fun i => x i - x0 i) (v j)| ≤ (c j + 30) * Real.sqrt n * supAbs (v j)) :=
  cor42 (fun n m v x0 hx0 c hc hsum => partial_coloring n m v x0 hx0 c hc hsum) n m v x0 hx0 c hc hsum

end Discrepancy
end Submission
