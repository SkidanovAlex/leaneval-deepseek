import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trace bound `S² ≤ n |Ric|²`

For an algebraic curvature tensor `R` on `ℝⁿ` (convention: `Rᵢⱼₖₗ = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`), the
scalar curvature is the trace of the Ricci tensor `Ricᵢⱼ = ∑ₖ Rₖᵢₖⱼ`:

  `scalAlg R = ∑ᵢ Ricᵢᵢ`

(componentwise: `Rᵢⱼᵢⱼ = -Rⱼᵢᵢⱼ = Rⱼᵢⱼᵢ` by the two antisymmetries). Since the trace of a matrix is
the pairing of the matrix with the identity, Cauchy–Schwarz gives

  `(∑ᵢ Ricᵢᵢ)² ≤ n · ∑ᵢⱼ Ricᵢⱼ² = n · ricSq R`.

This is item (3) of `Work.Diff.Alg.pinching_algebra`.

Note that no symmetry of the Ricci tensor is needed: for the second inequality we simply drop the
off-diagonal terms of the (manifestly nonnegative) sum `∑ᵢⱼ Ricᵢⱼ²`.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

/-- The scalar curvature is the sum of the diagonal entries of the Ricci tensor
`Ricᵢⱼ = ∑ₖ Rₖᵢₖⱼ`. -/
theorem scalAlg_eq_sum_ricDiag (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) :
    scalAlg R = ∑ i : Fin n, ∑ k, R k i k i := by
  simp only [scalAlg]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- `Rᵢₖᵢₖ = - Rₖᵢᵢₖ = Rₖᵢₖᵢ`
  have h1 := hR.1 i k i k
  have h2 := IsAlgCurv_antisym₃₄ hR k i i k
  linarith

/-- Item (3) of `Work.Diff.Alg.pinching_algebra`: `scalAlg R ^ 2 ≤ n * ricSq R`. -/
theorem scal_sq_le_ricSq (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) :
    scalAlg R ^ 2 ≤ (n : ℝ) * ricSq R := by
  rw [scalAlg_eq_sum_ricDiag n R hR, ricSq]
  -- Cauchy–Schwarz on the `Fin n`-indexed family `i ↦ Ricᵢᵢ`
  have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n => (∑ k, R k i k i))
  rw [hcard] at hCS
  -- each diagonal square is dominated by the corresponding row of `∑ᵢⱼ Ricᵢⱼ²`
  have hstep : (∑ i : Fin n, (∑ k, R k i k i) ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n, (∑ k, R k i k j) ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => (∑ k, R k i k j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith [hCS, mul_le_mul_of_nonneg_left hstep hnn]

end Work.Diff.Alg.PA
