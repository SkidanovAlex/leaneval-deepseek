import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod

set_option linter.unusedVariables false

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

theorem norm_iMulti_le_pow_of_norm_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {i : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (u v : Fin i → E)
    (hu : ∀ k, ‖u k‖ = 1) (hv : ∀ k, ‖v k - u k‖ ≤ δ) :
    ‖exteriorPower.ιMulti ℝ i v‖ ≤ (1 + δ) ^ i := by
  have hstep : ∀ k : Fin i, ‖v k‖ ≤ 1 + δ := by
    intro k
    calc ‖v k‖ = ‖(v k - u k) + u k‖ := by rw [sub_add_cancel]
      _ ≤ ‖v k - u k‖ + ‖u k‖ := norm_add_le _ _
      _ ≤ δ + 1 := by rw [hu k]; linarith [hv k]
      _ = 1 + δ := by ring
  calc ‖exteriorPower.ιMulti ℝ i v‖ ≤ ∏ k : Fin i, ‖v k‖ :=
        exteriorPower_norm_wedge_le_prod v
    _ ≤ ∏ k : Fin i, (1 + δ) :=
        Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hstep k)
    _ = (1 + δ) ^ i := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Commons.Analysis.InnerProductSpace
