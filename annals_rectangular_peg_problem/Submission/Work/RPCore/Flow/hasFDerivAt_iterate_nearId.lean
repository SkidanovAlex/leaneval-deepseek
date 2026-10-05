import Mathlib

namespace Work.RPCore.Flow

lemma hasFDerivAt_iterate_nearId {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) {β : ℝ} (hβ : 0 ≤ β)
    (hf : ∀ y : E, ∃ A : E →L[ℝ] E, HasFDerivAt f A y ∧ ‖A - 1‖ ≤ β) :
    ∀ n : ℕ, ∀ z : E, ∃ A : E →L[ℝ] E,
      HasFDerivAt (f^[n]) A z ∧ ‖A - 1‖ ≤ (1 + β)^n - 1 := by
  intro n
  induction n with
  | zero =>
    intro z
    exact ⟨1, hasFDerivAt_id z, by simp⟩
  | succ n ih =>
    intro z
    obtain ⟨A1, hA1, hA1n⟩ := ih z
    obtain ⟨A2, hA2, hA2n⟩ := hf (f^[n] z)
    refine ⟨A2.comp A1, ?_, ?_⟩
    · simpa only [Function.iterate_succ'] using hA2.comp z hA1
    · -- bound on the norm of the inner derivative
      have hA1norm : ‖A1‖ ≤ (1 + β) ^ n := by
        calc ‖A1‖ = ‖(A1 - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖A1 - 1‖ + ‖1‖ := norm_add_le _ _
          _ ≤ ((1 + β) ^ n - 1) + 1 :=
              add_le_add hA1n ContinuousLinearMap.norm_id_le
          _ = (1 + β) ^ n := by ring
      -- algebraic decomposition of the composed derivative minus the identity
      have hkey : A2.comp A1 - 1 = (A2 - 1).comp A1 + (A1 - 1) := by
        ext v
        simp [ContinuousLinearMap.comp_apply]
      calc ‖A2.comp A1 - 1‖ = ‖(A2 - 1).comp A1 + (A1 - 1)‖ := by rw [hkey]
        _ ≤ ‖(A2 - 1).comp A1‖ + ‖A1 - 1‖ := norm_add_le _ _
        _ ≤ ‖A2 - 1‖ * ‖A1‖ + ‖A1 - 1‖ :=
            add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) le_rfl
        _ ≤ β * (1 + β) ^ n + ((1 + β) ^ n - 1) :=
            add_le_add (mul_le_mul hA2n hA1norm (norm_nonneg _) hβ) hA1n
        _ = (1 + β) ^ (n + 1) - 1 := by ring

end Work.RPCore.Flow
