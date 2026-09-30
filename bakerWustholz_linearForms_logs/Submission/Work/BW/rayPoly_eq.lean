import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A polynomial over `ℚ` is determined by its values on all sufficiently large natural
numbers: if `q₁` and `q₂` agree at `t` for all large `t`, then `q₁ = q₂`. -/
lemma IsRayPoly.unique {N : ℕ} {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)} {q₁ q₂ : Polynomial ℚ}
    (h₁ : IsRayPoly N D I q₁) (h₂ : IsRayPoly N D I q₂) : q₁ = q₂ := by
  rw [IsRayPoly] at h₁ h₂
  obtain ⟨a₁, ha₁⟩ := Filter.eventually_atTop.mp h₁
  obtain ⟨a₂, ha₂⟩ := Filter.eventually_atTop.mp h₂
  -- `q₁ - q₂` has infinitely many roots, namely `↑(n + max a₁ a₂)` for `n : ℕ`.
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective
    (f := fun n : ℕ => ((n + max a₁ a₂ : ℕ) : ℚ)) ?_)
  · rintro x ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq]
    have h1 : ((rayHilb N D I (n + max a₁ a₂) : ℕ) : ℚ) = q₁.eval ((n + max a₁ a₂ : ℕ) : ℚ) :=
      ha₁ _ (by omega)
    have h2 : ((rayHilb N D I (n + max a₁ a₂) : ℕ) : ℚ) = q₂.eval ((n + max a₁ a₂ : ℕ) : ℚ) :=
      ha₂ _ (by omega)
    rw [← h1, h2]
  · intro n₁ n₂ h
    exact Nat.add_right_cancel (Nat.cast_injective h)

/-- The ray Hilbert polynomial is unique: if a polynomial `q` agrees with `t ↦ dim (R/I)_{tD}`
for all large `t`, then `q = rayPoly N D I`. (A nonzero polynomial over `ℚ` has finitely many
roots and `t ↦ (t : ℚ)` is injective on `ℕ`.) -/
theorem rayPoly_eq {N : ℕ} {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)} {q : Polynomial ℚ}
    (h : IsRayPoly N D I q) : rayPoly N D I = q := by
  unfold rayPoly
  rw [dite_eq_left (show ∃ q, IsRayPoly N D I q from ⟨q, h⟩)]
  exact IsRayPoly.unique (Classical.choose_spec _) h

end Work.BW
