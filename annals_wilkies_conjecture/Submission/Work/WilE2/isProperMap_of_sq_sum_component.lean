import Mathlib

namespace Work.WilE2

/-- For `w : Fin m → ℝ`, the sup norm of `w` is bounded by the square root of the sum of the
squares of its coordinates: a quadratic upper bound on `∑ j, (w j) ^ 2` bounds `w` itself. -/
lemma norm_le_sqrt_sum_sq {m : ℕ} (w : Fin m → ℝ) {B : ℝ}
    (h : ∑ j : Fin m, (w j) ^ 2 ≤ B) : ‖w‖ ≤ Real.sqrt B := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)]
  intro j
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact le_trans (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ j)) h

/-- If a map `f : (Fin m → ℝ) → (Fin k → ℝ)` has an `i`-th component equal to
`w ↦ ‖w‖² - c`, then the preimage of any compact set is bounded. -/
lemma isBounded_preimage_of_sq_sum_component {k m : ℕ} (c : ℝ)
    (f : (Fin m → ℝ) → (Fin k → ℝ)) (i : Fin k)
    (hcomp : ∀ w, f w i = (∑ j : Fin m, (w j) ^ 2) - c)
    {K : Set (Fin k → ℝ)} (hK : IsCompact K) : Bornology.IsBounded (f ⁻¹' K) := by
  rw [isBounded_iff_forall_norm_le]
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (hK.image (continuous_apply i)).isBounded
  refine ⟨Real.sqrt (R + c), fun w hw => ?_⟩
  have hwi : |f w i| ≤ R := by
    have h' := hR (f w i) ⟨f w, hw, rfl⟩
    rwa [Real.norm_eq_abs] at h'
  rw [hcomp w] at hwi
  have hsum : ∑ j : Fin m, (w j) ^ 2 ≤ R + c := by
    have := (abs_le.mp hwi).2; linarith
  exact norm_le_sqrt_sum_sq w hsum

theorem isProperMap_of_sq_sum_component {k m : ℕ} (c : ℝ)
    (f : (Fin m → ℝ) → (Fin k → ℝ)) (hf : Continuous f) (i : Fin k)
    (hcomp : ∀ w, f w i = (∑ j : Fin m, (w j) ^ 2) - c) : IsProperMap f := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hf, fun K hK => ?_⟩
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨hK.isClosed.preimage hf, isBounded_preimage_of_sq_sum_component c f i hcomp hK⟩

end Work.WilE2
