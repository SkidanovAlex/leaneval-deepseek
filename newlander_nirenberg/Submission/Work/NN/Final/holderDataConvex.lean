import Mathlib

namespace Work.NN.Final

open scoped ContDiff

/-- Mean value inequality wrapper: on a convex set, a bound on the (within) derivative of a
function `g` gives a Lipschitz bound for `g`. -/
private lemma lipschitz_of_fderivWithin_bound
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {s : Set E} (hc : Convex ℝ s)
    {g : E → G} {C : ℝ}
    (hder : ∀ x ∈ s, HasFDerivWithinAt g (fderivWithin ℝ g s x) s x)
    (hbound : ∀ x ∈ s, ‖fderivWithin ℝ g s x‖ ≤ C) {p q : E} (hp : p ∈ s) (hq : q ∈ s) :
    ‖g p - g q‖ ≤ C * ‖p - q‖ := by
  simpa [norm_sub_rev] using hc.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hp hq

theorem holderDataConvex {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} {s : Set E}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : ContDiff ℝ ⊤ f)
    {A : ℕ → ℝ} (hA : ∀ m, ∀ x ∈ s, ‖iteratedFDeriv ℝ m f x‖ ≤ A m) (hA0 : ∀ m, 0 ≤ A m)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L : ℝ, ∃ D E : ℕ → ℝ,
      (0 ≤ L ∧ ∀ p ∈ s, ∀ q ∈ s, ‖f p - f q‖ ≤ L * ‖p - q‖) ∧
      (∀ m, 1 ≤ m → ∀ p ∈ s, ‖iteratedFDerivWithin ℝ m f s p‖ ≤ D m) ∧
      (∀ m, 1 ≤ m → ∀ p ∈ s, ∀ q ∈ s,
        ‖iteratedFDerivWithin ℝ m f s p - iteratedFDerivWithin ℝ m f s q‖ ≤ E m * ‖p - q‖ ^ α) := by
  -- The iterate `iteratedFDerivWithin ℝ m f s` is differentiable within `s`.
  have hdiff : ∀ (m : ℕ) (x : E), x ∈ s →
      HasFDerivWithinAt (iteratedFDerivWithin ℝ m f s)
        (fderivWithin ℝ (iteratedFDerivWithin ℝ m f s) s x) s x := by
    intro m x hx
    exact (((hf.contDiffOn).differentiableOn_iteratedFDerivWithin (by simp)
      hs.uniqueDiffOn) x hx).hasFDerivWithinAt
  -- The (within) derivative of the `m`-th iterate is bounded by `A (m+1)`.
  have hbound : ∀ (m : ℕ) (x : E), x ∈ s →
      ‖fderivWithin ℝ (iteratedFDerivWithin ℝ m f s) s x‖ ≤ A (m + 1) := by
    intro m x hx
    rw [norm_fderivWithin_iteratedFDerivWithin]
    rw [iteratedFDerivWithin_of_isOpen (m + 1) hs hx]
    exact hA (m + 1) x hx
  -- Lipschitz bound for every iterate, by the mean value inequality on the convex set `s`.
  have hLip : ∀ (m : ℕ) (p q : E), p ∈ s → q ∈ s →
      ‖iteratedFDerivWithin ℝ m f s p - iteratedFDerivWithin ℝ m f s q‖
        ≤ A (m + 1) * ‖p - q‖ :=
    fun m p q hp hq => lipschitz_of_fderivWithin_bound hc (hdiff m) (hbound m) hp hq
  refine ⟨A 1, A, fun m => max (A (m + 1)) (2 * A m), ?_, ?_, ?_⟩
  · -- the Lipschitz bound for `f` itself, from the case `m = 0`
    refine ⟨hA0 1, ?_⟩
    intro p hp q hq
    have h0 := hLip 0 p q hp hq
    rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero] at h0
    simpa [dist_eq_norm, zero_add] using h0
  · -- the `D` bounds
    intro m hm p hp
    rw [iteratedFDerivWithin_of_isOpen m hs hp]
    exact hA m p hp
  · -- the `E` (Hölder) bounds
    intro m hm p hp q hq
    have hlip := hLip m p q hp hq
    have hpnorm : ‖iteratedFDerivWithin ℝ m f s p‖ ≤ A m := by
      rw [iteratedFDerivWithin_of_isOpen m hs hp]; exact hA m p hp
    have hqnorm : ‖iteratedFDerivWithin ℝ m f s q‖ ≤ A m := by
      rw [iteratedFDerivWithin_of_isOpen m hs hq]; exact hA m q hq
    rcases le_or_gt ‖p - q‖ 1 with hle | hgt
    · -- small distance: the Lipschitz bound, converted with `t ≤ t ^ α`
      have hpow : ‖p - q‖ ≤ ‖p - q‖ ^ α := by
        rcases eq_or_lt_of_le (norm_nonneg (p - q)) with hz | hpos
        · rw [← hz, Real.zero_rpow (ne_of_gt hα)]
        · calc ‖p - q‖ = ‖p - q‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ ‖p - q‖ ^ α := Real.rpow_le_rpow_of_exponent_ge hpos hle hα1
      calc ‖iteratedFDerivWithin ℝ m f s p - iteratedFDerivWithin ℝ m f s q‖
          ≤ A (m + 1) * ‖p - q‖ := hlip
        _ ≤ A (m + 1) * ‖p - q‖ ^ α := mul_le_mul_of_nonneg_left hpow (hA0 (m + 1))
        _ ≤ max (A (m + 1)) (2 * A m) * ‖p - q‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)
    · -- large distance: both values are bounded by `A m`
      have hpow : 1 ≤ ‖p - q‖ ^ α := Real.one_le_rpow (le_of_lt hgt) (le_of_lt hα)
      calc ‖iteratedFDerivWithin ℝ m f s p - iteratedFDerivWithin ℝ m f s q‖
          ≤ ‖iteratedFDerivWithin ℝ m f s p‖ + ‖iteratedFDerivWithin ℝ m f s q‖ :=
            norm_sub_le _ _
        _ ≤ A m + A m := add_le_add hpnorm hqnorm
        _ = 2 * A m := by ring
        _ = 2 * A m * 1 := by ring
        _ ≤ 2 * A m * ‖p - q‖ ^ α := mul_le_mul_of_nonneg_left hpow (by linarith [hA0 m])
        _ ≤ max (A (m + 1)) (2 * A m) * ‖p - q‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) α)

end Work.NN.Final
