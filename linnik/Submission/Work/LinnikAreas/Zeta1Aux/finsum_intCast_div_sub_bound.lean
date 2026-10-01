import Mathlib

namespace Work.LinnikAreas.Zeta1Aux

/-- Norm bound for a finitely supported integer-valued `finsum` of `1 / (s - u)`.

If `S : ℂ → ℤ` is nonnegative and finitely supported, and the points `u` in the
support of `S` stay at distance at least `δ` from `s`, then the norm of
`∑ᶠ u, (S u) * (1 / (s - u))` is at most `(∑ᶠ u, (S u)) / δ`. -/
lemma finsum_intCast_div_sub_bound {S : ℂ → ℤ} (hSfin : S.support.Finite)
    (hSnn : ∀ u, 0 ≤ S u) {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ u, S u ≠ 0 → δ ≤ ‖s - u‖) :
    ‖∑ᶠ u : ℂ, ((S u : ℤ) : ℂ) * (1 / (s - u))‖ ≤
      (∑ᶠ u : ℂ, ((S u : ℤ) : ℝ)) / δ := by
  -- Pointwise bound, valid for every `u` (the case `S u = 0` is trivial).
  have hterm : ∀ u : ℂ, ‖((S u : ℤ) : ℂ) * (1 / (s - u))‖ ≤ ((S u : ℤ) : ℝ) / δ := by
    intro u
    by_cases h0 : S u = 0
    · simp [h0]
    · have hnn : (0 : ℝ) ≤ ((S u : ℤ) : ℝ) := Int.cast_nonneg (hSnn u)
      have hnorm : ‖((S u : ℤ) : ℂ)‖ = ((S u : ℤ) : ℝ) := by
        rw [Complex.norm_intCast, abs_of_nonneg hnn]
      have hpos : 0 < ‖s - u‖ := lt_of_lt_of_le hδ (hsep u h0)
      have hle : ‖s - u‖⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hpos hδ).2 (hsep u h0)
      rw [norm_mul, hnorm, one_div, norm_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hle hnn
  -- Both `finsum`s are supported in the (finite) support of `S`.
  have hsuppL : Function.support (fun u : ℂ => ((S u : ℤ) : ℂ) * (1 / (s - u))) ⊆
      (hSfin.toFinset : Set ℂ) := by
    intro u hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hu ⊢
    exact fun h => hu (by simp [h])
  have hsuppR : Function.support (fun u : ℂ => ((S u : ℤ) : ℝ)) ⊆
      (hSfin.toFinset : Set ℂ) := by
    intro u hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hu ⊢
    exact fun h => hu (by simp [h])
  rw [finsum_eq_sum_of_support_subset _ hsuppL,
      finsum_eq_sum_of_support_subset _ hsuppR]
  calc ‖∑ u ∈ hSfin.toFinset, ((S u : ℤ) : ℂ) * (1 / (s - u))‖
      ≤ ∑ u ∈ hSfin.toFinset, ‖((S u : ℤ) : ℂ) * (1 / (s - u))‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ hSfin.toFinset, ((S u : ℤ) : ℝ) / δ := Finset.sum_le_sum (fun u _ => hterm u)
    _ = (∑ u ∈ hSfin.toFinset, ((S u : ℤ) : ℝ)) / δ := (Finset.sum_div _ _ _).symm

end Work.LinnikAreas.Zeta1Aux
