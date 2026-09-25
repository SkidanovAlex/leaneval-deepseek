import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- For a nonnegative real `s`, the norm of the complex inverse `(s : ℂ)⁻¹` is `s⁻¹`. -/
private lemma norm_inv_ofReal (s : ℝ) (hs : 0 ≤ s) : ‖((s : ℂ))⁻¹‖ = s⁻¹ := by
  rw [norm_inv, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs, abs_of_nonneg hs]

/-- For a complex `z`, `conj z * z = ‖z‖²` (as a complex number). -/
private lemma star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show star z = (starRingEnd ℂ) z from rfl, RCLike.conj_mul]
  exact (Complex.ofReal_pow ‖z‖ 2).symm

/-- `z ^ 2 * z⁻¹ = z`, with the convention `0⁻¹ = 0`. -/
private lemma sq_mul_inv (z : ℂ) : z ^ 2 * z⁻¹ = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [sq, mul_assoc, mul_inv_cancel₀ hz, mul_one]

/-- `‖z * (t : ℂ)⁻¹‖² = ‖z‖² * (t⁻¹)²` for a nonnegative real `t`. -/
private lemma norm_mul_inv_sq (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖z * ((t : ℂ))⁻¹‖ ^ 2 = ‖z‖ ^ 2 * (t⁻¹) ^ 2 := by
  rw [norm_mul, mul_pow, norm_inv_ofReal t ht]

/-- `s ^ 2 * (s⁻¹) ^ 2 ≤ 1` for every real `s`. -/
private lemma sq_mul_sq_inv_le_one (s : ℝ) : s ^ 2 * (s⁻¹) ^ 2 ≤ (1 : ℝ) := by
  rw [← mul_pow]
  by_cases h : s = 0
  · simp [h]
  · rw [mul_inv_cancel₀ h]; norm_num

/-- **Dual unit field lemma.** Given a finite family of vectors `v x : ι → ℂ`, there is a field
`u x : ι → ℂ` of `ℓ²`-norm at most one with `∑ i, u x i * v x i = ‖v x‖₂` for every `x`. The
witness is `u x i = conj (v x i) / ‖v x‖₂`. -/
theorem dual_unit_field_sqrt {α ι : Type*} [Fintype α] [Fintype ι] (v : α → ι → ℂ) :
    ∃ u : α → ι → ℂ,
      (∀ x, (∑ i, ‖u x i‖ ^ (2:ℝ)) ≤ 1) ∧
      ∀ x, (∑ i, u x i * v x i) = ((Real.sqrt (∑ i, ‖v x i‖ ^ (2:ℝ)) : ℝ) : ℂ) := by
  refine ⟨fun x i => star (v x i) * ((Real.sqrt (∑ i, ‖v x i‖ ^ (2:ℝ)) : ℝ) : ℂ)⁻¹, ?_, ?_⟩
  · intro x
    simp only [Real.rpow_two]
    have ht : (0 : ℝ) ≤ ∑ i, ‖v x i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hs : (Real.sqrt (∑ i, ‖v x i‖ ^ 2)) ^ 2 = ∑ i, ‖v x i‖ ^ 2 := Real.sq_sqrt ht
    have hsnn : (0 : ℝ) ≤ Real.sqrt (∑ i, ‖v x i‖ ^ 2) := Real.sqrt_nonneg _
    calc ∑ i, ‖star (v x i) * ((Real.sqrt (∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ)⁻¹‖ ^ 2
        = ∑ i, ‖v x i‖ ^ 2 * ((Real.sqrt (∑ i, ‖v x i‖ ^ 2))⁻¹) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by
            rw [norm_mul_inv_sq (star (v x i)) _ hsnn, norm_star])
      _ = (∑ i, ‖v x i‖ ^ 2) * ((Real.sqrt (∑ i, ‖v x i‖ ^ 2))⁻¹) ^ 2 := by
          rw [Finset.sum_mul]
      _ = (Real.sqrt (∑ i, ‖v x i‖ ^ 2)) ^ 2
            * ((Real.sqrt (∑ i, ‖v x i‖ ^ 2))⁻¹) ^ 2 := by
          nth_rewrite 1 [← hs]
          rfl
      _ ≤ 1 := sq_mul_sq_inv_le_one _
  · intro x
    simp only [Real.rpow_two]
    have ht : (0 : ℝ) ≤ ∑ i, ‖v x i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hs : (Real.sqrt (∑ i, ‖v x i‖ ^ 2)) ^ 2 = ∑ i, ‖v x i‖ ^ 2 := Real.sq_sqrt ht
    have hsum : ∑ i, star (v x i) * v x i = (((∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun i _ => star_mul_self (v x i))
    have hcast : (((∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ)
        = ((Real.sqrt (∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hs]
    calc ∑ i, (star (v x i) * ((Real.sqrt (∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ)⁻¹) * v x i
        = (∑ i, star (v x i) * v x i)
            * ((Real.sqrt (∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ)⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = (((∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ)
            * ((Real.sqrt (∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ)⁻¹ := by
          rw [hsum]
      _ = ((Real.sqrt (∑ i, ‖v x i‖ ^ 2) : ℝ) : ℂ) := by
          rw [hcast]
          exact sq_mul_inv _

end Work.BourgainPlan.IonescuWainger
