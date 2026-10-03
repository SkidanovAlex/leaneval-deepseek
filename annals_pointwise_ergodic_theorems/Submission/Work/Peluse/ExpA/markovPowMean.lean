import Mathlib

/-!
# The Markov / power-mean step of the short expansion (`ExpansionPETShortA`)

For a non-negative function `x` on a finite non-empty type with values `≤ 1`, a level `η ≥ 0` whose
level set carries all but half of the mass and a threshold `t ≤ 2η` below the mean of `x`, the
`2p`-th power of `t/2` is bounded by the `2p`-th power average of `x` over its level set:

`(t/2)^{2p} ≤ (card)⁻¹ ∑_{i : η ≤ x i} (x i)^{2p}`.

The proof is the two elementary steps

* the mass of the level set `A = {i : η ≤ x i}` is at least `card · t/2`:  the complement of `A` has
  `x i < η ≤ t/2` pointwise, so its mass is at most `card · t/2` while the total mass is `≥ card · t`;
* the power mean (Jensen for the convex function `z ↦ z^{2p}`) applied over the whole (non-empty)
  index type to the truncation `y i = if η ≤ x i then x i else 0`, with the uniform weights
  `(card)⁻¹`:  `(card⁻¹ ∑ y)^{2p} ≤ card⁻¹ ∑ y^{2p}`.

Combining, `(t/2)^{2p} ≤ (card⁻¹ ∑_{A} x)^{2p} ≤ card⁻¹ ∑_{A} x^{2p}`.
-/

open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.Peluse.ExpA

theorem markovPowMean {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℝ}
    {η t : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) (hη : 0 ≤ η) (hηt : η ≤ t / 2)
    (ht : t ≤ (((Finset.univ : Finset ι).card : ℕ) : ℝ)⁻¹ * ∑ i, x i) :
    t ^ (2 * p) / 2 ^ (2 * p) ≤ (((Finset.univ : Finset ι).card : ℕ) : ℝ)⁻¹ *
      ∑ i ∈ Finset.univ.filter (fun i => η ≤ x i), (x i) ^ (2 * p) := by
  set C : ℝ := (((Finset.univ : Finset ι).card : ℕ) : ℝ) with hC
  set A : Finset ι := Finset.univ.filter (fun i => η ≤ x i) with hA
  set Ā : Finset ι := Finset.univ.filter (fun i => ¬ η ≤ x i) with hĀ
  have hCpos : 0 < C := by
    rw [hC]
    exact_mod_cast Finset.card_pos.mpr Finset.univ_nonempty
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have ht0 : 0 ≤ t := by linarith
  -- The total mass dominates `C · t`.
  have ht' : C * t ≤ ∑ i, x i := by
    have h := mul_le_mul_of_nonneg_left ht hCpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hCne, one_mul] at h
    exact h
  have hsplit : (∑ i ∈ A, x i) + ∑ i ∈ Ā, x i = ∑ i, x i := by
    rw [hA, hĀ]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => η ≤ x i) x
  -- Off the level set `x < η`, so the mass there is at most `C · η`.
  have hcomp_le : ∑ i ∈ Ā, x i ≤ C * η := by
    have h1 : ∑ i ∈ Ā, x i ≤ ∑ i ∈ Ā, η := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hi' : ¬ η ≤ x i := (Finset.mem_filter.mp hi).2
      linarith
    have h2 : ∑ i ∈ Ā, η = (Ā.card : ℝ) * η := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (Ā.card : ℝ) ≤ C := by
      rw [hC]
      exact_mod_cast Finset.card_filter_le (Finset.univ : Finset ι) (fun i => ¬ η ≤ x i)
    calc ∑ i ∈ Ā, x i ≤ ∑ i ∈ Ā, η := h1
      _ = (Ā.card : ℝ) * η := h2
      _ ≤ C * η := mul_le_mul_of_nonneg_right h3 hη
  -- Hence the mass of the level set is at least `C · t/2`.
  have hS : C * t / 2 ≤ ∑ i ∈ A, x i := by
    have hCeta : C * η ≤ C * (t / 2) := mul_le_mul_of_nonneg_left hηt hCpos.le
    linarith
  -- The truncation of `x` to the level set.
  set y : ι → ℝ := (fun i => if η ≤ x i then x i else 0) with hy
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i
    by_cases h : η ≤ x i
    · simp [hy, h, hx0 i]
    · simp [hy, h]
  have hyS : ∑ i, y i = ∑ i ∈ A, x i := by
    rw [hA, Finset.sum_filter]
  have hyT : ∑ i, (y i) ^ (2 * p) = ∑ i ∈ A, (x i) ^ (2 * p) := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : η ≤ x i
    · simp [hy, h]
    · simp [hy, h, zero_pow (by omega : 2 * p ≠ 0)]
  -- The power mean over the whole index type, with the uniform weights `C⁻¹`.
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun z : ℝ => z ^ (2 * p)) := convexOn_pow (2 * p)
  have hw : ∀ i ∈ (Finset.univ : Finset ι), (0 : ℝ) ≤ C⁻¹ := fun i _ => by positivity
  have hsumw : ∑ i ∈ (Finset.univ : Finset ι), C⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hCeq : ((Fintype.card ι : ℕ) : ℝ) = C := by rw [hC, Finset.card_univ]
    rw [hCeq, mul_inv_cancel₀ hCne]
  have hjen := hconv.map_sum_le hw hsumw (fun i _ => Set.mem_Ici.mpr (hy0 i))
  have h1 : ∑ i ∈ (Finset.univ : Finset ι), C⁻¹ • y i = C⁻¹ * ∑ i ∈ A, x i := by
    rw [← hyS, Finset.mul_sum]
    simp [smul_eq_mul]
  have h2 : ∑ i ∈ (Finset.univ : Finset ι), C⁻¹ • (y i) ^ (2 * p)
      = C⁻¹ * ∑ i ∈ A, (x i) ^ (2 * p) := by
    rw [← hyT, Finset.mul_sum]
    simp [smul_eq_mul]
  have hmain : (C⁻¹ * ∑ i ∈ A, x i) ^ (2 * p) ≤ C⁻¹ * ∑ i ∈ A, (x i) ^ (2 * p) := by
    rw [h1, h2] at hjen
    exact hjen
  have hle : t / 2 ≤ C⁻¹ * ∑ i ∈ A, x i := by
    have h := mul_le_mul_of_nonneg_left hS (le_of_lt (inv_pos.mpr hCpos))
    have hCt : C⁻¹ * (C * t / 2) = t / 2 := by field_simp
    rwa [hCt] at h
  calc t ^ (2 * p) / 2 ^ (2 * p) = (t / 2) ^ (2 * p) := (div_pow t 2 (2 * p)).symm
    _ ≤ (C⁻¹ * ∑ i ∈ A, x i) ^ (2 * p) := pow_le_pow_left₀ (by linarith) hle _
    _ ≤ C⁻¹ * ∑ i ∈ A, (x i) ^ (2 * p) := hmain

end Work.Peluse.ExpA
