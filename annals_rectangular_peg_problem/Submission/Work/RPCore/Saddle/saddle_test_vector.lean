import Mathlib

/-!
# `Work.RPCore.Saddle.saddle_test_vector`

Given a `lam`-negative-definite operator `A₁` on `EuclideanSpace ℝ (Fin k)`
(`⟪A₁ x, x⟫ ≤ -lam * ‖x‖ ^ 2`) and a `lam`-positive-definite operator `A₂` on
`EuclideanSpace ℝ (Fin l)` (`lam * ‖y‖ ^ 2 ≤ ⟪A₂ y, y⟫`), for every pair
`(v₁, v₂)` there is `w` in the product space with `‖w‖ ≤ 1` such that

`lam * ‖(v₁, v₂)‖ ≤ ⟪A₁ v₁, w.2.1⟫ + ⟪A₂ v₂, w.2.2⟫`.

The proof is elementary duality: the assumption on `A₁` forces
`lam * ‖x‖ ≤ ‖A₁ x‖` (Cauchy–Schwarz against the hypothesis), and similarly
`lam * ‖y‖ ≤ ‖A₂ y‖` for `A₂`.  Taking `x` (resp. `y`) to be the unit vector
in the direction of `A₁ v₁` (resp. `A₂ v₂`) — or `0` when that vector vanishes —
realises `⟪A₁ v₁, x⟫ = ‖A₁ v₁‖` and `⟪A₂ v₂, y⟫ = ‖A₂ v₂‖`, so the right-hand
side is `‖A₁ v₁‖ + ‖A₂ v₂‖ ≥ lam * (‖v₁‖ + ‖v₂‖) ≥ lam * max ‖v₁‖ ‖v₂‖`, and
the product norm is the max norm.
-/

open scoped RealInnerProductSpace

namespace Work.RPCore.Saddle

/-- The Cauchy–Schwarz consequence of `lam`-negative-definiteness:
`lam * ‖x‖ ≤ ‖A x‖`. -/
private lemma norm_smul_le_of_neg {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (lam : ℝ) (_hlam : 0 < lam)
    (hA : ∀ x, inner ℝ (A x) x ≤ -lam * ‖x‖ ^ 2) :
    ∀ x, lam * ‖x‖ ≤ ‖A x‖ := by
  intro x
  have h2 : -inner ℝ (A x) x ≤ ‖A x‖ * ‖x‖ := by
    have h := (abs_le.mp (abs_real_inner_le_norm (A x) x)).1
    linarith
  have h1 : lam * ‖x‖ ^ 2 ≤ ‖A x‖ * ‖x‖ := by linarith [hA x]
  by_cases hx : ‖x‖ = 0
  · rw [hx, mul_zero]; exact norm_nonneg _
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have h3 : (lam * ‖x‖) * ‖x‖ ≤ ‖A x‖ * ‖x‖ := by
      calc (lam * ‖x‖) * ‖x‖ = lam * ‖x‖ ^ 2 := by ring
        _ ≤ ‖A x‖ * ‖x‖ := h1
    exact le_of_mul_le_mul_right h3 hxpos

/-- The Cauchy–Schwarz consequence of `lam`-positive-definiteness:
`lam * ‖y‖ ≤ ‖A y‖`. -/
private lemma norm_le_of_pos {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (lam : ℝ) (_hlam : 0 < lam)
    (hA : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A y) y) :
    ∀ y, lam * ‖y‖ ≤ ‖A y‖ := by
  intro y
  have h2 : inner ℝ (A y) y ≤ ‖A y‖ * ‖y‖ := real_inner_le_norm (A y) y
  have h1 : lam * ‖y‖ ^ 2 ≤ ‖A y‖ * ‖y‖ := le_trans (hA y) h2
  by_cases hy : ‖y‖ = 0
  · rw [hy, mul_zero]; exact norm_nonneg _
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
    have h3 : (lam * ‖y‖) * ‖y‖ ≤ ‖A y‖ * ‖y‖ := by
      calc (lam * ‖y‖) * ‖y‖ = lam * ‖y‖ ^ 2 := by ring
        _ ≤ ‖A y‖ * ‖y‖ := h1
    exact le_of_mul_le_mul_right h3 hypos

/-- Every vector `z` has a vector `x` of norm at most one with `⟪z, x⟫ = ‖z‖`
(namely the unit vector in the direction of `z`, or `0` when `z = 0`). -/
private lemma exists_inner_eq_norm {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    ∃ x, ‖x‖ ≤ 1 ∧ inner ℝ z x = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨0, by simp, by simp [hz]⟩
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    refine ⟨‖z‖⁻¹ • z, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z)]
      field_simp
      norm_num
    · rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp

theorem saddle_test_vector {k l : ℕ}
    (A₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (A₂ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (lam : ℝ) (hlam : 0 < lam)
    (hA₁ : ∀ x, inner ℝ (A₁ x) x ≤ -lam * ‖x‖ ^ 2)
    (hA₂ : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A₂ y) y)
    (v₁ : EuclideanSpace ℝ (Fin k)) (v₂ : EuclideanSpace ℝ (Fin l)) :
    ∃ w : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)),
      ‖w‖ ≤ 1 ∧ lam * ‖(v₁, v₂)‖ ≤ inner ℝ (A₁ v₁) w.2.1 + inner ℝ (A₂ v₂) w.2.2 := by
  obtain ⟨x, hx1, hx2⟩ := exists_inner_eq_norm (A₁ v₁)
  obtain ⟨y, hy1, hy2⟩ := exists_inner_eq_norm (A₂ v₂)
  refine ⟨(0, (x, y)), ?_, ?_⟩
  · rw [Prod.norm_def]
    refine max_le ?_ ?_
    · simp
    · rw [Prod.norm_def]; exact max_le hx1 hy1
  · have hb1 := norm_smul_le_of_neg A₁ lam hlam hA₁ v₁
    have hb2 := norm_le_of_pos A₂ lam hlam hA₂ v₂
    change lam * ‖(v₁, v₂)‖ ≤ inner ℝ (A₁ v₁) x + inner ℝ (A₂ v₂) y
    rw [hx2, hy2, Prod.norm_def]
    have hm : max ‖v₁‖ ‖v₂‖ ≤ ‖v₁‖ + ‖v₂‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    have hmlam : lam * max ‖v₁‖ ‖v₂‖ ≤ lam * (‖v₁‖ + ‖v₂‖) :=
      mul_le_mul_of_nonneg_left hm hlam.le
    linarith [hb1, hb2, hmlam]

end Work.RPCore.Saddle
