import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_resonant_high
import Submission.Work.GM.Affine.card_mul_pairs_le
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.window_integral_Bsum
import Submission.Work.GM.Affine.finset_sum_window_le_WinMass
import Submission.Work.GM.Affine.tsum_resonance_eq_finsum
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.sup_copy_far

/-!
# GM §9, region II, far part, relaxed third scale `M₃ ≤ C₃ Mbig`

This file proves `Work.GM.Affine.region_II_far_C3_c`, the far half of the region-II reduction with
the third scale relaxed to `M₃ ≤ C₃ Mbig`, in the *bare `Λ`-form* of the Fourier-decay
hypothesis (no explicit `supf f ≤ Λ`).

## The point

Earlier sessions recorded the `Λ`-form as "defective" (see `NOTES_T1_BOUND_defect.md`) on the
grounds that a narrow needle `f` with small `Λ` would be admissible with `supf f ≫ Λ`.  That
diagnosis is wrong: the `Λ`-form decay hypothesis *together with* the compatibility
`Λ ≤ 16 c(2,1) T³ ∫ f` already forces

  `supf f ≤ 16 * c 2 1 * T ^ 3 * ∫ f`     (`supf_le_sixteen_of_lambda_decay_c` below),

so the "extra" hypothesis `supf f ≤ Λ` of the proved `supf`-form
`Work.GM.Affine.regionII_far_C3_sup_c` is *free*: one simply applies the `supf`-form with
`Λ̃ := max Λ (supf f)`, for which

* `supf f ≤ Λ̃` is `le_max_right`,
* `Λ̃ ≤ 16 c 2 1 T³ ∫ f` is `max_le` of the given compatibility and the new bound,
* the decay hypothesis with `Λ̃` follows from the one with `Λ` by monotonicity (every
  `c j ε` is non-negative — forced by the decay hypothesis itself at `ξ = 1`).

## The bound `supf f ≤ 16 c(2,1) T³ ∫ f`

Let `M = supf f`, `A = ∫ f` and write `c' j ε := c j ε * (Λ/M)`.  Then `DecayHyp c' T f` *is*
the given `Λ`-form hypothesis (the factor `M` cancels), so `supf_le_of_decay` (which needs only
`0 ≤ c' 2 1`) gives

  `M ≤ 16 * c' 2 1 * T * T² * A = 16 c(2,1) Λ T³ A / M`,   hence   `M² ≤ 16 c(2,1) Λ T³ A`.

By the compatibility `Λ ≤ 16 c(2,1) T³ A` and `c(2,1) ≥ 0` the right side is at most
`(16 c(2,1) T³ A)²`, so `M ≤ 16 c(2,1) T³ A`.  (This is the same "balance the two tails of
`∫ ‖F̂f‖` at `|ξ| ≍ T`" argument that yields the paper's crude bound `sup f ⪅ T²`.)

Hence the whole region-II far estimate `regionII_far_C3` follows from the already proved
`supf`-form `regionII_far_C3_sup_c` by a change of `Λ`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- **The `Λ`-form decay hypothesis controls `supf f`.**  For a continuous, non-negative,
compactly supported `f` satisfying the `Λ`-form decay hypothesis of GM §9 together with the
compatibility `Λ ≤ 16 c(2,1) T³ ∫ f`, the supremum of `f` obeys the *same* bound
`supf f ≤ 16 c(2,1) T³ ∫ f`. -/
theorem supf_le_sixteen_of_lambda_decay_c {c : ℕ → ℝ → ℝ} {T Λ : ℝ} {f : ℝ → ℝ}
    (hT : 1 ≤ T) (hΛ : 0 < Λ) (hf : Continuous f) (hcs : HasCompactSupport f)
    (hnn : ∀ u, 0 ≤ f u)
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (hcompat : Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u) :
    supf f ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hAnn : (0 : ℝ) ≤ ∫ u, f u := integral_nonneg hnn
  -- the decay hypothesis itself forces `0 ≤ c 2 1`
  have hc21 : 0 ≤ c 2 1 := by
    have h1 := hdec 2 1 one_pos (1 : ℝ) one_ne_zero
    rw [Real.rpow_one, abs_one, div_one] at h1
    -- `h1 : ‖Fhat f 1‖ ≤ c 2 1 * T * T ^ 2 * Λ`
    have h2 : (0 : ℝ) ≤ c 2 1 * T * T ^ 2 * Λ := le_trans (norm_nonneg _) h1
    have hpos : (0 : ℝ) < T * T ^ 2 * Λ := mul_pos (mul_pos hTpos (pow_pos hTpos 2)) hΛ
    have hden : c 2 1 = (c 2 1 * T * T ^ 2 * Λ) / (T * T ^ 2 * Λ) := by field_simp
    rw [hden]
    exact div_nonneg h2 hpos.le
  by_cases hM0 : supf f = 0
  · -- `supf f = 0` forces `f ≡ 0`, contradicting `Λ > 0` and the compatibility
    exfalso
    have hf0 : ∀ u, f u = 0 := fun u => le_antisymm (hM0 ▸ le_supf hf hcs u) (hnn u)
    have hA0 : (∫ u, f u) = 0 := by simp [hf0]
    rw [hA0] at hcompat
    simp only [mul_zero] at hcompat
    linarith
  · have hMpos : 0 < supf f := lt_of_le_of_ne (supf_nonneg hf hcs hnn) (Ne.symm hM0)
    -- the `supf`-form decay hypothesis with the constant `c j ε * (Λ / supf f)`
    have hdec' : DecayHyp (fun j ε => c j ε * (Λ / supf f)) T f := by
      intro j ε hε ξ hξ
      have h := hdec j ε hε ξ hξ
      have hMne : supf f ≠ 0 := ne_of_gt hMpos
      calc ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ := h
        _ = (c j ε * (Λ / supf f)) * T ^ ε * (T / |ξ|) ^ j * supf f := by
            field_simp
    have hc' : 0 ≤ (fun j ε => c j ε * (Λ / supf f)) 2 1 :=
      mul_nonneg hc21 (div_nonneg hΛ.le hMpos.le)
    have hmain := supf_le_of_decay (c := fun j ε => c j ε * (Λ / supf f)) (T := T)
      (f := f) (ε := 1) hf hcs hnn hdec' one_pos hc'
    -- `supf f ≤ 16 * (c 2 1 * (Λ / supf f)) * T³ * ∫ f`
    have hM1 : supf f ≤ 16 * (c 2 1 * (Λ / supf f)) * T ^ 3 * ∫ u, f u := by
      have h := hmain
      rw [Real.rpow_one] at h
      convert h using 2
      ring
    -- multiply by `supf f > 0`
    have hM2 : supf f * supf f ≤ 16 * c 2 1 * Λ * T ^ 3 * (∫ u, f u) := by
      have h := mul_le_mul_of_nonneg_right hM1 hMpos.le
      have heq : (16 * (c 2 1 * (Λ / supf f)) * T ^ 3 * (∫ u, f u)) * supf f
          = 16 * c 2 1 * Λ * T ^ 3 * (∫ u, f u) := by
        field_simp
      rwa [heq] at h
    have hXnn : 0 ≤ 16 * c 2 1 * T ^ 3 * (∫ u, f u) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc21) (pow_nonneg hTpos.le 3)) hAnn
    have hsqM : supf f ^ 2 ≤ (16 * c 2 1 * T ^ 3 * (∫ u, f u)) ^ 2 := by
      have hsq : supf f ^ 2 = supf f * supf f := by ring
      rw [hsq]
      calc supf f * supf f ≤ 16 * c 2 1 * Λ * T ^ 3 * (∫ u, f u) := hM2
        _ ≤ 16 * c 2 1 * (16 * c 2 1 * T ^ 3 * (∫ u, f u)) * T ^ 3 * (∫ u, f u) := by
            have h := mul_le_mul_of_nonneg_right hcompat hXnn
            have hY : (16 * c 2 1 * T ^ 3 * (∫ u, f u))
                * (16 * c 2 1 * T ^ 3 * (∫ u, f u))
                = 16 * c 2 1 * (16 * c 2 1 * T ^ 3 * (∫ u, f u)) * T ^ 3 * (∫ u, f u) := by
              ring
            calc 16 * c 2 1 * Λ * T ^ 3 * (∫ u, f u)
                = Λ * (16 * c 2 1 * T ^ 3 * (∫ u, f u)) := by ring
              _ ≤ (16 * c 2 1 * T ^ 3 * (∫ u, f u)) * (16 * c 2 1 * T ^ 3 * (∫ u, f u)) := h
              _ = 16 * c 2 1 * (16 * c 2 1 * T ^ 3 * (∫ u, f u)) * T ^ 3 * (∫ u, f u) := hY
        _ = (16 * c 2 1 * T ^ 3 * (∫ u, f u)) ^ 2 := by ring
    have hsqle := sq_le_sq.mp hsqM
    rw [abs_of_nonneg hMpos.le, abs_of_nonneg hXnn] at hsqle
    exact hsqle

/-- **GM §9, region II, far half, third scale `M₃ ≤ C₃ Mbig` (bare `Λ`-form).** -/
theorem region_II_far_C3_c {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨C', hC'pos, hmain⟩ := regionII_far_C3_sup_c hC₀ hK hT₀ hC₃ c δ hδ
  refine ⟨C', hC'pos, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hcs : HasCompactSupport f := hcs_of_SuppHyp hsupp
  -- the `Λ`-form hypothesis forces the `supf` bound
  have hsupf16 : supf f ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u :=
    supf_le_sixteen_of_lambda_decay_c hT1 hΛ hf hcs hfnn hdec hcompat
  -- apply the `supf`-form at `Λ̃ = max Λ (supf f)`
  refine hmain T hT f hf hfnn hsupp (max Λ (supf f))
    (lt_of_lt_of_le hΛ (le_max_left Λ (supf f))) ?_ (le_max_right Λ (supf f))
    (max_le hcompat hsupf16) Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  -- the decay hypothesis transfers to the larger scale `max Λ (supf f)`
  intro j ε hε ξ hξ
  have hcj : 0 ≤ c j ε := by
    have h1 := hdec j ε hε (1 : ℝ) one_ne_zero
    rw [abs_one, div_one] at h1
    -- `h1 : ‖Fhat f 1‖ ≤ c j ε * T ^ ε * T ^ j * Λ`
    have h2 : (0 : ℝ) ≤ c j ε * T ^ ε * T ^ j * Λ := le_trans (norm_nonneg _) h1
    have hpos : (0 : ℝ) < T ^ ε * T ^ j * Λ :=
      mul_pos (mul_pos (Real.rpow_pos_of_pos hTpos ε) (pow_pos hTpos j)) hΛ
    have hden : c j ε
        = (c j ε * T ^ ε * T ^ j * Λ) / (T ^ ε * T ^ j * Λ) := by field_simp
    rw [hden]
    exact div_nonneg h2 hpos.le
  have hfac : (0 : ℝ) ≤ c j ε * T ^ ε * (T / |ξ|) ^ j :=
    mul_nonneg (mul_nonneg hcj (Real.rpow_nonneg hTpos.le ε))
      (pow_nonneg (div_nonneg hTpos.le (abs_nonneg ξ)) j)
  calc ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ := hdec j ε hε ξ hξ
    _ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * max Λ (supf f) :=
        mul_le_mul_of_nonneg_left (le_max_left Λ (supf f)) hfac

end

end Work.GM.Affine
