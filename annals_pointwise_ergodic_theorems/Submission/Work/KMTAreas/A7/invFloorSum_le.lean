import Mathlib
import Submission.Work.KMTAreas.A7.heightScale_rpow_le
import Submission.Work.KMTAreas.A7.invFloor_tail_le
import Submission.Work.KMTAreas.A7.invFloor_tsum_le

/-!
# The reciprocal-sum bound of area A7

This file proves `Work.KMTAreas.A7.invFloorSum_le`: for `C₀ ≥ 1` and a lacunary scale sequence
`a` (with `a n ≥ 1`), the sum of `1 / ⌊a n⌋` over the scales `n` whose height `l_{(⌊a n⌋)}`
exceeds `L` is at most `D · 2^{-2^{L/C₀} + 2}`, with `D` depending only on the lacunarity
parameter `Λ`.

The argument is a three-step comparison.

* `heightScale_rpow_le` (child): `L ≤ C₀ · LogLog N` forces `N ≥ 2^{2^{L/C₀} - 2} =: M`.
* `invFloor_tail_le` (child): summing `1/⌊a n⌋` over the tail `{⌊a n⌋ ≥ M}` (with `M ≥ 2`)
  costs at most `C/M`, because `a` grows geometrically.
* `invFloor_tsum_le` (child): the full sum `∑ₙ 1/⌊a n⌋` is finite (with a bound depending only
  on `Λ`); this covers the range `M < 2`, where `1/M > 1/2` absorbs the constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7

/-- Comparison of two nonnegative series: a pointwise majorant that is summable bounds the
`tsum` from above. -/
private lemma tsum_le_tsum_of_nonneg_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, f n ≤ g n) (hgsum : Summable g) : (∑' n, f n) ≤ ∑' n, g n :=
  Summable.tsum_le_tsum h (Summable.of_nonneg_of_le hf h hgsum) hgsum

theorem invFloorSum_le (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0))
        ≤ D * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
  obtain ⟨Ct, hCt0, htail⟩ := invFloor_tail_le Λ hΛ
  obtain ⟨CT, hCT0, htot⟩ := invFloor_tsum_le Λ hΛ
  refine ⟨max Ct (2 * CT), le_trans hCt0 (le_max_left _ _), fun L hL a ha ha1 => ?_⟩
  -- the threshold `M = 2^{2^{L/C₀} - 2}` implied by the height condition
  set M : ℝ := (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) - 2) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  -- `2^{-2^{L/C₀} + 2} = M⁻¹`
  have hrhs : (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) = M⁻¹ := by
    have h2 : -((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2
        = -((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) - 2) := by ring
    rw [hMdef, h2, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hrhs]
  have hfn : ∀ n, 0 ≤ (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
      then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0) := by
    intro n
    by_cases hc : L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
    · rw [if_pos hc]; exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · rw [if_neg hc]
  -- the height condition pushes the scale above `M`
  have hcmpM : ∀ n, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0)
      ≤ (if M ≤ ((Nat.floor (a n) : ℕ) : ℝ)
        then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0) := by
    intro n
    by_cases hc : L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
    · have hN : 1 ≤ Nat.floor (a n) := Nat.le_floor (by simpa using ha1 n)
      have hMle : M ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by
        rw [hMdef]; exact heightScale_rpow_le hC₀ hL hN hc
      rw [if_pos hc, if_pos hMle]
    · rw [if_neg hc]
      by_cases hM : M ≤ ((Nat.floor (a n) : ℕ) : ℝ)
      · rw [if_pos hM]; exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · rw [if_neg hM]
  have hcmpT : ∀ n, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0) ≤ (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ := by
    intro n
    by_cases hc : L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
    · rw [if_pos hc]
    · rw [if_neg hc]; exact inv_nonneg.mpr (Nat.cast_nonneg _)
  by_cases hM2 : 2 ≤ M
  · -- large threshold: use the geometric tail bound
    obtain ⟨hgsum, hgle⟩ := htail M hM2 a ha ha1
    calc (∑' n : ℕ, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
            then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0))
        ≤ (∑' n : ℕ, (if M ≤ ((Nat.floor (a n) : ℕ) : ℝ)
            then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0)) :=
          tsum_le_tsum_of_nonneg_le hfn hcmpM hgsum
      _ ≤ Ct / M := hgle
      _ = Ct * M⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ max Ct (2 * CT) * M⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hMpos.le)
  · -- small threshold: `1/M > 1/2` absorbs the crude total bound
    have hMlt : M < 2 := not_le.mp hM2
    obtain ⟨hhsum, hhle⟩ := htot a ha ha1
    have h1 : (∑' n : ℕ, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
            then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0))
        ≤ ∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ :=
      tsum_le_tsum_of_nonneg_le hfn hcmpT hhsum
    have h2CT : 0 ≤ 2 * CT := by linarith
    have hhalf : (2 : ℝ)⁻¹ ≤ M⁻¹ := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hMpos).mpr hMlt.le
    have h2 : (∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ≤ max Ct (2 * CT) * M⁻¹ := by
      refine le_trans hhle ?_
      calc CT = 2 * CT * (2 : ℝ)⁻¹ := by ring
        _ ≤ 2 * CT * M⁻¹ := mul_le_mul_of_nonneg_left hhalf h2CT
        _ ≤ max Ct (2 * CT) * M⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr hMpos.le)
    exact le_trans h1 h2

end Work.KMTAreas.A7
