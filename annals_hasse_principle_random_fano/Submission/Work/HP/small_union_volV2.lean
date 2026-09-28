import Mathlib
import Submission.Work.HP.ArchGlueV2
import Submission.Work.HP.tau_basic
import Submission.Work.HP.ArchDefs

namespace Work.HP

open MeasureTheory
open scoped ENNReal

theorem small_union_vol (d n : ℕ) {M Kb : ℝ} (hM : 0 < M) (hKb : 0 ≤ Kb)
    (hbvol : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      MeasureTheory.volume (Bset d n lam) ≤ ENNReal.ofReal (Kb * lam ^ 2))
    (hgeom : ∀ (M' σ : ℝ), 0 < M' → 0 < σ →
      (∑' ℓ : ℕ, (if M' / 2 ^ ℓ < σ then ENNReal.ofReal ((M' / 2 ^ ℓ) ^ 2) else 0))
        ≤ ENNReal.ofReal ((4 / 3) * σ ^ 2))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    MeasureTheory.volume (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅))
      ≤ ENNReal.ofReal (Kb * (16 / 3) * σ ^ 2) := by
  -- `2σ` is positive
  have h2σ : (0 : ℝ) < 2 * σ := by linarith
  -- Step 1: countable subadditivity.
  have h1 : MeasureTheory.volume
        (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅))
      ≤ ∑' ℓ : ℕ,
          MeasureTheory.volume (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅) :=
    measure_iUnion_le _
  -- Step 2: termwise use of `hbvol`.
  have h2 : ∑' ℓ : ℕ,
        MeasureTheory.volume (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅)
      ≤ ∑' ℓ : ℕ,
          (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal (Kb * (M / 2 ^ ℓ) ^ 2) else 0) := by
    apply ENNReal.tsum_le_tsum
    intro ℓ
    by_cases h : M / 2 ^ ℓ ≤ σ
    · rw [if_pos h, if_pos h]
      exact hbvol _ (div_pos hM (by positivity)) (le_trans h hσ1)
    · rw [if_neg h, if_neg h]
      simp
  -- Step 3: pull out the constant `Kb`.
  have h3 : ∑' ℓ : ℕ,
        (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal (Kb * (M / 2 ^ ℓ) ^ 2) else 0)
      = ENNReal.ofReal Kb *
          ∑' ℓ : ℕ,
            (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro ℓ
    by_cases h : M / 2 ^ ℓ ≤ σ
    · rw [if_pos h, if_pos h, ENNReal.ofReal_mul hKb]
    · rw [if_neg h, if_neg h, mul_zero]
  -- Step 4: geometric tail bound with the non-strict condition, via `hgeom` at `2σ`.
  have h4 : ∑' ℓ : ℕ,
        (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0)
      ≤ ENNReal.ofReal ((16 / 3) * σ ^ 2) := by
    have hb := hgeom M (2 * σ) hM h2σ
    have hpt : ∀ ℓ : ℕ,
        (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0)
          ≤ (if M / 2 ^ ℓ < 2 * σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0) := by
      intro ℓ
      by_cases h : M / 2 ^ ℓ ≤ σ
      · rw [if_pos h, if_pos (by linarith : M / 2 ^ ℓ < 2 * σ)]
      · rw [if_neg h]
        exact zero_le
    have hconst : (4 / 3 : ℝ) * (2 * σ) ^ 2 = (16 / 3) * σ ^ 2 := by ring
    calc ∑' ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0)
        ≤ ∑' ℓ : ℕ,
            (if M / 2 ^ ℓ < 2 * σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0) :=
          ENNReal.tsum_le_tsum hpt
      _ ≤ ENNReal.ofReal ((4 / 3) * (2 * σ) ^ 2) := hb
      _ = ENNReal.ofReal ((16 / 3) * σ ^ 2) := by rw [hconst]
  -- Step 5: reassemble.
  have h5 : ENNReal.ofReal Kb * ENNReal.ofReal ((16 / 3) * σ ^ 2)
      = ENNReal.ofReal (Kb * (16 / 3) * σ ^ 2) := by
    rw [← ENNReal.ofReal_mul hKb]
    congr 1
    ring
  calc MeasureTheory.volume
          (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅))
      ≤ ∑' ℓ : ℕ,
          MeasureTheory.volume (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅) := h1
    _ ≤ ∑' ℓ : ℕ,
          (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal (Kb * (M / 2 ^ ℓ) ^ 2) else 0) := h2
    _ = ENNReal.ofReal Kb *
          ∑' ℓ : ℕ,
            (if M / 2 ^ ℓ ≤ σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0) := h3
    _ ≤ ENNReal.ofReal Kb * ENNReal.ofReal ((16 / 3) * σ ^ 2) :=
          mul_le_mul_right h4 (ENNReal.ofReal Kb)
    _ = ENNReal.ofReal (Kb * (16 / 3) * σ ^ 2) := h5

end Work.HP
