import Mathlib
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le
import Submission.Work.BourgainPlan.Maximal.mst_level_defs

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **The cardinality of the MST level set `𝒰(n) = mstU l n` is `≲ exp((n^l)^{1/(10 l)})`**, uniformly
in `n`.  Here `mstU l n = iwSigma (mstRho l) (n^l) = sigmaLeFinset (taoSetS ρ (n^l)) (⌊2/ρ⌋₊ + 1)` is
Tao's Ionescu–Wainger superset at the scale `N = n^l`, with `ρ = mstRho l = 1/(10 l)`.

Route: `sigmaN_card_le (mstRho l) hρ` gives `∃ N₁, ∀ N ≥ N₁, |iwSigma ρ N| ≤ ⌈exp (N^ρ)⌉`; at
`N = n^l` this bounds `(mstU l n).card` by `⌈exp ((n^l)^ρ)⌉ ≤ 2 exp ((n^l)^ρ)` (the exponential is
`≥ 1`).  Since `mstRho l > 0` for `l ≥ 1`, `exp ((n^l)^ρ) ≥ 1`, so the finitely many `n` with
`n^l < N₁` (a subset of `n ≤ N₁`) are absorbed by taking `C ≥ max_{n ≤ N₁} (mstU l n).card`
(e.g. via `Finset.sup (Finset.range (N₁+1)) (fun n => (mstU l n).card)`), giving a single constant
`C > 0` that works for every `n`. -/
theorem mstU_card_le_exp (l : ℕ) (hl : 1 ≤ l) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ((mstU l n).card : ℝ) ≤ C * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hρ : 0 < mstRho l := by unfold mstRho; positivity
  obtain ⟨N₁, hN₁⟩ := sigmaN_card_le (mstRho l) hρ
  refine ⟨max 2 (((Finset.range (N₁ + 1)).sup (fun m => (mstU l m).card) : ℕ) : ℝ), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro n
    have hexp1 : 1 ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) :=
      Real.one_le_exp (Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg n) l) _)
    by_cases hbig : N₁ ≤ n ^ l
    · -- the large case: apply `sigmaN_card_le` at `N = n^l`
      have hcard : (mstU l n).card ≤ ⌈Real.exp (((n : ℝ) ^ l) ^ (mstRho l))⌉₊ := by
        simpa only [mstU, iwSigma, iwK, Nat.cast_pow] using hN₁ (n ^ l) hbig
      have hceil : ((⌈Real.exp (((n : ℝ) ^ l) ^ (mstRho l))⌉₊ : ℕ) : ℝ)
          ≤ 2 * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
        have h := Nat.ceil_lt_add_one (Real.exp_nonneg (((n : ℝ) ^ l) ^ (mstRho l)))
        linarith
      calc ((mstU l n).card : ℝ)
          ≤ ((⌈Real.exp (((n : ℝ) ^ l) ^ (mstRho l))⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ 2 * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := hceil
        _ ≤ max 2 (((Finset.range (N₁ + 1)).sup (fun m => (mstU l m).card) : ℕ) : ℝ)
              * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    · -- the small case: `n ≤ N₁`, absorbed by the finite maximum
      have hnle : n ≤ N₁ := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · omega
        · have h1 : n ^ 1 ≤ n ^ l := Nat.pow_le_pow_right hpos hl
          have h2 : n < N₁ := by simpa using lt_of_le_of_lt h1 (not_le.mp hbig)
          omega
      have hmem : n ∈ Finset.range (N₁ + 1) := Finset.mem_range.mpr (by omega)
      have hsup : ((mstU l n).card : ℝ)
          ≤ (((Finset.range (N₁ + 1)).sup (fun m => (mstU l m).card) : ℕ) : ℝ) := by
        exact_mod_cast Finset.le_sup (f := fun m => (mstU l m).card) hmem
      calc ((mstU l n).card : ℝ)
          ≤ max 2 (((Finset.range (N₁ + 1)).sup (fun m => (mstU l m).card) : ℕ) : ℝ) :=
            hsup.trans (le_max_right _ _)
        _ = max 2 (((Finset.range (N₁ + 1)).sup (fun m => (mstU l m).card) : ℕ) : ℝ) * 1 :=
            (mul_one _).symm
        _ ≤ max 2 (((Finset.range (N₁ + 1)).sup (fun m => (mstU l m).card) : ℕ) : ℝ)
              * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) :=
            mul_le_mul_of_nonneg_left hexp1 (le_trans (by norm_num) (le_max_left _ _))

end Work.BourgainPlan.Maximal
