import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The `ε`-normalised `ℓ¹`-mass of the smoothing kernel `⟨ε m⟩^{-12}` over `ℤ` is bounded by
`2 ^ 61`, uniformly for `0 < ε ≤ 1`.

The proof splits the `ℤ`-sum into its nonnegative and negative halves
(`tsum_of_nat_of_neg_add_one`), observes that the summand is even
(`jbDecay_neg`), and bounds each half by the Riemann-sum comparison `riemann_shift` at `n = 11`,
`t = 0`. -/
theorem eps_tsum_jbDecay_twelve_int_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ε * ∑' m : ℤ, Work.Analysis.InverseTheory.jbDecay 12 (ε * (m : ℝ)) ≤ (2 : ℝ) ^ 61 := by
  -- Summability of the two `ℕ`-indexed halves.
  have hg : Summable (fun n : ℕ => ε * jbDecay 12 (ε * (n : ℝ))) := by
    simpa using summable_eps_jbDecay_shift (ε := ε) hε0 0
  have hg' : Summable (fun n : ℕ => ε * jbDecay 12 (ε * ((-(n + 1) : ℤ) : ℝ))) := by
    refine (summable_eps_jbDecay_shift (ε := ε) hε0 1).congr (fun n => ?_)
    have hcast : ((↑(-(n + 1) : ℤ) : ℝ)) = -(1 + (n : ℝ)) := by push_cast; ring
    rw [hcast, mul_neg, jbDecay_neg]
  rw [← tsum_mul_left]
  -- Split the `ℤ`-sum into the nonnegative and the negative half.
  have hdec : (∑' (x : ℤ), ε * jbDecay 12 (ε * (x : ℝ)))
      = (∑' n : ℕ, ε * jbDecay 12 (ε * (n : ℝ)))
        + (∑' n : ℕ, ε * jbDecay 12 (ε * ((-(n + 1) : ℤ) : ℝ))) :=
    tsum_of_nat_of_neg_add_one hg hg'
  rw [hdec]
  -- Riemann-sum comparison bounds the nonnegative half by `2 ^ 60`.
  have hg0 : (∑' n : ℕ, ε * jbDecay 12 (ε * (n : ℝ))) ≤ (2 : ℝ) ^ 60 := by
    have hr := riemann_shift 11 (by norm_num) hε0 hε1 (le_refl (0 : ℝ))
    simpa [jbDecay_n_zero] using hr
  -- The negative half is termwise dominated by the nonnegative half, since the summand is even
  -- and decreasing in `|ε m|`.
  have hle : ∀ n : ℕ,
      ε * jbDecay 12 (ε * ((-(n + 1) : ℤ) : ℝ)) ≤ ε * jbDecay 12 (ε * (n : ℝ)) := by
    intro n
    have hcast : ((↑(-(n + 1) : ℤ) : ℝ)) = -(1 + (n : ℝ)) := by push_cast; ring
    rw [hcast, mul_neg, jbDecay_neg]
    refine mul_le_mul_of_nonneg_left ?_ hε0.le
    refine jbDecay_le_of_abs_le ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hn : (n : ℝ) ≤ 1 + (n : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_left hn hε0.le
  have hg2 : (∑' n : ℕ, ε * jbDecay 12 (ε * ((-(n + 1) : ℤ) : ℝ))) ≤ (2 : ℝ) ^ 60 := by
    have h1 : (∑' n : ℕ, ε * jbDecay 12 (ε * ((-(n + 1) : ℤ) : ℝ)))
        ≤ (∑' n : ℕ, ε * jbDecay 12 (ε * (n : ℝ))) :=
      Summable.tsum_le_tsum hle hg' hg
    linarith
  calc (∑' n : ℕ, ε * jbDecay 12 (ε * (n : ℝ)))
        + (∑' n : ℕ, ε * jbDecay 12 (ε * ((-(n + 1) : ℤ) : ℝ)))
      ≤ (2 : ℝ) ^ 60 + (2 : ℝ) ^ 60 := add_le_add hg0 hg2
    _ = (2 : ℝ) ^ 61 := by norm_num

end Work.KMTAreas.A4
