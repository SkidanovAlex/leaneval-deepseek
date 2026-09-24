import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.psi1hat_decay

namespace Work.GM.Affine

/-- **Finiteness of the resonance sum.**  The resonance weight
`W(x) = M₃ Σ_ℓ ψ̂₁(M₃(ℓ - x))` against which the region-II argument is summed has, for
`|x| ≤ L - 2`, all its terms with `ℓ ∉ [-L, L]` equal to zero: if `|ℓ| ≥ L + 1` then
`|ℓ - x| ≥ |ℓ| - |x| ≥ 3 > 2 ≥ 2/M₃`, so the indicator `|ℓ - x| ≤ 2/M₃` cuts those `ℓ` out.
Hence the (a priori infinite) sum over `ℤ` is the finite sum over `Icc (-L) L`. -/
theorem tsum_resonance_eq_finsum {K M₃ x : ℝ} {L : ℤ} (hM₃ : 1 ≤ M₃) (hx : |x| ≤ (L:ℝ) - 2) :
    (∑' ℓ : ℤ, if |(ℓ:ℝ) - x| ≤ 2/M₃ then psi1hat K (M₃*((ℓ:ℝ) - x)) else 0)
      = ∑ ℓ ∈ Finset.Icc (-L) L,
          (if |(ℓ:ℝ) - x| ≤ 2/M₃ then psi1hat K (M₃*((ℓ:ℝ) - x)) else 0) := by
  refine tsum_eq_sum (fun ℓ hℓ => ?_)
  have hM3pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have h2M3 : 2/M₃ ≤ 2 := by rw [div_le_iff₀ hM3pos]; linarith
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hℓ
  -- Any `ℓ ∉ [-L, L]` is at distance `> 2/M₃` from `x`.
  have hge3 : 2/M₃ < |(ℓ:ℝ) - x| := by
    have h3 : (3:ℝ) ≤ |(ℓ:ℝ) - x| := by
      rcases hℓ with h | h
      · -- `ℓ < -L`, hence `ℓ ≤ -L - 1` and `x - ℓ ≥ 3`
        have h1 : (ℓ:ℝ) ≤ -(L:ℝ) - 1 := by
          have h2 : ℓ ≤ -L - 1 := by omega
          have h3 : ((ℓ : ℤ) : ℝ) ≤ ((-L - 1 : ℤ) : ℝ) := by exact_mod_cast h2
          push_cast at h3; linarith
        rw [abs_sub_comm]
        have : (3:ℝ) ≤ x - (ℓ:ℝ) := by linarith [neg_abs_le x]
        exact this.trans (le_abs_self _)
      · -- `L < ℓ`, hence `L + 1 ≤ ℓ` and `ℓ - x ≥ 3`
        have h1 : (L:ℝ) + 1 ≤ (ℓ:ℝ) := by
          have h2 : L + 1 ≤ ℓ := by omega
          have h3 : ((L + 1 : ℤ) : ℝ) ≤ ((ℓ : ℤ) : ℝ) := by exact_mod_cast h2
          push_cast at h3; linarith
        have : (3:ℝ) ≤ (ℓ:ℝ) - x := by linarith [le_abs_self x]
        exact this.trans (le_abs_self _)
    linarith
  rw [if_neg (not_le.mpr hge3)]

end Work.GM.Affine
