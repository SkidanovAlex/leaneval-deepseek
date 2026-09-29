import Mathlib
import Submission.Work.Resample.sliceB1defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

/-- The retained window `egHset m = {h | 0 < |h| ≤ m}` has `2m` elements. -/
lemma bu_card_egHset (m : ℕ) : (egHset m).card = 2 * m := by
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> [exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le m);
      exact_mod_cast Nat.zero_le m]
  rw [egHset, Finset.card_erase_of_mem hmem, Int.card_Icc]
  have hcast : ((m : ℤ) + 1 - (-(m : ℤ))).toNat = 2 * m + 1 := by
    have h : (m : ℤ) + 1 - (-(m : ℤ)) = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  rw [hcast]; omega

/-- Weight error bound: if the integer weights `Wt ℓ h` differ from the true real weights
`egW s t α ℓ h` by at most `δ / 2^p` (after scaling by `2^{-p}`) on the retained window
`h ∈ egHset m`, then the corresponding convolution term, applied to any vector `u` with
`‖u‖ ≤ 1`, has operator norm at most `2 m δ / 2^p`. -/
theorem buWeightErr (p m s t α : ℕ) (Wt : ℤ → ℤ → ℤ) (δ : ℝ) (ℓ : Fin s) (hs : 0 < s) (u : Fin s → ℂ)
    (hδ0 : 0 ≤ δ)
    (hWt : ∀ h : ℤ, h ∈ Work.Resample.egHset m →
      |((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - Work.Resample.egW s t α ℓ h)| ≤ δ / (2 : ℝ) ^ p)
    (hu : ∀ j, ‖u j‖ ≤ 1) :
    ‖∑ h ∈ Work.Resample.egHset m,
      ((((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - Work.Resample.egW s t α ℓ h : ℝ)) : ℂ)
        * u (Work.Resample.egIdx s hs ((ℓ : ℤ) + h))‖ ≤ 2 * (m : ℝ) * δ / (2 : ℝ) ^ p := by
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hcard : (((egHset m).card : ℕ) : ℝ) = 2 * (m : ℝ) := by
    rw [bu_card_egHset]; push_cast; ring
  have hδp : 0 ≤ δ / (2 : ℝ) ^ p := div_nonneg hδ0 h2p.le
  calc ‖∑ h ∈ egHset m,
        ((((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h : ℝ)) : ℂ)
          * u (egIdx s hs ((ℓ : ℤ) + h))‖
      ≤ ∑ h ∈ egHset m,
          ‖((((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h : ℝ)) : ℂ)
            * u (egIdx s hs ((ℓ : ℤ) + h))‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ egHset m, δ / (2 : ℝ) ^ p := by
        apply Finset.sum_le_sum
        intro h hh
        have h1 := hWt h hh
        have h2 := hu (egIdx s hs ((ℓ : ℤ) + h))
        have h3 : ‖((((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h : ℝ)) : ℂ)‖
            = |((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h)| := by
          simpa using RCLike.norm_ofReal (K := ℂ) ((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h)
        rw [norm_mul, h3]
        calc |((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h)|
              * ‖u (egIdx s hs ((ℓ : ℤ) + h))‖
            ≤ (δ / (2 : ℝ) ^ p) * 1 := mul_le_mul h1 h2 (norm_nonneg _) hδp
          _ = δ / (2 : ℝ) ^ p := mul_one _
    _ = ((egHset m).card : ℝ) * (δ / (2 : ℝ) ^ p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (m : ℝ) * δ / (2 : ℝ) ^ p := by
        rw [hcard, mul_div_assoc]

end Work.Resample
