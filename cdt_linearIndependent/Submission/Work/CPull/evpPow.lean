import Mathlib
import Submission.Work.CPull.evp_aux

namespace Work.CPull

/-- Powers of a power series: if the coefficient series of `b` is absolutely summable at `z`, then
so is that of `b ^ d`, its ℓ¹-mass is bounded by the `d`-th power of the ℓ¹-mass of `b`, and
`b ↦ evp b z` is multiplicative on powers. -/
theorem evpPow (b : PowerSeries ℚ) (z : ℂ)
    (hb : Summable fun j : ℕ => ‖((PowerSeries.coeff j b : ℚ) : ℂ) * z ^ j‖) :
    ∀ d : ℕ,
      Summable (fun n : ℕ => ‖((PowerSeries.coeff n (b ^ d) : ℚ) : ℂ) * z ^ n‖) ∧
        (∑' n : ℕ, ‖((PowerSeries.coeff n (b ^ d) : ℚ) : ℂ) * z ^ n‖)
          ≤ (∑' j : ℕ, ‖((PowerSeries.coeff j b : ℚ) : ℂ) * z ^ j‖) ^ d ∧
        (∑' n : ℕ, ((PowerSeries.coeff n (b ^ d) : ℚ) : ℂ) * z ^ n) = (evp b z) ^ d := by
  intro d
  induction d with
  | zero =>
    have h1 : (fun n : ℕ => ‖((PowerSeries.coeff n (1 : PowerSeries ℚ) : ℚ) : ℂ) * z ^ n‖)
        = fun n : ℕ => if n = 0 then (1 : ℝ) else 0 := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [PowerSeries.coeff_one]; simp [hn]
    have h2 : (fun n : ℕ => ((PowerSeries.coeff n (1 : PowerSeries ℚ) : ℚ) : ℂ) * z ^ n)
        = fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [PowerSeries.coeff_one]; simp [hn]
    refine ⟨?_, ?_, ?_⟩
    · rw [pow_zero, h1]
      exact (hasSum_ite_eq 0 (1 : ℝ)).summable
    · rw [pow_zero, h1, tsum_ite_eq 0 (fun _ => (1 : ℝ))]
      simp
    · rw [pow_zero, h2, tsum_ite_eq 0 (fun _ => (1 : ℂ))]
      simp
  | succ d ih =>
    obtain ⟨hS, hle, hev⟩ := ih
    obtain ⟨hS', hle', _hsum', hev'⟩ := evpMul (b ^ d) b z hS hb
    have hM : 0 ≤ ∑' j : ℕ, ‖((PowerSeries.coeff j b : ℚ) : ℂ) * z ^ j‖ :=
      tsum_nonneg (fun j => norm_nonneg _)
    have hpowb : b ^ (d + 1) = b ^ d * b := pow_succ b d
    have hpowM : (∑' j : ℕ, ‖((PowerSeries.coeff j b : ℚ) : ℂ) * z ^ j‖) ^ (d + 1)
        = (∑' j : ℕ, ‖((PowerSeries.coeff j b : ℚ) : ℂ) * z ^ j‖) ^ d
          * (∑' j : ℕ, ‖((PowerSeries.coeff j b : ℚ) : ℂ) * z ^ j‖) := pow_succ _ d
    refine ⟨?_, ?_, ?_⟩
    · rw [hpowb]; exact hS'
    · rw [hpowb, hpowM]
      exact le_trans hle' (mul_le_mul hle le_rfl hM (pow_nonneg hM d))
    · rw [hpowb]
      have h2 : (∑' n : ℕ, ((PowerSeries.coeff n (b ^ d * b) : ℚ) : ℂ) * z ^ n)
          = (∑' n : ℕ, ((PowerSeries.coeff n (b ^ d) : ℚ) : ℂ) * z ^ n) * (evp b z) := by
        show evp (b ^ d * b) z = evp (b ^ d) z * evp b z
        exact hev'
      rw [h2, hev, pow_succ]

end Work.CPull
