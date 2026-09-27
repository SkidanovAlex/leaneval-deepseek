import Mathlib
import Submission.Work.EQ.FanTri.SecOrderDefs

namespace Work.EQ.FanTri

open Work.EQ

/-- First coordinate of the backward branch `invBranch a true` at `A₁ + z`, with
`A₁ = (-1/2, 0)`: writing `Q = A₁ + z` one has `Q.1 + a/2 = -sD a z`, hence
`(invBranch a true Q).1 = 1/2 - z.1 - sD a z/sR a z`. -/
lemma PhiT_invBranch_fst (a : ℝ) (z : ℂ × ℂ) :
    (invBranch a true (shiftA1 z)).1 = 1 / 2 - z.1 - sD a z / sR a z := by
  have hQ1 : (((-1 / 2 : ℝ) : ℂ) + z.1) + ((a / 2 : ℝ) : ℂ) = -sD a z := by
    simp only [sD, sHat]; push_cast; ring
  unfold invBranch shiftA1 sR
  simp only [ite_true, one_mul]
  rw [hQ1]
  norm_num
  ring

/-- Second coordinate of the backward branch `invBranch a true` at `A₁ + z`:
`(invBranch a true (A₁+z)).2 = z.2/sR a z - z.2`. -/
lemma PhiT_invBranch_snd (a : ℝ) (z : ℂ × ℂ) :
    (invBranch a true (shiftA1 z)).2 = z.2 / sR a z - z.2 := by
  have hQ1 : (((-1 / 2 : ℝ) : ℂ) + z.1) + ((a / 2 : ℝ) : ℂ) = -sD a z := by
    simp only [sD, sHat]; push_cast; ring
  unfold invBranch shiftA1 sR
  simp only [ite_true, one_mul]
  rw [hQ1]
  ring

/-- The eigenvalue identity `1/λ + 1 = 1/s` (`λ = eqLam a`, `s = sHat a`), pushed to `ℂ`:
`(eqLam a : ℂ)⁻¹ + 1 = ((sHat a)⁻¹ : ℝ)`. -/
lemma PhiT_ofReal_inv_eqLam_add_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ((eqLam a : ℂ))⁻¹ + 1 = (((sHat a)⁻¹ : ℝ) : ℂ) := by
  have h := congrArg (fun t : ℝ => (t : ℂ)) (inv_eqLam_add_one ha0 ha1)
  push_cast at h
  simpa [Complex.ofReal_inv] using h

/-- Coordinates of the second-order remainder
`PhiT a z = invBranch a true (A₁+z) - A₁ - L z` at `A₁ = (-1/2,0)`, where
`L(δ₁,δ₂) = (-δ₁, δ₂/λ)`, `λ = eqLam a`, `facA a z = (sR a z * (sR a z + sD a z))⁻¹`,
`facB a z = (sR a z)⁻¹`.

With `Q = A₁ + z` one has `Q.1 + a/2 = -sD a z`, so
`(invBranch a true Q).1 = 1/2 - z.1 - sD a z/sR a z` and `(invBranch a true Q).2 = z.2/sR a z - z.2`.
Hence `(PhiT a z).1 = 1 - sD a z/sR a z = z.2^2/(sR a z * (sR a z + sD a z))` (using
`sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2`, supplied by `sD_sR_setup`) and
`(PhiT a z).2 = z.2 * ((sR a z)⁻¹ - (sHat a)⁻¹)`, using `1/λ + 1 = 1/sHat a`
(`inv_eqLam_add_one`).  The two nonvanishing statements are in the conclusion because the
first identity needs `R + D ≠ 0` and the second needs `R ≠ 0` (both hold on the ball). -/
theorem PhiT_coords {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ} (hz : ‖z‖ ≤ sHat a / 16) :
    sR a z ≠ 0 ∧ sR a z + sD a z ≠ 0 ∧
      (PhiT a z).1 = z.2 ^ 2 * facA a z ∧
      (PhiT a z).2 = z.2 * (facB a z - (((sHat a)⁻¹ : ℝ) : ℂ)) := by
  obtain ⟨hDne, hDre, hDim, hz2D, hRfac, hRsq⟩ := sD_sR_setup ha0 ha1 hz
  have hDn : 0 < ‖sD a z‖ := norm_pos_iff.mpr hDne
  -- `R ≠ 0`: `R = D · sqHalf ((z₂/D)²)` has positive real part.
  have hRne : sR a z ≠ 0 := by
    have h := FanSep.re_mul_sqHalf_pos_aux hDne hDre hDim hz2D
    have hpos : 0 < (sR a z).re := by rwa [hRfac]
    intro h0
    rw [h0] at hpos
    simp at hpos
  -- `R + D ≠ 0`: `R + D = D · (sqHalf ((z₂/D)²) + 1)` and `‖(z₂/D)²‖ < 1`.
  have hRDne : sR a z + sD a z ≠ 0 := by
    have hw : ‖(z.2 / sD a z) ^ 2‖ < 1 := by
      rw [norm_pow, norm_div]
      have h2 : ‖z.2‖ / ‖sD a z‖ ≤ 1 / 2 := by
        rw [div_le_iff₀ hDn]; linarith
      have hnn : 0 ≤ ‖z.2‖ / ‖sD a z‖ := div_nonneg (norm_nonneg _) hDn.le
      nlinarith
    have hS1 : sqHalf ((z.2 / sD a z) ^ 2) + 1 ≠ 0 := sqHalf_add_one_ne_zero hw
    intro h
    apply hS1
    have hmul : sD a z * (sqHalf ((z.2 / sD a z) ^ 2) + 1) = 0 := by
      rw [mul_add, mul_one, ← hRfac]; exact h
    exact (mul_eq_zero.mp hmul).resolve_left hDne
  refine ⟨hRne, hRDne, ?_, ?_⟩
  · have hP1 : (PhiT a z).1 = 1 - sD a z / sR a z := by
      unfold PhiT
      simp only [Prod.fst_sub, PhiT_invBranch_fst a z]
      norm_num
      ring
    rw [hP1, facA, div_eq_mul_inv]
    field_simp
    linear_combination hRsq
  · have hP2 : (PhiT a z).2 = z.2 / sR a z - z.2 - z.2 / (eqLam a : ℂ) := by
      unfold PhiT
      simp only [Prod.snd_sub, PhiT_invBranch_snd a z]
      ring
    rw [hP2, facB, div_eq_mul_inv, div_eq_mul_inv]
    have hlam := PhiT_ofReal_inv_eqLam_add_one ha0 ha1
    linear_combination (-z.2) * hlam

end Work.EQ.FanTri
