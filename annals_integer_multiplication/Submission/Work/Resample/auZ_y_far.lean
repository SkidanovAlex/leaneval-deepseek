import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.ExpPosTdivKit

namespace Work.Resample

/-- If the fixed-point exponent `auZ p α t N` already exceeds the guard `(p+10)·2^P`, then the
*true* exponent `πN/(α²t²)` is at least `p+9`.

The fixed-point value `auPi p` of `2^P π` is known to within `1`, and `auZ` is the truncated
quotient of `auPi p · N` by `α²t²`; both numerator and denominator of that quotient are
nonnegative, so `auZ` is the floor of `auPi p · N / (α²t²)`.  Hence `auZ > (p+10)·2^P` gives
`auPi p · N ≥ ((p+10)·2^P + 1)·α²t²`, so `N/(α²t²) ≥ ((p+10)·2^P+1)/(2^P π + 1)`, and finally
`π N/(α²t²) ≥ π((p+10)·2^P+1)/(2^P π+1) ≥ p+9`. -/
theorem auZ_y_far (p α t : ℕ) (N : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) (ht : 1 ≤ t)
    (hpi : |(auPi p : ℝ) - (2:ℝ)^(auPrec p) * Real.pi| ≤ 1)
    (hg : ((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) < auZ p α t (N:ℤ)) :
    (p:ℝ) + 9 ≤ Real.pi * (N:ℝ) / ((α:ℝ)^2 * (t:ℝ)^2) := by
  have hαZ : (2:ℤ) ≤ (α:ℤ) := by exact_mod_cast hα
  have htZ : (1:ℤ) ≤ (t:ℤ) := by exact_mod_cast ht
  have hpow1 : (1:ℝ) ≤ (2:ℝ)^(auPrec p) := one_le_pow₀ (by norm_num)
  have hpowpos : (0:ℝ) < (2:ℝ)^(auPrec p) := pow_pos (by norm_num) _
  -- bounds on `auPi p`
  have hpi_le : (auPi p : ℝ) ≤ (2:ℝ)^(auPrec p) * Real.pi + 1 := by
    have := (abs_le.mp hpi).2; linarith
  have hpi_ge : (2:ℝ)^(auPrec p) * Real.pi - 1 ≤ (auPi p : ℝ) := by
    have := (abs_le.mp hpi).1; linarith
  have hpi3 : (3:ℝ) ≤ (2:ℝ)^(auPrec p) * Real.pi := by
    have h3 : (3:ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    calc (3:ℝ) = 1 * 3 := by ring
      _ ≤ (2:ℝ)^(auPrec p) * Real.pi :=
          mul_le_mul hpow1 h3 (by norm_num) (le_of_lt hpowpos)
  have hpi_posR : (0:ℝ) < (auPi p : ℝ) := by linarith only [hpi_ge, hpi3]
  have hpi_nonneg : (0:ℤ) ≤ auPi p := by
    have : (0:ℝ) ≤ (auPi p : ℝ) := le_of_lt hpi_posR
    exact_mod_cast this
  set L : ℤ := (α:ℤ)^2 * (t:ℤ)^2 with hLdef
  set Y : ℤ := auPi p * (N:ℤ) with hYdef
  have hLposZ : (0:ℤ) < L := by
    rw [hLdef]
    exact mul_pos (pow_pos (by omega) 2) (pow_pos (by omega) 2)
  have hL1 : (1:ℤ) ≤ L := by omega
  have hLposR : (0:ℝ) < (L:ℝ) := by exact_mod_cast hLposZ
  have hy : (0:ℤ) ≤ Y := by
    rw [hYdef]
    exact mul_nonneg hpi_nonneg (Int.natCast_nonneg N)
  obtain ⟨_, _, h3, _, _⟩ := Work.Fx.ExpPosTdivKit Y L hL1
  obtain ⟨h3a, _⟩ := h3 hy
  have hZeq : auZ p α t (N:ℤ) = Y.tdiv L := by simp only [auZ, hLdef, hYdef]
  have hle : (auZ p α t (N:ℤ) : ℝ) ≤ (Y:ℝ)/(L:ℝ) := by rw [hZeq]; exact h3a
  have hYcast : (Y:ℝ) = (auPi p : ℝ) * (N:ℝ) := by rw [hYdef]; push_cast; ring
  have hLcast : (L:ℝ) = (α:ℝ)^2 * (t:ℝ)^2 := by rw [hLdef]; push_cast; ring
  have hXpos : (0:ℝ) < (α:ℝ)^2 * (t:ℝ)^2 := by rw [← hLcast]; exact hLposR
  -- `auZ > (p+10)·2^P` implies `A·X ≤ auPi·N`
  have hCp1 : (((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) : ℝ) + 1 ≤ (auZ p α t (N:ℤ) : ℝ) := by
    have hz : ((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) + 1 ≤ auZ p α t (N:ℤ) := by omega
    calc (((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) : ℝ) + 1
        = ((((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) + 1 : ℤ) : ℝ) := by push_cast; ring
      _ ≤ (auZ p α t (N:ℤ) : ℝ) := by exact_mod_cast hz
  have hstep1 : ((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1 ≤ (Y:ℝ)/(L:ℝ) := by
    have hcast : (((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) : ℝ) = ((p:ℝ)+10) * (2:ℝ)^(auPrec p) := by
      push_cast; ring
    calc ((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1
        = (((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) : ℝ) + 1 := by rw [hcast]
      _ ≤ (auZ p α t (N:ℤ) : ℝ) := hCp1
      _ ≤ (Y:ℝ)/(L:ℝ) := hle
  have hstep2 : (((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1) * ((α:ℝ)^2*(t:ℝ)^2)
      ≤ (auPi p : ℝ)*(N:ℝ) := by
    have h := hstep1
    rw [hYcast, hLcast, le_div_iff₀ hXpos] at h
    linarith only [h]
  have hNnonneg : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hstep3 : (((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1) * ((α:ℝ)^2*(t:ℝ)^2)
      ≤ ((2:ℝ)^(auPrec p) * Real.pi + 1) * (N:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hpi_le hNnonneg
    linarith only [hstep2, hmul]
  have hDpos : (0:ℝ) < (2:ℝ)^(auPrec p) * Real.pi + 1 := by linarith only [hpi3]
  -- divide by `2^P π + 1`
  have hstep4 : (((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1) * ((α:ℝ)^2*(t:ℝ)^2)
      / ((2:ℝ)^(auPrec p) * Real.pi + 1) ≤ (N:ℝ) := by
    rw [div_le_iff₀ hDpos]; linarith only [hstep3]
  have hstep4' : (((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1) * ((α:ℝ)^2*(t:ℝ)^2)
      ≤ (N:ℝ) * ((2:ℝ)^(auPrec p) * Real.pi + 1) := by
    have h := hstep4
    rw [div_le_iff₀ hDpos] at h
    linarith only [h]
  -- multiply by `π / (α²t²)`
  have hstep5' : Real.pi * (((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1)
      / ((2:ℝ)^(auPrec p) * Real.pi + 1) ≤ Real.pi * (N:ℝ) / ((α:ℝ)^2*(t:ℝ)^2) := by
    rw [le_div_iff₀ hXpos, div_mul_eq_mul_div, div_le_iff₀ hDpos]
    have h := mul_le_mul_of_nonneg_left hstep4' (le_of_lt Real.pi_pos)
    linarith only [h]
  -- `(p+9) ≤ π A / D`
  have hp9 : (p:ℝ) + 9 ≤ (2:ℝ)^(auPrec p) := by
    have h1 : ((p+9:ℕ):ℝ) ≤ (2:ℝ)^(auPrec p) := by
      have h2 : ((p+9:ℕ):ℝ) < (2:ℝ)^(p+9) := by exact_mod_cast (Nat.lt_two_pow_self (n := p+9))
      have h3 : (2:ℝ)^(p+9) ≤ (2:ℝ)^(auPrec p) := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ (2:ℝ))
        simp only [auPrec]; omega
      linarith only [h2, h3]
    push_cast at h1
    exact h1
  have hfinal : (p:ℝ) + 9 ≤ Real.pi * (((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1)
      / ((2:ℝ)^(auPrec p) * Real.pi + 1) := by
    rw [le_div_iff₀ hDpos]
    have hbc : (p:ℝ) + 9 ≤ (2:ℝ)^(auPrec p) * Real.pi := by
      have h1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have h := mul_le_mul_of_nonneg_left h1 (le_of_lt hpowpos)
      linarith only [hp9, h]
    have hexp : Real.pi * (((p:ℝ)+10) * (2:ℝ)^(auPrec p) + 1)
        - ((p:ℝ)+9) * ((2:ℝ)^(auPrec p) * Real.pi + 1)
        = (2:ℝ)^(auPrec p) * Real.pi + Real.pi - ((p:ℝ)+9) := by ring
    linarith only [hbc, Real.pi_pos, hexp]
  linarith only [hfinal, hstep5']

end Work.Resample
