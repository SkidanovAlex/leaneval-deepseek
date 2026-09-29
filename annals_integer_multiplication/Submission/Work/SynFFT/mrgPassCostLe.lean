import Mathlib
import Submission.Work.SynFFT.kit2

namespace Work.SynFFT

/-- The merge-pass cost of the synthetic FFT is dominated by `K₁ * t * (r+1) * (p+1) + K₁`.

Since `2 * s ∣ t`, writing `k = t / (2 * s)` we have `k * (2 * s) = t`, so in particular
`k ≤ t`, `k * s ≤ t` and `s ≤ 2 * s ≤ t`.  All the `isz`-terms are sizes of `1`, `s` and
`2 * s`, hence at most `t` up to constants, and `V ≤ t * (13 * (r+1) * (p+1) + 1) + 1`.
The constant `K₁` below is chosen generously (roughly the sum of the coefficients plus the
additive constants) so that the term-by-term estimate closes. -/
theorem mrgPassCostLe (Kpv Kpk Kshl Kch Kdr Kb Kml Kfl : ℕ) :
    ∃ K₁ : ℕ, ∀ (V t s r p : ℕ), 0 < s → 0 < t → 2 * s ∣ t →
      V ≤ t * (13 * (r + 1) * (p + 1) + 1) + 1 →
      Kpv * (HvdH.isz (1 : ℤ) + 1)
      + Kpk * 3 * (HvdH.isz (1 : ℤ) + V + HvdH.isz (s : ℤ) + 1)
      + Kshl * (HvdH.isz (s : ℤ) + 1 + HvdH.isz (1 : ℤ))
      + Kch * (V + (t / (2 * s) + 1) * HvdH.isz ((2 * s : ℕ) : ℤ) + 1)
      + Kdr * (HvdH.isz ((2 * s : ℕ) : ℤ) + 1)
      + (t / (2 * s)) * ((Kb * s * (r + 1) * (p + 1) + Kb) +
          Kml * (2 * s * (13 * (r + 1) * (p + 1) + 1) + 2)) + Kml
      + Kfl * ((t / (2 * s)) * (2 * s * (13 * (r + 1) * (p + 1) + 1) + 2) + 2)
      ≤ K₁ * t * (r + 1) * (p + 1) + K₁ := by
  refine ⟨4*Kpv + 66*Kpk + 7*Kshl + 22*Kch + 4*Kdr + 2*Kb + 16*Kml + 18*Kfl + Kml + 1, ?_⟩
  intro V t s r p hs ht hd hV
  -- unfold the three `isz` values
  have hisz1 : HvdH.isz (1:ℤ) = 3 := by simp [HvdH.isz]
  have hiszs : HvdH.isz (s:ℤ) = s.size + 2 := by
    simp only [HvdH.isz, Int.natAbs_natCast]
  have hisz2s : HvdH.isz ((2*s:ℕ):ℤ) = (2*s).size + 2 := by
    simp only [HvdH.isz, Int.natAbs_natCast]
  rw [hisz1, hiszs, hisz2s]
  -- basic size facts
  have hD1 : 1 ≤ (r+1)*(p+1) := by
    have h1 : 1 ≤ r+1 := by omega
    have h2 : 1 ≤ p+1 := by omega
    nlinarith only [h1, h2]
  have ht_le_tD : t ≤ t*((r+1)*(p+1)) := by
    have := Nat.mul_le_mul_left t hD1
    simpa using this
  have htD : 1 ≤ t*((r+1)*(p+1)) := by
    have := Nat.mul_le_mul ht hD1
    simpa using this
  have h2s : 2*s ≤ t := Nat.le_of_dvd ht hd
  have hs_le : s ≤ t := by omega
  -- the quotient `t / (2*s)` and its basic bounds
  have hk2s : t/(2*s) * (2*s) = t := Nat.div_mul_cancel hd
  have hk_le : t/(2*s) ≤ t := by
    have h := Nat.mul_le_mul_left (t/(2*s)) (show (1:ℕ) ≤ 2*s by omega)
    simp only [Nat.mul_one] at h
    exact h.trans_eq hk2s
  have hks_le : t/(2*s) * s ≤ t := by
    have h := Nat.mul_le_mul_left (t/(2*s)) (show s ≤ 2*s by omega)
    exact h.trans_eq hk2s
  have hksD : t/(2*s)*s*((r+1)*(p+1)) ≤ t*((r+1)*(p+1)) :=
    Nat.mul_le_mul_right ((r+1)*(p+1)) hks_le
  -- sizes are bounded by `t`
  have hsz_2s' : (2*s).size ≤ 2*s := Nat.size_le.2 Nat.lt_two_pow_self
  have hsz_sD : s.size ≤ t*((r+1)*(p+1)) := by
    have hsz_s : s.size ≤ t := (Nat.size_le.2 Nat.lt_two_pow_self).trans hs_le
    linarith only [hsz_s, ht_le_tD]
  have hsz_2sD : (2*s).size ≤ t*((r+1)*(p+1)) := by
    linarith only [hsz_2s', h2s, ht_le_tD]
  -- `V` grows at most linearly in `t * (r+1) * (p+1)`
  have hVD : V ≤ 15*(t*((r+1)*(p+1))) := by
    have h1 : t + 1 ≤ 2*(t*((r+1)*(p+1))) := by nlinarith only [ht_le_tD, htD]
    nlinarith only [hV, h1]
  -- the `Kch` block
  have hstep4 : (t/(2*s)+1)*((2*s).size+2) ≤ 6*(t*((r+1)*(p+1))) := by
    have hm := Nat.mul_le_mul_left (t/(2*s)+1)
      (show (2*s).size + 2 ≤ 2*s + 2 by omega)
    nlinarith only [hm, hk2s, hk_le, h2s, ht_le_tD, htD]
  -- the `Kml` block: the factor `k * (2*s)` collapses to `t`
  have hk13 : (t/(2*s))*(2*s*(13*(r+1)*(p+1)+1)) = t*(13*(r+1)*(p+1)+1) := by
    rw [← mul_assoc, hk2s]
  -- the constant is large enough
  have hSle : (4*Kpv + 66*Kpk + 7*Kshl + 22*Kch + 4*Kdr + 2*Kb + 16*Kml + 18*Kfl + 1)
      ≤ 4*Kpv + 66*Kpk + 7*Kshl + 22*Kch + 4*Kdr + 2*Kb + 16*Kml + 18*Kfl + Kml + 1 := by
    omega
  have hKmle : Kml
      ≤ 4*Kpv + 66*Kpk + 7*Kshl + 22*Kch + 4*Kdr + 2*Kb + 16*Kml + 18*Kfl + Kml + 1 := by
    omega
  nlinarith only [hV, hVD, hsz_sD, hsz_2sD, hsz_2s', htD, ht_le_tD, hk2s, hk13, hk_le,
    hksD, h2s, hstep4, hs, hSle, hKmle]

end Work.SynFFT
