import Mathlib
import Submission.Work.FIArea2.Count.card_box_filter_congr_le

namespace Work.FIArea6.S16ErrTwo

/-- **Counting solutions of a linear congruence in a symmetric interval.**

For `m ≥ 1`, coprime to `b`, the number of `u ∈ [-R,R]` with `m ∣ b*u + n` is at most
`2R/m + 1`.  Indeed the congruence is `m ∣ b*u - (-n)`, which is the shape covered by
`Work.FIArea2.Count.card_Icc_filter_dvd_le`, whose bound is `2R·gcd(b.natAbs,m)/m + 1`; the
coprimality hypothesis makes the gcd equal to `1`. -/
theorem card_Icc_filter_dvd_le (m : ℕ) (hm : 1 ≤ m) (b n : ℤ) (R : ℕ)
    (hb : Nat.Coprime m b.natAbs) :
    ((Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun u => (m : ℤ) ∣ (b * u + n))).card
      ≤ 2 * R / m + 1 := by
  have h := Work.FIArea2.Count.card_Icc_filter_dvd_le m hm b (-n) R
  have hcongr : (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun u => (m : ℤ) ∣ (b * u + n))
      = (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun u => (m : ℤ) ∣ (b * u - -n)) := by
    apply Finset.filter_congr
    intro u _
    rw [sub_neg_eq_add]
  rw [hcongr]
  have hg : Nat.gcd b.natAbs m = 1 := by
    rw [Nat.gcd_comm]; exact hb
  rw [hg] at h
  simpa using h

end Work.FIArea6.S16ErrTwo
