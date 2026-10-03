import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea6Hecke.R

open Work.FIPlan

/-- `gnorm z = 0` if and only if `z = 0`. -/
private lemma gnorm_eq_zero' {z : GaussianInt} : gnorm z = 0 ↔ z = 0 := by
  rw [gnorm, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

/-- The norm `gnorm z = |z|²` is multiplicative. -/
private lemma gnorm_mul' (z w : GaussianInt) : gnorm (z * w) = gnorm z * gnorm w := by
  simp only [gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- If `M'` is a proper divisor of `M` and `M ≠ 0`, then `gnorm M' < gnorm M`.
Indeed `M = M' * c` with `c` a non-unit (else `M ∣ M'`), so `gnorm c ≥ 2` and
`gnorm M = gnorm M' * gnorm c > gnorm M'`. -/
theorem gnorm_lt_of_dvd_of_not_dvd {M' M : GaussianInt} (hdvd : M' ∣ M) (hnot : ¬ M ∣ M')
    (hM : M ≠ 0) : Work.FIPlan.gnorm M' < Work.FIPlan.gnorm M := by
  obtain ⟨c, rfl⟩ := hdvd
  have hM' : M' ≠ 0 := by
    intro h
    exact hnot (by simp [h])
  have hc0 : c ≠ 0 := by
    intro h
    exact hM (by rw [h, mul_zero])
  have hgc_ne1 : gnorm c ≠ 1 := by
    intro h1
    have hunit : IsUnit c := Zsqrtd.norm_eq_one_iff.mp h1
    obtain ⟨d, hd⟩ := isUnit_iff_dvd_one.mp hunit
    exact hnot ⟨d, by rw [mul_assoc, ← hd, mul_one]⟩
  have hgc2 : 2 ≤ gnorm c := by
    have h0 : gnorm c ≠ 0 := fun h => hc0 (gnorm_eq_zero'.mp h)
    omega
  have hpos : 0 < gnorm M' := Nat.pos_of_ne_zero (fun h => hM' (gnorm_eq_zero'.mp h))
  rw [gnorm_mul']
  calc gnorm M' = gnorm M' * 1 := (mul_one _).symm
    _ < gnorm M' * gnorm c := Nat.mul_lt_mul_of_pos_left (by omega) hpos

end Work.FIArea6Hecke.R
