import Mathlib
import Submission.Work.FIArea3.JointCount.pieces

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Divisibility of the Gaussian-integer lifts of two ordinary integers is the same as
divisibility in `ℤ`.  (The forward direction reads off the real part, which is why no
hypothesis on the sign of the integers is needed.) -/
lemma intCast_dvd_intCast_iff {a b : ℤ} :
    ((a : GaussianInt) ∣ (b : GaussianInt)) ↔ a ∣ b := by
  constructor
  · rintro ⟨w, hw⟩
    have h := congrArg Zsqrtd.re hw
    rw [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] at h
    simp at h
    exact ⟨w.re, h⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(k : GaussianInt), by push_cast; ring⟩

/-- **The piece `gaussPieceGen d u · ℤ[i]` lies inside `{z | d ∣ |z|²}`.**

Writing `g = gaussPieceGen d u = lcm u (star (d/u))`, the membership hypothesis `g ∣ z` splits
(via `EuclideanDomain.lcm_dvd_iff` and `star_dvd_iff_dvd_star`) into `u ∣ z` and `(d/u) ∣ star z`.
Multiplying the two witnesses and using `u * (d/u) = d` (here `hd` and `hu` give `u ≠ 0`)
produces `d ∣ z * star z = |z|²`, and reading off the real part converts the Gaussian
divisibility into the integer divisibility `d ∣ gnorm z`. -/
theorem gaussPieceGen_dvd_gnorm (d : ℕ) (hd : 1 ≤ d) {u z : GaussianInt}
    (hu : u ∣ (d : GaussianInt)) (hz : Work.FIArea3.JointCount.gaussPieceGen d u ∣ z) :
    d ∣ Work.FIPlan.gnorm z := by
  rw [gaussPieceGen, EuclideanDomain.lcm_dvd_iff] at hz
  obtain ⟨huz, hsz⟩ := hz
  have h2 : ((d : GaussianInt) / u) ∣ star z := (star_dvd_iff_dvd_star _ _).mp hsz
  obtain ⟨a, ha⟩ := huz
  obtain ⟨b, hb⟩ := h2
  have hd0 : (d : GaussianInt) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hu0 : u ≠ 0 := ne_zero_of_dvd_ne_zero hd0 hu
  have hmul : u * ((d : GaussianInt) / u) = (d : GaussianInt) :=
    EuclideanDomain.mul_div_cancel' hu0 hu
  -- `z * star z = |z|²` is divisible by `u * (d/u) = d`.
  have hprod : z * star z = (d : GaussianInt) * (a * b) := by
    calc z * star z = (u * a) * (((d : GaussianInt) / u) * b) := by rw [hb, ha]
      _ = (u * ((d : GaussianInt) / u)) * (a * b) := by ring
      _ = (d : GaussianInt) * (a * b) := by rw [hmul]
  -- identify the Gaussian integer `z * star z` with the lift of `gnorm z`.
  have hnormcast : (gnorm z : GaussianInt) = z * star z := by
    have hnn : 0 ≤ z.norm := Zsqrtd.norm_nonneg (d := -1) (by norm_num) z
    have h1 : ((z.norm.natAbs : ℤ) : GaussianInt) = ((z.norm : ℤ) : GaussianInt) := by
      rw [Int.natAbs_of_nonneg hnn]
    simpa [gnorm] using h1.trans (Zsqrtd.norm_eq_mul_conj z)
  have hddvd : (d : GaussianInt) ∣ (gnorm z : GaussianInt) :=
    ⟨a * b, hnormcast.trans hprod⟩
  -- descend from Gaussian divisibility of integer lifts to `d ∣ gnorm z` in `ℕ`.
  rw [← Int.cast_natCast d, ← Int.cast_natCast (gnorm z)] at hddvd
  have hz1 : (d : ℤ) ∣ (gnorm z : ℤ) := intCast_dvd_intCast_iff.mp hddvd
  exact_mod_cast hz1

end

end Work.FIArea3.JointCount
