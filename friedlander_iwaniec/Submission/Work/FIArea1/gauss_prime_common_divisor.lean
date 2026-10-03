import Mathlib
import Submission.Work.FIArea1.conjunct2_defs

namespace Work.FIArea1

/-- **A common Gaussian prime of a non-coprime polar pair, of large norm.**

If `z₁, z₂` are two points of the polar box (5.14) at scale `N` with *squarefree* norm free of
primes `≤ P` (5.8) and are not coprime in `ℤ[i]`, then they share a Gaussian prime `π` whose norm
`|π|²` exceeds `P`.

The existence of `π` is the UFD property of `ℤ[i]` (a common non-unit divisor, already produced by
`Work.FIArea1.offdiag_exists_common_dvd`, has a prime factor); the size `|π|² > P` is (5.8): the
prime `π` divides `z₁`, and `gnorm z₁` is squarefree with no prime factor `≤ P`. -/
theorem gauss_prime_common_divisor {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : z1 ∈ Work.FIArea1.polarSupp Pa φ) (h2 : z2 ∈ Work.FIArea1.polarSupp Pa φ)
    (hnc : ¬ Work.FIPlan.GaussCoprime z1 z2) :
    ∃ π : GaussianInt, Prime π ∧ π ∣ z1 ∧ π ∣ z2 ∧ Pa.Pz < Work.FIPlan.gnorm π := by
  -- read off the polar-box structure of `z₁`
  rw [Work.FIArea1.mem_polarSupp] at h1
  obtain ⟨-, hp1, -, hns1⟩ := h1
  -- `¬ IsCoprime` gives a common non-unit divisor `d`
  have hnc' : ¬ IsCoprime z1 z2 := hnc
  have hex : ∃ d : GaussianInt, d ∣ z1 ∧ d ∣ z2 ∧ ¬ IsUnit d := by
    rw [← isRelPrime_iff_isCoprime] at hnc'
    rw [IsRelPrime] at hnc'
    push Not at hnc'
    exact hnc'
  obtain ⟨d, hd1, hd2, hdu⟩ := hex
  -- `d ≠ 0`, since `z₁ ≠ 0` (it has norm `> N ≥ 1`)
  have hd0 : d ≠ 0 := by
    intro hd
    obtain ⟨k, hk⟩ := hd1
    rw [hd, zero_mul] at hk
    have hz : (Work.FIPlan.gnorm z1 : ℝ) = 0 := by rw [hk]; simp [Work.FIPlan.gnorm]
    linarith [hp1.2.1, Pa.hN1]
  -- a prime factor `π` of `d` in the UFD `ℤ[i]`
  obtain ⟨π, hirr, hπd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  have hprime : Prime π := hirr.prime
  refine ⟨π, hprime, hπd.trans hd1, hπd.trans hd2, ?_⟩
  -- `gnorm π ≥ 2`, hence `gnorm π` has a prime factor `q`
  have hπne0 : π ≠ 0 := hprime.ne_zero
  have hgn0 : Work.FIPlan.gnorm π ≠ 0 := by
    intro hgg
    apply hπne0
    have : π.norm = 0 := by
      rw [Work.FIPlan.gnorm] at hgg; exact Int.natAbs_eq_zero.mp hgg
    exact (Zsqrtd.norm_eq_zero_iff (by norm_num : (-1 : ℤ) < 0) π).mp this
  have hgn1 : Work.FIPlan.gnorm π ≠ 1 := by
    intro hgg
    exact hprime.not_isUnit (Zsqrtd.norm_eq_one_iff.mp hgg)
  obtain ⟨q, hq, hqπ⟩ := Nat.exists_prime_and_dvd hgn1
  -- `q ∣ gnorm z₁`, so by (5.8) `q > Pz`
  have hvd : Work.FIPlan.gnorm π ∣ Work.FIPlan.gnorm z1 := by
    obtain ⟨k, hk⟩ := hπd.trans hd1
    rw [hk, Work.FIArea1.gnorm_mul]
    exact Nat.dvd_mul_right _ _
  have hqvd : q ∣ Work.FIPlan.gnorm z1 := hqπ.trans hvd
  have hqP : Pa.Pz < q := by
    by_contra hle
    exact hns1 q hq (le_of_not_gt hle) hqvd
  -- `q ≤ gnorm π`
  exact lt_of_lt_of_le hqP (Nat.le_of_dvd (Nat.pos_of_ne_zero hgn0) hqπ)

end Work.FIArea1
