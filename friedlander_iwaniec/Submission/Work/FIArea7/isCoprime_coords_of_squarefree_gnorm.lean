import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea7

/-- The Gaussian norm of `Zsqrtd`-element `z` is `re ^ 2 + im ^ 2` (here `d = -1`). -/
private lemma gaussianInt_norm_eq (z : GaussianInt) :
    z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- `gnorm z = re.natAbs ^ 2 + im.natAbs ^ 2`. -/
private lemma gnorm_eq (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  unfold Work.FIPlan.gnorm
  rw [gaussianInt_norm_eq,
      Int.natAbs_add_of_nonneg (by positivity) (by positivity),
      Int.natAbs_pow, Int.natAbs_pow]

/-- If the (rational) norm `gnorm z = re ^ 2 + im ^ 2` is squarefree, then the two
coordinates `re`, `im` of the Gaussian integer `z` are coprime.

Indeed, if `d = gcd (re.natAbs) (im.natAbs)` then `d ^ 2 ∣ re ^ 2 + im ^ 2 = gnorm z`,
so squarefreeness forces `d = 1`, i.e. `IsCoprime z.re z.im`. -/
theorem isCoprime_coords_of_squarefree_gnorm {z : GaussianInt}
    (h : Squarefree (Work.FIPlan.gnorm z)) : IsCoprime z.re z.im := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  -- the gcd of the coordinate absolute values squares to a divisor of `gnorm z`
  have hdvd : (z.re.natAbs.gcd z.im.natAbs) * (z.re.natAbs.gcd z.im.natAbs) ∣
      z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
    have h1 : (z.re.natAbs.gcd z.im.natAbs) ^ 2 ∣ z.re.natAbs ^ 2 :=
      pow_dvd_pow_of_dvd (Nat.gcd_dvd_left _ _) 2
    have h2 : (z.re.natAbs.gcd z.im.natAbs) ^ 2 ∣ z.im.natAbs ^ 2 :=
      pow_dvd_pow_of_dvd (Nat.gcd_dvd_right _ _) 2
    have h3 := Nat.dvd_add h1 h2
    rwa [sq] at h3
  have hunit : IsUnit (z.re.natAbs.gcd z.im.natAbs) := h _ (by rwa [gnorm_eq])
  simpa [Nat.isUnit_iff] using hunit

end Work.FIArea7
