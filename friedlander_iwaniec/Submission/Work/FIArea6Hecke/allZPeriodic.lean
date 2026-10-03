import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs

namespace Work.FIArea6Hecke

open Work.FIArea6Hecke.R

/-- The modulus `M` divides its own norm `gnorm M = N(M) = M · M̄`, viewed as an element of `ℤ[i]`.
This is what makes `M`-periodicity imply `N(M)`-periodicity. -/
lemma dvd_gnorm_self (M : GaussianInt) :
    M ∣ (((Work.FIPlan.gnorm M : ℤ)) : GaussianInt) := by
  refine ⟨star M, ?_⟩
  rw [← Zsqrtd.norm_eq_mul_conj (d := -1) M]
  norm_num [Work.FIPlan.gnorm, GaussianInt.natCast_natAbs_norm]

theorem allZPeriodic (M : GaussianInt) (chi₀ : GaussianInt → ℂ)
    (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi₀) :
    ∀ z w : GaussianInt, (((Work.FIPlan.gnorm M : ℤ)) : GaussianInt) ∣ (z - w) → chi₀ z = chi₀ w := by
  intro z w h
  exact hchi.2.2.2.1 z w (dvd_trans (dvd_gnorm_self M) h)

end Work.FIArea6Hecke
