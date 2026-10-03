import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.principalStrict_one_of_isPrimary
import Submission.Work.FIArea6Hecke.R.axisBadPoly_one

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- Every primary Gaussian integer is a unit modulo `4`, so the Hecke eigenvalue attached to the
trivial character `1` and that attached to the principal strict character modulo `4` agree. -/
lemma heckeLam_one_eq_heckeLam_principalStrict_one (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam (fun _ => (1 : ℂ)) 0 n
      = Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict 1) 0 n := by
  classical
  simp only [Work.FIArea5.S16Hecke.heckeLam, Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter] at hz
  rw [Work.FIArea6Hecke.R.principalStrict_one_of_isPrimary hz.2.1]

/-- The Hecke `L`-series at weight `0` for the trivial character equals the one for the principal
strict character modulo `4`. -/
lemma heckeLSeries_one_eq_principalStrict_one (s : ℂ) :
    Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s
      = Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict 1) 0 s := by
  simp only [Work.FIArea5.S16Hecke.heckeLSeries]
  rw [funext heckeLam_one_eq_heckeLam_principalStrict_one]

/-- **The trivial Hecke `L`-series is `ζ·L(χ₄)` with the Euler factor at `2` removed.**  Every
primary Gaussian integer is odd, so no primary element has norm divisible by `2`; hence
`heckeLam (fun _ => 1) 0 (2^ν) = 0` for `ν ≥ 1` and

  `heckeLSeries (fun _ => 1) 0 s = ζ(s)·L(s,χ₄)·(1 - 2^{-s})`.

Equivalently: `heckeLam (fun _ => 1) 0` agrees with `heckeLam (principalStrict 1) 0` on primary
elements (all primary elements are odd, hence units modulo `4`), and the identity is
`Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq` at `d = 1` (`axisBadPoly 1 s = 1 - 2^{-s}`).
A route from scratch: `λ(n) = #{primary z : gnorm z = n}` and (via
`Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4` together with the bijection
between primary elements of norm `n` and the four associates of the representations
`n = a² + b²`) one has `λ(n) = Σ_{d ∣ n} χ₄(d)` for odd `n` and `λ(n) = 0` for even `n`; the
Euler-product comparison then gives the claim. -/
theorem heckeLSeries_one_eq_zeta_mul_chi4 {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s
      = riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s
        * (1 - (2 : ℂ) ^ (-s)) := by
  rw [heckeLSeries_one_eq_principalStrict_one s,
    Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq 1 le_rfl hs,
    Work.FIArea6Hecke.R.axisBadPoly_one s]

end

end Work.FIArea6Hecke.R
