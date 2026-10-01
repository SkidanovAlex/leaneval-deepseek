import Mathlib
import Submission.Work.LinnikAreas.tentLeftEdgeDeps
import Submission.Work.LinnikAreas.FarBoundOfDensity

/-!
# Norm bound for the tent kernel `Φ` on the left edge `Re u = -1/2`

`Commons.NumberTheory.Linnik.tentPhi L K q u = tentK L K ((1 - u)·log q)`, and
`tentK L K z = e^{-(L-2K)z}·((1 - e^{-Kz})/z)^2`.  On the left edge `u = -1/2 + it` one has
`1 - u = 3/2 - it`, so `Re z = (3/2)log q > 0`, `|z|² = (9/4 + t²)(log q)²`, and
`‖1 - e^{-Kz}‖ ≤ 2`.  With `L - 2K = 49/10` this gives

`‖Φ(11/2, 3/10, q, -1/2+it)‖ ≤ 4·q^{-147/20}·((log q)²·(9/4 + t²))⁻¹`.

The kernel estimate itself is `Work.LinnikAreas.Hk_norm_le` (the same kernel under the name
`Hk = e^{-(L-2K)z}F₂(z)`), and the two kernels are identified at `z ≠ 0` via
`tentK_eq_closed` and `F₂`.
-/

namespace Work.LinnikAreas

open Commons.NumberTheory.Linnik

theorem tentPhi_leftEdge_norm_bound (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    ‖Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q
        ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 4 * ((q : ℝ) ^ (-(147 : ℝ) / 20)) *
          (((Real.log (q : ℝ)) ^ 2) * (9 / 4 + t ^ 2))⁻¹ := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlogne : ((Real.log (q : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr hlogpos.ne'
  have hzne : ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
      ((Real.log (q : ℝ) : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ hlogne
    intro h
    have hre : ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I).re = 0 := by
      simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [Complex.sub_re, Complex.mul_re] at hre
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
    norm_num at hre
  have hnormsq : ‖((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
      ((Real.log (q : ℝ) : ℝ) : ℂ)‖ ^ 2 = (9 / 4 + t ^ 2) * (Real.log (q : ℝ)) ^ 2 := by
    rw [show ‖((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
          ((Real.log (q : ℝ) : ℝ) : ℂ)‖ ^ 2
        = Complex.normSq (((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
          ((Real.log (q : ℝ) : ℝ) : ℂ)) from Complex.sq_norm _]
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    have e1 : Complex.normSq ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) = 9/4 + t^2 := by
      rw [Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
      ring
    rw [e1]; ring
  have hHk := Work.LinnikAreas.Hk_norm_le (L := Real.log (q : ℝ)) hlogpos.le
    (ρ := (-(1 / 2) : ℂ) + (t : ℂ) * Complex.I) (by
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
      norm_num)
  rw [show (1 - ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I))
        = (((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I from by push_cast; ring] at hHk
  rw [show ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I).re = -(1/2 : ℝ) from by
        simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
        norm_num] at hHk
  rw [show -(49 / 10) * ((1 - -(1/2 : ℝ)) * Real.log (q : ℝ))
        = -(147 / 20) * Real.log (q : ℝ) from by ring] at hHk
  rw [hnormsq] at hHk
  have hphi : tentPhi (11 / 2) (3 / 10) q ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)
      = Work.LinnikContract.Hk (11 / 2) (3 / 10)
          (((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) * ((Real.log (q : ℝ) : ℝ) : ℂ)) := by
    rw [tentPhi]
    rw [show (1 - ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (q : ℝ) : ℝ) : ℂ)
        = ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) * ((Real.log (q : ℝ) : ℝ) : ℂ) from by
      push_cast; ring]
    rw [tentK_eq_closed _ _ _ hzne, Work.LinnikContract.Hk, Work.LinnikContract.F2]
    ring_nf
  rw [hphi]
  refine hHk.trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos hqpos]
  rw [show Real.log (q : ℝ) * (-(147 : ℝ) / 20) = -(147 : ℝ)/20 * Real.log (q:ℝ) by ring]
  rw [div_eq_mul_inv, mul_comm ((9 / 4 : ℝ) + t ^ 2) ((Real.log (q : ℝ)) ^ 2)]
  ring_nf

end Work.LinnikAreas
