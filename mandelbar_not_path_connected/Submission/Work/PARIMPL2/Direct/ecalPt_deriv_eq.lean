import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL2.Direct.inbound_bounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

/-- For `0 < lam * w.re < π` the complex sine `sin (lam * w)` does not vanish:
its real part is `sin (lam * w.re) * cosh (lam * w.im) > 0`. -/
private theorem sin_ne_zero_of_lam_re (lam : ℝ) (w : ℂ)
    (h1 : 0 < lam * w.re) (h2 : lam * w.re < Real.pi) :
    Complex.sin ((lam : ℂ) * w) ≠ 0 := by
  set z : ℂ := (lam : ℂ) * w with hz
  have hzre : z.re = lam * w.re := by rw [hz]; simp
  have hsinpos : 0 < Real.sin z.re :=
    Real.sin_pos_of_pos_of_lt_pi (by rw [hzre]; exact h1) (by rw [hzre]; exact h2)
  have hcoshpos : 0 < Real.cosh z.im := Real.cosh_pos z.im
  have hre : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    have hs1 : Complex.sin (↑z.re : ℂ) = ↑(Real.sin z.re) := (Complex.ofReal_sin z.re).symm
    have hc1 : Complex.cosh (↑z.im : ℂ) = ↑(Real.cosh z.im) := (Complex.ofReal_cosh z.im).symm
    have hs2 : Complex.cos (↑z.re : ℂ) = ↑(Real.cos z.re) := (Complex.ofReal_cos z.re).symm
    have hc2 : Complex.sinh (↑z.im : ℂ) = ↑(Real.sinh z.im) := (Complex.ofReal_sinh z.im).symm
    rw [Complex.sin_eq, hs1, hc1, hs2, hc2]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  intro h
  have hz0 : (Complex.sin z).re = 0 := by rw [h]; simp
  rw [hre] at hz0
  exact (ne_of_gt (mul_pos hsinpos hcoshpos)) hz0

/-- The multiplier coordinate `e^{2az}` at `a = i·lam` avoids the value `1` whenever
`sin (lam * w) ≠ 0`, because `e^{2 i z} - 1 = e^{i z} (e^{i z} - e^{-i z})` and
`e^{i z} - e^{-i z} = 2 i sin z`. -/
private theorem ecalE_ne_one_of_sin_ne (lam : ℝ) (w : ℂ)
    (hsin : Complex.sin ((lam : ℂ) * w) ≠ 0) :
    Work.Implosion.ecalE ((lam : ℂ) * Complex.I) w ≠ 1 := by
  set z : ℂ := (lam : ℂ) * w with hz
  have hEeq : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) w =
      Complex.exp (2 * (z * Complex.I)) := by
    rw [Work.Implosion.ecalE, hz]; congr 1; ring
  rw [hEeq]
  have hsinz : Complex.sin z ≠ 0 := by rw [hz]; exact hsin
  intro h
  have hexp_sub : Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) =
      2 * Complex.sin z * Complex.I := by
    have e1 : Complex.exp (z * Complex.I) = Complex.cos z + Complex.sin z * Complex.I :=
      (Complex.cos_add_sin_I z).symm
    have e2 : Complex.exp (-(z * Complex.I)) = Complex.cos z - Complex.sin z * Complex.I := by
      rw [show -(z * Complex.I) = -z * Complex.I by ring, Complex.cos_sub_sin_I]
    rw [e1, e2]; ring
  have hone : Complex.exp (z * Complex.I) * Complex.exp (-(z * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hfac : Complex.exp (z * Complex.I) ^ 2 - 1 =
      Complex.exp (z * Complex.I) * (2 * Complex.sin z * Complex.I) := by
    rw [← hone, ← hexp_sub]; ring
  have h2 : Complex.exp (2 * (z * Complex.I)) = Complex.exp (z * Complex.I) ^ 2 := by
    simpa using Complex.exp_nat_mul (z * Complex.I) 2
  rw [h2] at h
  have hzero : Complex.exp (z * Complex.I) * (2 * Complex.sin z * Complex.I) = 0 := by
    rw [← hfac, h]; ring
  rcases mul_eq_zero.mp hzero with h3 | h3
  · exact Complex.exp_ne_zero _ h3
  · obtain h4 | h4 := mul_eq_zero.mp h3
    · obtain h5 | h5 := mul_eq_zero.mp h4
      · norm_num at h5
      · exact hsinz h5
    · exact Complex.I_ne_zero h4

/-- `ecalPt` at `a = i·lam` is `lam · cos(lam w) / sin(lam w)`. -/
private theorem ecalPt_eq_lam_mul_cos_div_sin (lam : ℝ) (w : ℂ)
    (hE1 : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) w ≠ 1) :
    Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) w =
      (lam : ℂ) * Complex.cos ((lam : ℂ) * w) / Complex.sin ((lam : ℂ) * w) := by
  set z : ℂ := (lam : ℂ) * w with hz
  rw [Work.Implosion.Ecalle.ecallePt_eq_coth _ _ hE1]
  have haw : ((lam : ℂ) * Complex.I) * w = z * Complex.I := by rw [hz]; ring
  rw [haw, Work.Implosion.coth, Complex.cosh_mul_I, Complex.sinh_mul_I]
  field_simp

theorem ecalPt_deriv_eq (lam : ℝ) (hlam : 0 < lam) (w : ℂ)
    (h1 : 0 < lam * w.re) (h2 : lam * w.re < Real.pi) :
    deriv (fun z : ℂ => Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) z)
      w = -(((lam : ℂ) ^ 2) / (Complex.sin ((lam : ℂ) * w)) ^ 2) := by
  have hsin : Complex.sin ((lam : ℂ) * w) ≠ 0 := sin_ne_zero_of_lam_re lam w h1 h2
  have hE1 : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) w ≠ 1 :=
    ecalE_ne_one_of_sin_ne lam w hsin
  have hd := Work.Implosion.Ecalle.ecallePt_hasDerivAt ((lam : ℂ) * Complex.I) w hE1
  have hpt : Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) w =
      (lam : ℂ) * Complex.cos ((lam : ℂ) * w) / Complex.sin ((lam : ℂ) * w) :=
    ecalPt_eq_lam_mul_cos_div_sin lam w hE1
  rw [show (fun z : ℂ => Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) z) =
        Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) from rfl]
  rw [hd.deriv, hpt]
  field_simp
  have hI : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
  rw [hI]
  linear_combination (-((lam : ℂ) ^ 2)) * Complex.sin_sq_add_cos_sq ((lam : ℂ) * w)

end Work.PARIMPL2.Direct
