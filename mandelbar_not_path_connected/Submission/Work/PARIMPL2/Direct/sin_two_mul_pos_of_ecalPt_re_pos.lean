import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL2.Direct.ecalPt_re_pos
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Converse monotonicity direction of `ecalPt_re_pos`: on the purely imaginary
parameter line `a = iλ` (`λ > 0`) of the implosion, strict positivity of the real
part of the Écalle point already forces `sin (2 λ Re u) > 0`.

The computation is the same closed form as in `ecalPt_re_pos`,

  `Re ζ(u) = 2 λ · E.im / ‖E − 1‖²`,   `E = e^{2 a u}`,

together with `E.im = e^{−2λ Im u} · sin(2 λ Re u)`.  The hypothesis
`0 < Re ζ(u)` shows in particular `E ≠ 1` (otherwise `ζ(u) = 0`), so the
denominator `‖E − 1‖²` is positive; since `2λ > 0` and `e^{−2λ Im u} > 0`, the
sign of `Re ζ(u)` is exactly the sign of `sin(2 λ Re u)`. -/
theorem sin_two_mul_pos_of_ecalPt_re_pos (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (hpos : 0 < (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re) :
    0 < Real.sin (2 * (lam * u.re)) := by
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  have hposa : 0 < (Work.Implosion.ecalPt a u).re := by rw [ha]; exact hpos
  set θ : ℝ := lam * u.re with hθdef
  set η : ℝ := lam * u.im with hηdef
  -- exponent `2 a u = -2η + 2θ i`
  have hre : (2 * a * u).re = -2 * η := by
    rw [ha, hηdef]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have him : (2 * a * u).im = 2 * θ := by
    rw [ha, hθdef]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  set E : ℂ := Work.Implosion.ecalE a u with hEdef
  have hE : E = Complex.exp (2 * a * u) := by rw [hEdef]; rfl
  have hEim : E.im = Real.exp (-2 * η) * Real.sin (2 * θ) := by
    rw [hE, Complex.exp_im, hre, him]
  -- real and imaginary parts of numerator `a (E + 1)` and denominator `E - 1`
  have hNre : (a * (E + 1)).re = -lam * E.im := by
    rw [ha]; simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hNim : (a * (E + 1)).im = lam * (E.re + 1) := by
    rw [ha]; simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hDre : (E - 1).re = E.re - 1 := by simp
  have hDim : (E - 1).im = E.im := by simp
  -- closed form for the real part
  have hmain : (Work.Implosion.ecalPt a u).re
      = 2 * lam * E.im / Complex.normSq (E - 1) := by
    rw [Work.Implosion.ecalPt, ← hEdef]
    rw [Complex.div_re, hNre, hNim, hDre, hDim]
    ring
  -- the denominator is positive, since `E = 1` would give `ζ(u) = 0`
  have hDpos : 0 < Complex.normSq (E - 1) := by
    rcases lt_trichotomy (Complex.normSq (E - 1)) 0 with h | h | h
    · exact absurd h (not_lt.mpr (Complex.normSq_nonneg _))
    · exfalso
      have hz : (Work.Implosion.ecalPt a u).re = 0 := by rw [hmain, h]; simp
      linarith [hposa, hz]
    · exact h
  have hprod : 0 < 2 * lam * E.im := by
    have h := hposa
    rw [hmain] at h
    have h2 : 0 < (2 * lam * E.im / Complex.normSq (E - 1)) * Complex.normSq (E - 1) :=
      mul_pos h hDpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h2
  have hEimpos : 0 < E.im := by
    have h2lam : 0 < (2 : ℝ) * lam := by linarith
    exact pos_of_mul_pos_right hprod (le_of_lt h2lam)
  have hsinpos : 0 < Real.sin (2 * θ) := by
    have h := hEimpos
    rw [hEim] at h
    exact pos_of_mul_pos_right h (le_of_lt (Real.exp_pos _))
  exact hsinpos

end Work.PARIMPL2.Direct
