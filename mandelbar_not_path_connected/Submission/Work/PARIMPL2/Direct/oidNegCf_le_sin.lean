import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-! ## Size bound for the negative growth coefficient `-C'_j`

`C'_j = oidCf λ cr x y j = -cr·(ζ_j).im / y_j` with
`ζ_j = ecalPt (iλ) (x_j + i y_j)`, and `(ζ_j).im = -λ sinh(λ y_j) cosh(λ y_j)/D_j`,
`D_j = ocDen λ x y j = sin²(λ x_j) + sinh²(λ y_j)`.  Hence

`-C'_j = -cr · λ sinh(λ y_j) cosh(λ y_j) / (D_j y_j)`.

For `cr ≤ 0` this is a nonnegative multiple of the "ratio" `R`, and we prove
`R ≤ λ²/sin²(λ x_j)` whenever `sin(λ x_j) > 0`.  The analytic input is again
`sinh t ≤ t cosh t` together with `cosh² = sinh² + 1` and `sin ≤ 1`.
-/

/-- Numerical core: for `λ > 0`, `0 < s ≤ 1`, `t > 0`.

`λ sinh(λt) cosh(λt) / ((s² + sinh²(λt))·t) ≤ λ²/s²`.

Indeed `sinh(λt) ≤ λt·cosh(λt)` gives
`λ sinh(λt) cosh(λt) ≤ λ² t cosh²(λt) = λ² t (1+sinh²(λt))`, and the factor
`(1+sinh²(λt))/(s²+sinh²(λt)) ≤ 1/s²` because `s² ≤ 1`. -/
private theorem oidSin_core (lam s t : ℝ) (hlam : 0 < lam) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : 0 < t) :
    lam * Real.sinh (lam*t) * Real.cosh (lam*t)
      / ((s^2 + Real.sinh (lam*t)^2) * t) ≤ lam^2 / s^2 := by
  set S := Real.sinh (lam*t) with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact Real.sinh_nonneg_iff.mpr (by positivity)
  have hCsq : Real.cosh (lam*t)^2 = S^2 + 1 := by rw [hSdef]; exact Real.cosh_sq _
  have hkey : S ≤ lam*t*Real.cosh (lam*t) := by
    rw [hSdef]; exact sinh_le_mul_cosh (lam*t) (by positivity)
  have hs2 : 0 < s^2 := by positivity
  have hs21 : s^2 ≤ 1 := by nlinarith [hs, hs1]
  have hDpos : 0 < (s^2 + S^2)*t := by positivity
  rw [div_le_div_iff₀ hDpos hs2]
  have h1 : lam*S*Real.cosh (lam*t)*s^2 ≤ lam^2*t*Real.cosh (lam*t)^2*s^2 := by
    have hh := mul_le_mul_of_nonneg_right hkey
      (by positivity : (0:ℝ) ≤ lam*Real.cosh (lam*t)*s^2)
    nlinarith [hh]
  have h3 : 0 ≤ S^2*(1-s^2) := mul_nonneg (sq_nonneg S) (by linarith)
  have h4 : 0 ≤ lam^2 * t := mul_nonneg (sq_nonneg lam) ht.le
  have h2 : lam^2*t*Real.cosh (lam*t)^2*s^2 ≤ lam^2*((s^2+S^2)*t) := by
    rw [hCsq]
    have h5 : 0 ≤ lam^2*t*(S^2*(1-s^2)) := mul_nonneg h4 h3
    nlinarith [h5]
  linarith [h1, h2]

/-- The ratio appearing in `-oidCf` is bounded by `λ²/sin²(λ x_i)`:

`λ sinh(λ y_i) cosh(λ y_i) / (ocDen λ x y i · y_i) ≤ λ² / sin²(λ x_i)`,

whenever `sin(λ x_i) > 0`.  (No hypothesis on the sign or size of `y_i`: for
`y_i < 0` the two sign changes cancel via `sinh(-t) = -sinh t`.) -/
private theorem oidRat_le_sin (lam : ℝ) (x y : ℕ → ℝ) (i : ℕ) (hlam : 0 < lam)
    (hsin : 0 < Real.sin (lam*x i)) (hD : 0 < ocDen lam x y i) :
    lam * Real.sinh (lam*y i) * Real.cosh (lam*y i) / (ocDen lam x y i * y i)
      ≤ lam^2 / Real.sin (lam*x i)^2 := by
  have hs1 : Real.sin (lam*x i) ≤ 1 := Real.sin_le_one _
  rcases lt_trichotomy (y i) 0 with h | h | h
  · -- `y i < 0`: substitute `t = -y i`
    set t := -(y i) with ht
    have htpos : 0 < t := by rw [ht]; linarith
    have hy : y i = -t := by rw [ht]; ring
    have hsinh : Real.sinh (lam*y i) = -Real.sinh (lam*t) := by
      rw [hy, show lam*(-t) = -(lam*t) by ring, Real.sinh_neg]
    have hcosh : Real.cosh (lam*y i) = Real.cosh (lam*t) := by
      rw [hy, show lam*(-t) = -(lam*t) by ring, Real.cosh_neg]
    have hcore := oidSin_core lam (Real.sin (lam*x i)) t hlam hsin hs1 htpos
    have h1 : lam * Real.sinh (lam*y i) * Real.cosh (lam*y i)
        = -(lam * Real.sinh (lam*t) * Real.cosh (lam*t)) := by
      rw [hsinh, hcosh]; ring
    have h2 : ocDen lam x y i * y i
        = -((Real.sin (lam*x i)^2 + Real.sinh (lam*t)^2)*t) := by
      rw [ocDen, hsinh, hy]; ring
    rw [h1, h2, neg_div_neg_eq]
    exact hcore
  · -- `y i = 0`: both sides reduce, left-hand side is `0`
    rw [h]
    simp only [mul_zero, Real.sinh_zero, zero_mul, zero_div]
    exact div_nonneg (sq_nonneg lam) (sq_nonneg (Real.sin (lam*x i)))
  · -- `y i > 0`: apply the core bound with `t = y i`
    have hcore := oidSin_core lam (Real.sin (lam*x i)) (y i) hlam hsin hs1 h
    simpa [ocDen] using hcore

theorem oidNegCf_le_sin (lam cr : ℝ) (hlam : 0 < lam) (hcr : cr ≤ 0) (n : ℕ) (x y : ℕ → ℝ)
    (i : ℕ) (hi : i < n) (hsin : 0 < Real.sin (lam * x i))
    (hD : 0 < Work.PARIMPL2.Direct.ocDen lam x y i) :
    - Work.PARIMPL2.Direct.oidCf lam cr x y i
      ≤ -cr * lam ^ 2 / Real.sin (lam * x i) ^ 2 := by
  have hR := oidRat_le_sin lam x y i hlam hsin hD
  have hident : -oidCf lam cr x y i
      = -cr * (lam * Real.sinh (lam*y i) * Real.cosh (lam*y i)
          / (ocDen lam x y i * y i)) := by
    rw [oidCf, oidZeta_im]; ring_nf
  rw [hident]
  rw [show -cr * lam ^ 2 / Real.sin (lam * x i) ^ 2
        = -cr * (lam ^ 2 / Real.sin (lam * x i) ^ 2) from by rw [mul_div_assoc]]
  exact mul_le_mul_of_nonneg_left hR (by linarith : (0:ℝ) ≤ -cr)

end Work.PARIMPL2.Direct
