/-
# The `ε^{-q}`-weighted Hardy inequality with boundary term on `[a,b]`

`Work.FTS.EllipticEst.H2W.hardy_boundary_clean`: for `0 ≤ q < 1`, `0 < a ≤ b` and `U` of class
`C¹` on `[a,b]`,

  `(1+q)^2/4 * ∫_a^b U^2 ε^{-(2+q)}
        ≤ (∫_a^b (U')^2 ε^{-q}) - (1+q)/2 * (U(b)^2 b^{-(1+q)} - U(a)^2 a^{-(1+q)})`.

This is the classical Hardy inequality with boundary term, in its sharp form: the constant
`4/(1+q)^2` is optimal (the power model `U(ε) = ε^((1+q)/2)` saturates it asymptotically).  The
proof is the pointwise completion of squares

  `ε^{-q} (U' - (1+q)/2 * U/ε)^2
      = (U')^2 ε^{-q} - (1+q)/2 * (2 U U' ε^{-(1+q)} - (1+q) U^2 ε^{-(2+q)})
        - ((1+q)/2)^2 * U^2 ε^{-(2+q)}`

integrated over `a..b` against the fundamental theorem of calculus for the flux
`ε ↦ U ε^2 * ε^{-(1+q)}` (whose derivative is the bracket in the middle of the identity).  The
square integrates to a nonnegative quantity, and moving the boundary term to the other side
gives the estimate.

Integrability bookkeeping: `deriv U` is only available on the open interval, so on `(a,b)` it is
replaced by the continuous `derivWithin U (Icc a b)` (a.e. equal on `uIoo a b`,
`IntervalIntegrable.congr_uIoo`); no smoothness beyond `ContDiffOn ℝ 1` on the closed interval is
used.  The hypotheses `0 ≤ q` and `q < 1` are not needed by this lemma itself (they matter for
the neighbouring estimates) — the inequality holds for every real `q` with `1 + q ≠ 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set intervalIntegral

namespace Work.FTS.EllipticEst.H2W

/-- Pointwise completion of squares for the `ε^{-q}`-weighted Hardy inequality: for `ε > 0`,

`ε^{-q} (u' - (1+q)/2 * u/ε)^2 = u'^2 ε^{-q}
      - (1+q)/2 (2 u u' ε^{-(1+q)} - (1+q) u^2 ε^{-(2+q)}) - ((1+q)/2)^2 u^2 ε^{-(2+q)}`. -/
private theorem hardyClean_sq_expand {q ε u u' : ℝ} (hε : 0 < ε) :
    ε ^ (-q) * (u' - (1 + q) / 2 * u / ε) ^ 2
      = u' ^ 2 * ε ^ (-q)
        - (1 + q) / 2 * (2 * u * u' * ε ^ (-(1 + q)) - (1 + q) * u ^ 2 * ε ^ (-(2 + q)))
        - ((1 + q) / 2) ^ 2 * (u ^ 2 * ε ^ (-(2 + q))) := by
  have h1 : ε ^ (-(1 + q)) = ε ^ (-q) * ε ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  have h2 : ε ^ (-(2 + q)) = ε ^ (-q) * ε ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  rw [h1, h2, Real.rpow_neg_one, Real.rpow_neg hε.le 2, Real.rpow_two]
  field_simp
  ring

/-- Derivative of the flux `ε ↦ U ε ^ 2 * ε ^ (-(1 + q))` (for `U` differentiable at `x > 0`). -/
private theorem hasDerivAt_hardyClean_flux {q x : ℝ} {U : ℝ → ℝ} (hx : 0 < x)
    (hU : HasDerivAt U (deriv U x) x) :
    HasDerivAt (fun ε => U ε ^ 2 * ε ^ (-(1 + q)))
      (2 * U x * deriv U x * x ^ (-(1 + q)) - (1 + q) * U x ^ 2 * x ^ (-(2 + q))) x := by
  have h2 : HasDerivAt (fun ε => U ε ^ 2) (2 * U x * deriv U x) x := by
    have h := hU.pow 2
    have hfun : (U ^ 2) = fun ε => U ε ^ 2 := by funext ε; simp
    rw [hfun] at h
    simpa using h
  have hw : HasDerivAt (fun ε : ℝ => ε ^ (-(1 + q))) ((-(1 + q)) * x ^ (-(1 + q) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hm := h2.mul hw
  have h3 : x ^ (-(1 + q) - 1) = x ^ (-(2 + q)) := by congr 1; ring
  rw [h3] at hm
  convert hm using 1
  ring

/-- **Weighted Hardy inequality with boundary term.**

For `0 ≤ q < 1`, `0 < a ≤ b` and `U` of class `C¹` on `[a,b]`:

`(1+q)^2/4 * ∫_a^b U^2 ε^{-(2+q)}
    ≤ (∫_a^b (U')^2 ε^{-q}) - (1+q)/2 * (U(b)^2 b^{-(1+q)} - U(a)^2 a^{-(1+q)})`.

Proved by integrating the pointwise completion of squares `hardyClean_sq_expand` and applying
the fundamental theorem of calculus to the flux `ε ↦ U ε^2 * ε^{-(1+q)}` (see
`hasDerivAt_hardyClean_flux`). -/
theorem hardy_boundary_clean {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {U : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b)
    (hU : ContDiffOn ℝ 1 U (Set.Icc a b)) :
    (1 + q) ^ 2 / 4 * (∫ ε in a..b, U ε ^ 2 * ε ^ (-(2 + q)))
      ≤ (∫ ε in a..b, (deriv U ε) ^ 2 * ε ^ (-q))
        - (1 + q) / 2 * (U b ^ 2 * b ^ (-(1 + q)) - U a ^ 2 * a ^ (-(1 + q))) := by
  rcases hab.eq_or_lt with rfl | hablt
  · simp
  have hUcont : ContinuousOn U (Icc a b) := hU.continuousOn
  set dU : ℝ → ℝ := derivWithin U (Icc a b) with hdU
  have hdUcont : ContinuousOn dU (Icc a b) :=
    hU.continuousOn_derivWithin (uniqueDiffOn_Icc hablt) le_rfl
  have hUderiv : ∀ x ∈ Ioo a b, HasDerivAt U (deriv U x) x := by
    intro x hx
    exact ((hU.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt one_ne_zero).hasDerivAt
  have hpowq : ContinuousOn (fun ε : ℝ => ε ^ (-q)) (Icc a b) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
  have hpow1 : ContinuousOn (fun ε : ℝ => ε ^ (-(1 + q))) (Icc a b) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
  have hpow2 : ContinuousOn (fun ε : ℝ => ε ^ (-(2 + q))) (Icc a b) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
  set F : ℝ → ℝ := fun ε => (deriv U ε) ^ 2 * ε ^ (-q) with hF
  set φ : ℝ → ℝ := fun ε => 2 * U ε * deriv U ε * ε ^ (-(1 + q))
      - (1 + q) * U ε ^ 2 * ε ^ (-(2 + q)) with hφ
  set H : ℝ → ℝ := fun ε => U ε ^ 2 * ε ^ (-(2 + q)) with hH
  set g : ℝ → ℝ := fun ε => U ε ^ 2 * ε ^ (-(1 + q)) with hg
  have hdx : ∀ x ∈ Ioo a b, deriv U x = dU x := by
    intro x hx
    rw [hdU]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm
  have hintF : IntervalIntegrable F volume a b := by
    have hcont : ContinuousOn (fun ε => dU ε ^ 2 * ε ^ (-q)) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact (hdUcont.pow 2).mul hpowq
    refine hcont.intervalIntegrable.congr_uIoo ?_
    intro x hx
    rw [uIoo_of_le hab] at hx
    simp only [hF, hdx x hx]
  have hintφ : IntervalIntegrable φ volume a b := by
    have hcont : ContinuousOn (fun ε => 2 * U ε * dU ε * ε ^ (-(1 + q))
        - (1 + q) * U ε ^ 2 * ε ^ (-(2 + q))) (uIcc a b) := by
      rw [uIcc_of_le hab]
      refine ContinuousOn.sub ?_ ?_
      · exact (((continuousOn_const.mul hUcont).mul hdUcont).mul hpow1)
      · exact (continuousOn_const.mul (hUcont.pow 2)).mul hpow2
    refine hcont.intervalIntegrable.congr_uIoo ?_
    intro x hx
    rw [uIoo_of_le hab] at hx
    simp only [hφ, hdx x hx]
  have hintH : IntervalIntegrable H volume a b := by
    have hcont : ContinuousOn (fun ε => U ε ^ 2 * ε ^ (-(2 + q))) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact (hUcont.pow 2).mul hpow2
    exact hcont.intervalIntegrable.congr_uIoo (fun x _ => by simp only [hH])
  have hgcont : ContinuousOn g (Icc a b) := by
    rw [hg]
    exact (hUcont.pow 2).mul hpow1
  have hgderiv : ∀ x ∈ Ioo a b, HasDerivAt g (φ x) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans ha hx.1
    have h := hasDerivAt_hardyClean_flux (q := q) hxpos (hUderiv x hx)
    rw [hg, hφ]
    exact h
  have hFTC : ∫ ε in a..b, φ ε = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hgcont hgderiv hintφ
  have hsq : ∫ ε in a..b, ε ^ (-q) * (deriv U ε - (1 + q) / 2 * U ε / ε) ^ 2
      = (∫ ε in a..b, F ε) - (1 + q) / 2 * (∫ ε in a..b, φ ε)
        - ((1 + q) / 2) ^ 2 * (∫ ε in a..b, H ε) := by
    have hcongr : ∫ ε in a..b, ε ^ (-q) * (deriv U ε - (1 + q) / 2 * U ε / ε) ^ 2
        = ∫ ε in a..b, (F ε - (1 + q) / 2 * φ ε - ((1 + q) / 2) ^ 2 * H ε) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [uIoo_of_le hab] at hx
      have hxpos : 0 < x := lt_trans ha hx.1
      simp only [hF, hφ, hH]
      exact hardyClean_sq_expand (q := q) hxpos
    rw [hcongr]
    have h1 : ∫ ε in a..b, (F ε - (1 + q) / 2 * φ ε - ((1 + q) / 2) ^ 2 * H ε)
        = (∫ ε in a..b, (F ε - (1 + q) / 2 * φ ε))
          - ((1 + q) / 2) ^ 2 * (∫ ε in a..b, H ε) := by
      rw [intervalIntegral.integral_sub (hintF.sub (hintφ.const_mul ((1 + q) / 2)))
            (hintH.const_mul (((1 + q) / 2) ^ 2)), intervalIntegral.integral_const_mul]
    have h2 : ∫ ε in a..b, (F ε - (1 + q) / 2 * φ ε)
        = (∫ ε in a..b, F ε) - (1 + q) / 2 * (∫ ε in a..b, φ ε) := by
      rw [intervalIntegral.integral_sub hintF (hintφ.const_mul ((1 + q) / 2)),
          intervalIntegral.integral_const_mul]
    rw [h1, h2]
  have hnn : 0 ≤ ∫ ε in a..b, ε ^ (-q) * (deriv U ε - (1 + q) / 2 * U ε / ε) ^ 2 := by
    refine intervalIntegral.integral_nonneg hab ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    exact mul_nonneg (Real.rpow_nonneg hxpos.le _) (sq_nonneg _)
  have hkey : 0 ≤ (∫ ε in a..b, F ε) - (1 + q) / 2 * (∫ ε in a..b, φ ε)
      - ((1 + q) / 2) ^ 2 * (∫ ε in a..b, H ε) := by
    rw [← hsq]; exact hnn
  have hfinal : ((1 + q) / 2) ^ 2 * (∫ ε in a..b, H ε)
      ≤ (∫ ε in a..b, F ε) - (1 + q) / 2 * (g b - g a) := by
    have h := hkey
    rw [hFTC] at h
    linarith
  have hcoef : ((1 + q) / 2) ^ 2 = (1 + q) ^ 2 / 4 := by ring
  rw [hcoef] at hfinal
  simpa only [hF, hH, hg] using hfinal

end Work.FTS.EllipticEst.H2W
