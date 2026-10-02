import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.log_sinh_modelDisp_sub

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The one-step bounds of the model displacement on the whole transit strip

`Work.PARIMPL2.Direct.modelDisp_step_bounds2` — the (E2) estimate of
`PARIMPL2/Lavaurs/NOTES_LEAD_transit_exit_direct_S2.md` §3.3, on the *whole* strip
`R/4 + 2 ≤ Re u ≤ π/λ - R/4` (not only its left half `u.re < π/(2λ)`):

for `a = iλ`, `ζ = ecalPt a u`, `Φ = modelDisp a h u`, `κ = τ - h1/τ`,

* `-2 ≤ Re Φ ≤ -1/3` and `|Im Φ| ≤ 2` (the second-order expansion
  `Φ + h(ζ) - ζ h(ζ)² = O(‖ζ‖² + λ²)` of `Implosion/Approx/modelDisp_second_order`);
* `-2 ≤ Re (Ũ(u+Φ) - Ũ(u)) ≤ -1/4` for the approximate perturbed Fatou coordinate
  `Ũ = approxEcal a κ` (the step is `-1` up to `O(1/R)`);
* the whole segment `u + [0,1]Φ` lies in the slit plane (so the principal logarithm
  of the construction never jumps).

The proof of the second item is exact-algebra first: from the logarithmic identity
`log Z(u+Φ) - log Z(u) = -aΦ - log(1+A₂)` (`Direct.log_sinh_modelDisp_sub`) one gets

  `Ũ(u+Φ) - Ũ(u) + τ = S + (1-κa)(Φ + h(ζ) - ζh(ζ)²) - κ(log(1+A₂) - A₂)`,

with `S = τ - (1-κa)h(ζ) + (1-κa)ζh(ζ)² - κ(ζ+a)h(ζ)`, and the algebraic rewrite
`S = -e + ζw(τ + h1/τ) + ζw² - κaζh(ζ)²` (`e = h(ζ) - τ - h1ζ`, `w = h1ζ + e`) whose
first two terms cancel the linear part.  Every remaining term is then `O(1/R)` and the
final bookkeeping is the real-arithmetic lemma `step_arith`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

namespace Work.PARIMPL2.Direct

open Complex

/-- The exact algebraic rewrite of the constant term `S` of the one-step decomposition:
with `κ = τ - h1/τ` the combination `τ - (1-κa)x + (1-κa)ζx² - κ(ζ+a)x` at
`x = τ + h1ζ + e` equals `-e + ζw(τ + h1/τ) + ζw² - κaζx²` with `w = h1ζ + e`.
The cancellation `-w + ζh1`, i.e. `-e`, is what kills the linear term of the step. -/
private lemma step_S_ident (a τ h1 κ ζ e : ℂ) (hκ : κ = τ - h1 / τ) (hτ : τ ≠ 0) :
    τ - (1 - κ*a)*(τ + h1*ζ + e) + (1 - κ*a)*ζ*(τ + h1*ζ + e)^2 - κ*(ζ+a)*(τ + h1*ζ + e)
      = -e + ζ*(h1*ζ+e)*(τ + h1/τ) + ζ*(h1*ζ+e)^2 - κ*a*ζ*(τ+h1*ζ+e)^2 := by
  have h2 : τ * (τ - (1 - κ*a)*(τ + h1*ζ + e) + (1 - κ*a)*ζ*(τ + h1*ζ + e)^2
        - κ*(ζ+a)*(τ + h1*ζ + e))
      = τ * (-e + ζ*(h1*ζ+e)*(τ + h1/τ) + ζ*(h1*ζ+e)^2 - κ*a*ζ*(τ+h1*ζ+e)^2) := by
    rw [hκ]; field_simp; ring
  exact mul_left_cancel₀ hτ h2

/-- **The real-arithmetic bookkeeping of the step.**  For `R ≥ 128` the four error terms
of the one-step estimate are bounded by `1/4`; together with the `3/8` coming from the
quadratic germ remainder this is the `5/8` of the step.  Each individual term is `O(1/R)`:
`3/64`, `9/2048`, `1/200`, `1/30`, `1/200` at `R = 128`, and `3/8 + 1/4 < 5/8`. -/
private lemma step_arith (R : ℝ) (hR : 128 ≤ R) :
    (4/R)*(3/8)*(2 + R/64) + (4/R)*(9/64) + (R/64)*(1/R^2)*(4/R)*(121/64)
      + (1 + (R/64)*(1/R^2))*32*((4/R)^2 + (1/R^2)^2)
      + (R/64)*(((4/R) + (1/R^2))*(11/8))^2 ≤ 1/4 := by
  have hR0 : (0:ℝ) < R := by linarith
  have hR2 : (16384:ℝ) ≤ R^2 := by nlinarith only [hR]
  have hR4 : (16384:ℝ)^2 ≤ R^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 16384) hR2 2
    have h' : (R^2)^2 = R^4 := by ring
    rwa [h'] at h
  have e1 : (4/R)*(3/8)*(2 + R/64) ≤ 3/64 := by
    have hid : (4/R)*(3/8)*(2 + R/64) = 3/R + 3/128 := by field_simp <;> ring
    rw [hid]
    have h : 3/R ≤ 3/128 := by rw [div_le_iff₀ hR0]; linarith
    linarith
  have e2 : (4/R)*(9/64) ≤ 9/2048 := by
    have hid : (4/R)*(9/64) = 9/(16*R) := by field_simp <;> ring
    rw [hid]
    have h : 9/(16*R) ≤ 9/(16*128) := div_le_div₀ (by norm_num) le_rfl (by positivity) (by linarith)
    have h2 : (9:ℝ)/(16*128) = 9/2048 := by norm_num
    linarith
  have e3 : (R/64)*(1/R^2)*(4/R)*(121/64) ≤ 1/200 := by
    have hid : (R/64)*(1/R^2)*(4/R)*(121/64) = 121/(1024*R^2) := by field_simp <;> ring
    rw [hid]
    have h : 121/(1024*R^2) ≤ 121/(1024*16384) :=
      div_le_div₀ (by norm_num) le_rfl (by positivity) (by linarith)
    have h2 : (121:ℝ)/(1024*16384) ≤ 1/200 := by norm_num
    linarith
  have e4 : (1 + (R/64)*(1/R^2))*32*((4/R)^2 + (1/R^2)^2) ≤ 1/30 := by
    have hid1 : (R/64)*(1/R^2) = 1/(64*R) := by field_simp <;> ring
    have hid2 : (4/R)^2 = 16/R^2 := by field_simp <;> ring
    have hid3 : (1/R^2)^2 = 1/R^4 := by field_simp <;> ring
    rw [hid1, hid2, hid3]
    have h1 : 1/(64*R) ≤ 1/(64*128) := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : 16/R^2 ≤ 16/16384 := div_le_div₀ (by norm_num) le_rfl (by positivity) hR2
    have h3 : 1/R^4 ≤ 1/(16384^2) := one_div_le_one_div_of_le (by norm_num) hR4
    have hA : (0:ℝ) ≤ 1 + 1/(64*R) := by positivity
    have hB : (0:ℝ) ≤ 16/R^2 + 1/R^4 := by positivity
    have hAB : 1 + 1/(64*R) ≤ 1 + 1/(64*128) := by linarith
    have hCD : 16/R^2 + 1/R^4 ≤ 16/16384 + 1/(16384^2) := by linarith
    have hstep : (1 + 1/(64*R))*32*(16/R^2 + 1/R^4)
        ≤ (1 + 1/(64*128))*32*(16/16384 + 1/(16384^2)) := by
      calc (1 + 1/(64*R))*32*(16/R^2 + 1/R^4)
          = ((1 + 1/(64*R))*32)*(16/R^2 + 1/R^4) := by ring
        _ ≤ ((1 + 1/(64*128))*32)*(16/16384 + 1/(16384^2)) :=
              mul_le_mul (mul_le_mul hAB le_rfl (by norm_num) (by positivity)) hCD hB (by positivity)
        _ = (1 + 1/(64*128))*32*(16/16384 + 1/(16384^2)) := by ring
    have h5 : (1 + (1:ℝ)/(64*128))*32*(16/16384 + 1/(16384^2)) ≤ 1/30 := by norm_num
    linarith
  have e5 : (R/64)*(((4/R) + (1/R^2))*(11/8))^2 ≤ 1/200 := by
    have hid : (R/64)*(((4/R) + (1/R^2))*(11/8))^2 = (121/(256*R))*(1 + 1/(4*R))^2 := by
      field_simp <;> ring
    rw [hid]
    have h1 : 121/(256*R) ≤ 121/(256*128) := div_le_div₀ (by norm_num) le_rfl (by positivity) (by linarith)
    have h2 : 1/(4*R) ≤ 1/(4*128) := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h3 : (1 + 1/(4*R))^2 ≤ (1 + 1/(4*128))^2 := by
      have hA : (0:ℝ) ≤ 1 + 1/(4*R) := by positivity
      have hB : 1 + 1/(4*R) ≤ 1 + 1/(4*128) := by linarith
      nlinarith only [hA, hB]
    have h4 : (121/(256*R))*(1 + 1/(4*R))^2 ≤ (121/(256*128))*(1 + 1/(4*128))^2 :=
      mul_le_mul h1 h3 (by positivity) (by positivity)
    have h5 : (121/(256*128))*(1 + 1/(4*128))^2 ≤ 1/200 := by norm_num
    linarith
  linarith only [e1, e2, e3, e4, e5]

/-- The step estimate `‖Ũ(u+Φ) - Ũ(u) + τ‖ ≤ 5/8` under the hypotheses of
`modelDisp_step_bounds2` and the two bounds on `Re Φ`. -/
private lemma approxEcal_step_le_aux (lam R B : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hB0 : 0 ≤ B)
    (h : ℂ → ℂ) (τ h1 κ : ℂ) (A r : ℝ) (hA : 0 ≤ A)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hκ : κ = τ - h1/τ)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hκR : 64 * ‖κ‖ ≤ R)
    (u : ℂ) (hx1 : R / 4 + 2 ≤ u.re) (hx2 : u.re ≤ Real.pi / lam - R / 4)
    (hζn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hζr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r)
    (hΦlo : (-2 : ℝ) ≤ (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re)
    (hΦhi : (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ≤ -(1 / 3)) :
    ‖Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ
        (u + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u)
      - Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u + τ‖ ≤ 5 / 8 := by
  have hR0 : 0 < R := by linarith
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζdef
  set Φ : ℂ := Work.Implosion.modelDisp a h u with hΦdef
  set hz : ℂ := h ζ with hhzdef
  have hna : ‖a‖ = lam := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact abs_of_pos hlam
  have hane : a ≠ 0 := by
    rw [ha]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hζn' : ‖ζ‖ ≤ 4 / R := hζn
  have hζr' : ‖ζ‖ < r := hζr
  have hlamR0 : lam ≤ 1 / R ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < R ^ 2)]; linarith only [hlamR]
  have hζ2 : ‖ζ‖ ^ 2 ≤ 16 / R ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
    have h2 : (4 / R) ^ 2 = 16 / R ^ 2 := by field_simp <;> ring
    nlinarith only [hζn', h0, h2]
  have h4 : 4 * (‖ζ‖ + ‖a‖) ≤ 1 := by
    rw [hna]
    have hd1 : (4:ℝ)/R ≤ 4/128 := div_le_div₀ (by norm_num) le_rfl (by norm_num) hR
    have hd2 : (1:ℝ)/R^2 ≤ 1/16384 := by
      apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16384); nlinarith only [hR]
    nlinarith only [hζn', hlamR0, hd1, hd2]
  have hτnorm : ‖τ‖ = 1 := hb.2.1
  have hτ_ne : τ ≠ 0 := by
    intro h0
    have h1' : ‖τ‖ = 0 := by rw [h0, norm_zero]
    rw [hτnorm] at h1'; norm_num at h1'
  have hζr_le : ‖hz - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 := by
    have hh := hb.2.2.1 ζ hζr'; simpa [hhzdef] using hh
  have hρ : ‖hz - τ‖ ≤ 3 / 8 := by
    have heq : hz - τ = (hz - τ - h1 * ζ) + h1 * ζ := by ring
    have hd1 : ‖hz - τ‖ ≤ ‖hz - τ - h1 * ζ‖ + ‖h1 * ζ‖ := by
      nth_rewrite 1 [heq]; exact norm_add_le _ _
    rw [norm_mul] at hd1
    have hd2 : ‖h1‖ * ‖ζ‖ ≤ B * (4 / R) := mul_le_mul hh1 hζn' (norm_nonneg _) hB0
    have hd3 : A * ‖ζ‖ ^ 2 ≤ A * (16 / R ^ 2) := mul_le_mul_of_nonneg_left hζ2 hA
    have hd4 : B * (4 / R) + A * (16 / R ^ 2) = 4 * B / R + 16 * A / R ^ 2 := by ring
    linarith only [hd1, hd2, hd3, hd4, hAr, hζr_le]
  have hhz_le : ‖hz‖ ≤ 11 / 8 := by
    have heq : ‖hz‖ = ‖τ + (hz - τ)‖ := by congr 1; ring
    have hd1 : ‖hz‖ ≤ ‖τ‖ + ‖hz - τ‖ := by rw [heq]; exact norm_add_le τ (hz - τ)
    rw [hτnorm] at hd1; linarith only [hd1, hρ]
  have hhz2 : ‖hz‖ ≤ 2 := by linarith only [hhz_le]
  have hso : ‖Φ + hz - ζ * hz ^ 2‖ ≤ 32 * (‖ζ‖ ^ 2 + lam ^ 2) := by
    have hh := Work.Implosion.Approx.modelDisp_second_order a h u hane h4 hhz2
    have h' : ‖Φ + hz - ζ * hz ^ 2‖ ≤ 32 * (‖ζ‖ ^ 2 + ‖a‖ ^ 2) := by
      simpa [hΦdef, hζdef, hhzdef] using hh
    rwa [hna] at h'
  have hκle : ‖κ‖ ≤ R / 64 := by linarith only [hκR]
  have hσ32 : ‖ζ‖ ≤ 1 / 32 := by
    have hd : (4:ℝ) / R ≤ 4 / 128 := div_le_div₀ (by norm_num) le_rfl (by norm_num) hR
    linarith
  have hlam2 : lam ≤ 1 / 16384 := by
    have hd : (1:ℝ) / R ^ 2 ≤ 1 / 16384 := by
      apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16384); nlinarith only [hR]
    linarith only [hlamR0, hd]
  have hh1le : ‖h1‖ ≤ 1 + R / 64 := by
    have heq : h1 = τ * (τ - κ) := by rw [hκ]; field_simp <;> ring
    rw [heq, norm_mul, hτnorm, one_mul]
    have h2 : ‖τ - κ‖ ≤ 1 + ‖κ‖ := by
      calc ‖τ - κ‖ ≤ ‖τ‖ + ‖κ‖ := norm_sub_le τ κ
        _ = 1 + ‖κ‖ := by rw [hτnorm]
    linarith only [h2, hκle]
  have hcv : 32 * (‖ζ‖^2 + lam^2) + ‖ζ‖ * ‖hz‖^2 ≤ 1/6 := by
    have hstep1 : ‖ζ‖ * ‖hz‖^2 ≤ (1/32) * (11/8)^2 := by
      have h0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
      have h1 : ‖hz‖^2 ≤ (11/8)^2 := by nlinarith only [hhz_le, norm_nonneg hz]
      nlinarith only [hσ32, h1, h0]
    have hstep2 : 32 * (‖ζ‖^2 + lam^2) ≤ 32 * ((1/32)^2 + (1/16384)^2) := by
      have h0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
      have h1 : ‖ζ‖^2 ≤ (1/32)^2 := by nlinarith only [hσ32, h0]
      have h2 : lam^2 ≤ (1/16384)^2 := by nlinarith only [hlam2, le_of_lt hlam]
      linarith
    nlinarith only [hstep1, hstep2]
  have hΦn : ‖Φ‖ ≤ 11 / 8 + 1 / 6 := by
    have heq : Φ = (Φ + hz - ζ * hz ^ 2) - hz + ζ * hz ^ 2 := by ring
    have htri : ‖Φ‖ ≤ ‖Φ + hz - ζ * hz ^ 2‖ + ‖hz‖ + ‖ζ * hz ^ 2‖ := by
      calc ‖Φ‖ = ‖(Φ + hz - ζ*hz^2) - hz + ζ*hz^2‖ := by rw [← heq]
        _ ≤ ‖(Φ + hz - ζ*hz^2) - hz‖ + ‖ζ*hz^2‖ := norm_add_le _ _
        _ ≤ (‖Φ + hz - ζ*hz^2‖ + ‖hz‖) + ‖ζ*hz^2‖ := by
              have hh := norm_sub_le (Φ + hz - ζ*hz^2) hz; linarith
    have hζhz : ‖ζ * hz^2‖ ≤ ‖ζ‖ * ‖hz‖^2 := by rw [norm_mul, norm_pow]
    linarith only [htri, hso, hζhz, hcv, hhz_le]
  have hε : ‖a * Φ‖ < Real.pi / 2 := by
    rw [norm_mul, hna]
    have hlt : lam * (11/8 + 1/6) < Real.pi / 2 := by
      nlinarith only [hlam2, le_of_lt hlam, Real.pi_gt_three]
    nlinarith only [hΦn, le_of_lt hlam, hlt]
  have hW0 : 0 < (Complex.sinh (a * u) / a).re := by
    have hv1 : R / 4 ≤ u.re := by linarith
    have hh := Work.Implosion.Approx.sinh_mul_I_div_re_pos lam (R/4) hlam (by linarith) u hv1 hx2
    rwa [← ha] at hh
  have hW1 : 0 < (Complex.sinh (a * (u + Φ)) / a).re := by
    have hv1 : R / 4 ≤ (u + Φ).re := by rw [Complex.add_re]; linarith
    have hv2 : (u + Φ).re ≤ Real.pi / lam - R / 4 := by rw [Complex.add_re]; linarith
    have hh := Work.Implosion.Approx.sinh_mul_I_div_re_pos lam (R/4) hlam (by linarith) (u + Φ) hv1 hv2
    rwa [← ha] at hh
  have hdisp1 : ‖Work.Implosion.dispNum1 a h u‖ ≤ (4/R + 1/R^2) * (11/8) := by
    have heq : Work.Implosion.dispNum1 a h u = (ζ - a) * hz := by
      simp only [Work.Implosion.dispNum1, hhzdef, hζdef]
    rw [heq, norm_mul]
    have h1 : ‖ζ - a‖ ≤ 4/R + lam := by
      have hh := norm_sub_le ζ a; rw [hna] at hh; linarith only [hh, hζn']
    calc ‖ζ - a‖ * ‖hz‖ ≤ (4/R + lam) * (11/8) :=
          mul_le_mul h1 hhz_le (norm_nonneg _) (by positivity)
      _ ≤ (4/R + 1/R^2) * (11/8) := by nlinarith only [hlamR0]
  have hdisp2 : ‖Work.Implosion.dispNum2 a h u‖ ≤ (4/R + 1/R^2) * (11/8) := by
    have heq : Work.Implosion.dispNum2 a h u = (ζ + a) * hz := by
      simp only [Work.Implosion.dispNum2, hhzdef, hζdef]
    rw [heq, norm_mul]
    have h1 : ‖ζ + a‖ ≤ 4/R + lam := by
      have hh := norm_add_le ζ a; rw [hna] at hh; linarith only [hh, hζn']
    calc ‖ζ + a‖ * ‖hz‖ ≤ (4/R + lam) * (11/8) :=
          mul_le_mul h1 hhz_le (norm_nonneg _) (by positivity)
      _ ≤ (4/R + 1/R^2) * (11/8) := by nlinarith only [hlamR0]
  have hdisp12 : (4/R + 1/R^2) * (11/8) ≤ 1/2 := by
    have hd : (4:ℝ)/R ≤ 4/128 := div_le_div₀ (by norm_num) le_rfl (by norm_num) hR
    have hd2 : (1:ℝ)/R^2 ≤ 1/16384 := by
      apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16384); nlinarith only [hR]
    nlinarith only [hlamR0, hd, hd2]
  have hA1ne : 1 + Work.Implosion.dispNum1 a h u ≠ 0 := by
    intro hh
    have h2 : Work.Implosion.dispNum1 a h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hdisp1
    linarith only [hdisp1, hdisp12]
  have hA2ne : 1 + Work.Implosion.dispNum2 a h u ≠ 0 := by
    intro hh
    have h2 : Work.Implosion.dispNum2 a h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hdisp2
    linarith only [hdisp2, hdisp12]
  have hA2re : 0 < (1 + Work.Implosion.dispNum2 a h u).re := by
    have h2 : -(1/2 : ℝ) ≤ (Work.Implosion.dispNum2 a h u).re := by
      have hh := (abs_le.mp (Complex.abs_re_le_norm (Work.Implosion.dispNum2 a h u))).1
      linarith only [hh, hdisp2, hdisp12]
    simp only [Complex.add_re, Complex.one_re]; linarith
  have hEne : Work.Implosion.ecalE a u ≠ 1 := by
    intro hE
    have hmem : u ∈ Work.Implosion.periodLattice a := hE
    rw [Work.Implosion.mem_periodLattice_iff a u hane] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hratio : Real.pi * Complex.I / a = ((Real.pi / lam : ℝ) : ℂ) := by
      rw [ha, mul_div_mul_right _ _ Complex.I_ne_zero]
      exact (Complex.ofReal_div _ _).symm
    rw [hratio] at hn
    have hure : u.re = (n:ℝ) * (Real.pi / lam) := by rw [hn]; simp [Complex.mul_re]
    have hπ : 0 < Real.pi / lam := div_pos Real.pi_pos hlam
    rcases lt_or_ge (0:ℤ) n with hn1 | hn0
    · have h1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have h2 : Real.pi / lam ≤ (n:ℝ) * (Real.pi/lam) := by nlinarith only [h1', hπ]
      rw [← hure] at h2
      linarith only [h2, hx2, hR0]
    · have hn0' : (n:ℝ) ≤ 0 := by exact_mod_cast hn0
      have hlt : (n:ℝ) * (Real.pi/lam) ≤ 0 := by nlinarith only [hn0', hπ]
      rw [← hure] at hlt
      linarith only [hlt, hx1, hR0]
  have hlog0 := Work.PARIMPL2.Direct.log_sinh_modelDisp_sub a h u hane hW0 hW1 hA1ne hA2ne hA2re
    hEne hε
  have hlog : Complex.log (Complex.sinh (a * (u + Φ)) / a) - Complex.log (Complex.sinh (a * u) / a)
      = -(a * Φ) - Complex.log (1 + Work.Implosion.dispNum2 a h u) := by
    rw [← hΦdef] at hlog0
    exact hlog0
  have hA2eq : Work.Implosion.dispNum2 a h u = (ζ + a) * hz := by
    simp only [Work.Implosion.dispNum2, hhzdef, hζdef]
  set S : ℂ := τ - (1 - κ * a) * hz + (1 - κ * a) * ζ * hz ^ 2 - κ * (ζ + a) * hz with hSdef
  have hdecomp : Work.Implosion.approxEcal a κ (u + Φ) - Work.Implosion.approxEcal a κ u + τ
      = S + (1 - κ * a) * (Φ + hz - ζ * hz ^ 2)
        - κ * (Complex.log (1 + Work.Implosion.dispNum2 a h u)
            - Work.Implosion.dispNum2 a h u) := by
    have hΔW : Work.Implosion.approxEcal a κ (u + Φ) - Work.Implosion.approxEcal a κ u
        = Φ + κ * (Complex.log (Complex.sinh (a * (u + Φ)) / a)
            - Complex.log (Complex.sinh (a * u) / a)) := by
      simp only [Work.Implosion.approxEcal_apply]; ring
    rw [hΔW, hlog, hA2eq, hSdef]; ring
  set he : ℂ := hz - τ - h1 * ζ with hedef
  have he38 : ‖he‖ ≤ 3 / 8 := by
    have h5 : (0:ℝ) ≤ 4*B/R := by positivity
    have h6 : 16 * A / R^2 ≤ 3/8 := by linarith only [hAr, h5]
    have h7 : ‖he‖ ≤ 16*A/R^2 := by
      have h8 : A * (16/R^2) = 16*A/R^2 := by ring
      have h9 : A * ‖ζ‖^2 ≤ A * (16/R^2) := mul_le_mul_of_nonneg_left hζ2 hA
      rw [hedef]
      linarith only [hζr_le, h9, h8.le, h8.ge]
    linarith only [h7, h6]
  have hw_eq : h1 * ζ + he = hz - τ := by rw [hedef]; ring
  have hSident : S = -he + ζ*(h1*ζ+he)*(τ + h1/τ) + ζ*(h1*ζ+he)^2 - κ*a*ζ*hz^2 := by
    have hz_eq : τ + h1 * ζ + he = hz := by rw [hedef]; ring
    rw [hSdef, ← hz_eq]
    exact step_S_ident a τ h1 κ ζ he hκ hτ_ne
  have hw3 : ‖h1 * ζ + he‖ ≤ 3 / 8 := by rw [hw_eq]; exact hρ
  have hτh1 : ‖τ + h1/τ‖ ≤ 1 + ‖h1‖ := by
    calc ‖τ + h1/τ‖ ≤ ‖τ‖ + ‖h1/τ‖ := norm_add_le _ _
      _ = 1 + ‖h1‖ := by rw [hτnorm, norm_div, hτnorm, div_one]
  have hSb : ‖S‖ ≤ ‖he‖ + ‖ζ‖*‖h1*ζ+he‖*(1 + ‖h1‖) + ‖ζ‖*‖h1*ζ+he‖^2
      + ‖κ‖*lam*‖ζ‖*‖hz‖^2 := by
    rw [hSident]
    have t1 : ‖ζ*(h1*ζ+he)*(τ + h1/τ)‖ ≤ ‖ζ‖*‖h1*ζ+he‖*(1+‖h1‖) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul le_rfl le_rfl (norm_nonneg _) (norm_nonneg _)) hτh1
        (norm_nonneg _) (by positivity)
    have t2 : ‖ζ*(h1*ζ+he)^2‖ = ‖ζ‖*‖h1*ζ+he‖^2 := by rw [norm_mul, norm_pow]
    have t3 : ‖κ*a*ζ*hz^2‖ = ‖κ‖*lam*‖ζ‖*‖hz‖^2 := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, hna]
    have htri : ‖-he + ζ*(h1*ζ+he)*(τ + h1/τ) + ζ*(h1*ζ+he)^2 - κ*a*ζ*hz^2‖
        ≤ ‖he‖ + ‖ζ*(h1*ζ+he)*(τ + h1/τ)‖ + ‖ζ*(h1*ζ+he)^2‖ + ‖κ*a*ζ*hz^2‖ := by
      have h1' := norm_sub_le (-he + ζ*(h1*ζ+he)*(τ + h1/τ) + ζ*(h1*ζ+he)^2) (κ*a*ζ*hz^2)
      have h2' := norm_add_le (-he + ζ*(h1*ζ+he)*(τ + h1/τ)) (ζ*(h1*ζ+he)^2)
      have h3' := norm_add_le (-he) (ζ*(h1*ζ+he)*(τ + h1/τ))
      simp only [norm_neg] at h3'
      linarith
    linarith only [htri, t1, t2, t3]
  have hSb2 : ‖S‖ ≤ 3/8 + (4/R)*(3/8)*(2 + R/64) + (4/R)*(9/64)
      + (R/64)*(1/R^2)*(4/R)*(121/64) := by
    have hB : ‖ζ‖*‖h1*ζ+he‖*(1 + ‖h1‖) ≤ (4/R)*(3/8)*(2 + R/64) := by
      have h1' : ‖ζ‖*‖h1*ζ+he‖*(1 + ‖h1‖) ≤ (4/R)*(3/8)*(1 + (1 + R/64)) := by
        have h2 : (0:ℝ) ≤ ‖h1*ζ+he‖ := norm_nonneg _
        have h0 : (0:ℝ) ≤ 1 + ‖h1‖ := by positivity
        have h5 : (0:ℝ) ≤ 1 + (1 + R/64) := by positivity
        have h6 : (1:ℝ) + ‖h1‖ ≤ 1 + (1 + R/64) := by linarith only [hh1le]
        have h7 : ‖ζ‖*‖h1*ζ+he‖ ≤ (4/R)*(3/8) := mul_le_mul hζn' hw3 h2 (by positivity)
        calc ‖ζ‖*‖h1*ζ+he‖*(1 + ‖h1‖) ≤ ((4/R)*(3/8))*(1 + (1 + R/64)) :=
              mul_le_mul h7 h6 h0 (by positivity)
          _ = (4/R)*(3/8)*(1 + (1 + R/64)) := by ring
      have h2 : (4/R)*(3/8)*(1 + (1 + R/64)) = (4/R)*(3/8)*(2 + R/64) := by ring
      linarith only [h1', h2.le, h2.ge]
    have hC : ‖ζ‖*‖h1*ζ+he‖^2 ≤ (4/R)*(9/64) := by
      have h2 : ‖h1*ζ+he‖^2 ≤ (3/8)^2 := by nlinarith only [hw3, norm_nonneg (h1*ζ+he)]
      have h0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
      have h3 : ‖ζ‖*‖h1*ζ+he‖^2 ≤ (4/R)*(3/8)^2 := by
        have h5 : (0:ℝ) ≤ (3/8)^2 := by norm_num
        calc ‖ζ‖*‖h1*ζ+he‖^2 ≤ ‖ζ‖*(3/8)^2 := by nlinarith only [h2, h0]
          _ ≤ (4/R)*(3/8)^2 := mul_le_mul_of_nonneg_right hζn' h5
      have h4 : (4/R)*(3/8)^2 = (4/R)*(9/64) := by ring
      linarith only [h3, h4.le, h4.ge]
    have hD : ‖κ‖*lam*‖ζ‖*‖hz‖^2 ≤ (R/64)*(1/R^2)*(4/R)*(121/64) := by
      have h2 : ‖hz‖^2 ≤ (121/64) := by
        have h2' : ‖hz‖^2 ≤ (11/8)^2 := by nlinarith only [hhz_le, norm_nonneg hz]
        have he2 : ((11:ℝ)/8)^2 = 121/64 := by norm_num
        linarith only [h2', he2.le, he2.ge]
      have h6 : ‖κ‖*lam*‖ζ‖ ≤ (R/64)*(1/R^2)*(4/R) := by
        have h0b : (0:ℝ) ≤ R/64 := by positivity
        have h7 : lam*‖ζ‖ ≤ (1/R^2)*(4/R) := by
          have h8 : (0:ℝ) ≤ 1/R^2 := by positivity
          exact mul_le_mul hlamR0 hζn' (norm_nonneg _) h8
        calc ‖κ‖*lam*‖ζ‖ = ‖κ‖*(lam*‖ζ‖) := by ring
          _ ≤ (R/64)*((1/R^2)*(4/R)) := mul_le_mul hκle h7 (by positivity) h0b
          _ = (R/64)*(1/R^2)*(4/R) := by ring
      have h0 : (0:ℝ) ≤ ‖κ‖*lam*‖ζ‖ := by positivity
      have h5 : (0:ℝ) ≤ 121/64 := by norm_num
      calc ‖κ‖*lam*‖ζ‖*‖hz‖^2 ≤ ‖κ‖*lam*‖ζ‖*(121/64) := by nlinarith only [h2, h0]
        _ ≤ (R/64)*(1/R^2)*(4/R)*(121/64) := mul_le_mul h6 le_rfl h5 (by positivity)
    linarith only [he38, hB, hC, hD, hSb]
  have hEb : ‖(1 - κ * a) * (Φ + hz - ζ * hz ^ 2)‖
      ≤ (1 + (R/64)*(1/R^2))*32*((4/R)^2 + (1/R^2)^2) := by
    rw [norm_mul]
    have hκa : ‖1 - κ * a‖ ≤ 1 + (R/64)*(1/R^2) := by
      calc ‖1 - κ * a‖ ≤ ‖(1:ℂ)‖ + ‖κ * a‖ := norm_sub_le _ _
        _ = 1 + ‖κ‖ * lam := by rw [norm_one, norm_mul, hna]
        _ ≤ 1 + (R/64)*(1/R^2) := by
              have h5 : (0:ℝ) ≤ R/64 := by positivity
              have h6 : (0:ℝ) ≤ lam := le_of_lt hlam
              have h7 : ‖κ‖ * lam ≤ (R/64) * lam := mul_le_mul_of_nonneg_right hκle h6
              have h8 : (R/64) * lam ≤ (R/64) * (1/R^2) :=
                mul_le_mul_of_nonneg_left hlamR0 h5
              linarith only [h7, h8]
    have hσ2 : ‖ζ‖^2 ≤ (4/R)^2 := by nlinarith only [hζn', norm_nonneg ζ]
    have hlamsq : lam^2 ≤ (1/R^2)^2 := by nlinarith only [hlamR0, le_of_lt hlam]
    have h32 : 32 * (‖ζ‖^2 + lam^2) ≤ 32 * ((4/R)^2 + (1/R^2)^2) := by linarith
    have h0 : (0:ℝ) ≤ 1 + (R/64)*(1/R^2) := by positivity
    calc ‖1 - κ * a‖ * ‖Φ + hz - ζ * hz^2‖
        ≤ (1 + (R/64)*(1/R^2)) * (32 * (‖ζ‖^2 + lam^2)) :=
          mul_le_mul hκa hso (norm_nonneg _) h0
      _ ≤ (1 + (R/64)*(1/R^2)) * (32 * ((4/R)^2 + (1/R^2)^2)) :=
          mul_le_mul_of_nonneg_left h32 h0
      _ = (1 + (R/64)*(1/R^2))*32*((4/R)^2 + (1/R^2)^2) := by ring
  have hFb : ‖κ * (Complex.log (1 + Work.Implosion.dispNum2 a h u)
        - Work.Implosion.dispNum2 a h u)‖
      ≤ (R/64)*(((4/R) + (1/R^2))*(11/8))^2 := by
    rw [norm_mul]
    have hlogb : ‖Complex.log (1 + Work.Implosion.dispNum2 a h u)
        - Work.Implosion.dispNum2 a h u‖ ≤ ‖Work.Implosion.dispNum2 a h u‖^2 :=
      Work.Implosion.norm_log_one_add_sub_self_le_of_le_half (by linarith only [hdisp2, hdisp12])
    have hsq : ‖Work.Implosion.dispNum2 a h u‖^2 ≤ (((4/R) + (1/R^2))*(11/8))^2 := by
      have h0 : (0:ℝ) ≤ (4/R + 1/R^2)*(11/8) := by positivity
      nlinarith only [hdisp2, norm_nonneg (Work.Implosion.dispNum2 a h u)]
    have h0 : (0:ℝ) ≤ R/64 := by positivity
    have h5 : (0:ℝ) ≤ (((4/R) + (1/R^2))*(11/8))^2 := by positivity
    calc ‖κ‖ * ‖Complex.log (1 + Work.Implosion.dispNum2 a h u)
          - Work.Implosion.dispNum2 a h u‖
        ≤ ‖κ‖ * ‖Work.Implosion.dispNum2 a h u‖^2 :=
          mul_le_mul_of_nonneg_left hlogb (norm_nonneg _)
      _ ≤ (R/64) * (((4/R) + (1/R^2))*(11/8))^2 := mul_le_mul hκle hsq (sq_nonneg _) h0
  have htri : ‖Work.Implosion.approxEcal a κ (u + Φ) - Work.Implosion.approxEcal a κ u + τ‖
      ≤ ‖S‖ + ‖(1 - κ * a) * (Φ + hz - ζ * hz ^ 2)‖
        + ‖κ * (Complex.log (1 + Work.Implosion.dispNum2 a h u)
            - Work.Implosion.dispNum2 a h u)‖ := by
    rw [hdecomp]
    have hh1 := norm_sub_le (S + (1 - κ * a) * (Φ + hz - ζ * hz ^ 2))
      (κ * (Complex.log (1 + Work.Implosion.dispNum2 a h u) - Work.Implosion.dispNum2 a h u))
    have hh2 := norm_add_le S ((1 - κ * a) * (Φ + hz - ζ * hz ^ 2))
    linarith only [hh1, hh2]
  have harith := step_arith R hR
  linarith only [htri, hSb2, hEb, hFb, harith]

/-- The real and imaginary parts of the model displacement `Φ = modelDisp a h u`
(`a = iλ`) are negative and bounded under the hypotheses of the step estimate. -/
private lemma modelDisp_re_im (lam R B : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hB0 : 0 ≤ B)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r : ℝ) (hA : 0 ≤ A)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8)
    (u : ℂ) (hζn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hζr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    (-2 : ℝ) ≤ (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ∧
      (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ≤ -(1 / 3) ∧
      |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).im| ≤ 2 := by
  have hR0 : 0 < R := by linarith
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζdef
  set Φ : ℂ := Work.Implosion.modelDisp a h u with hΦdef
  set hz : ℂ := h ζ with hhzdef
  have hna : ‖a‖ = lam := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact abs_of_pos hlam
  have hane : a ≠ 0 := by
    rw [ha]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hζn' : ‖ζ‖ ≤ 4 / R := hζn
  have hζr' : ‖ζ‖ < r := hζr
  have hζ2 : ‖ζ‖ ^ 2 ≤ 16 / R ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
    have h2 : (4 / R) ^ 2 = 16 / R ^ 2 := by field_simp <;> ring
    nlinarith only [hζn', h0, h2]
  have hlamR0 : lam ≤ 1 / R ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < R ^ 2)]; linarith only [hlamR]
  have h4 : 4 * (‖ζ‖ + ‖a‖) ≤ 1 := by
    rw [hna]
    have hd1 : (4:ℝ)/R ≤ 4/128 := div_le_div₀ (by norm_num) le_rfl (by norm_num) hR
    have hd2 : (1:ℝ)/R^2 ≤ 1/16384 := by
      apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16384); nlinarith only [hR]
    nlinarith only [hζn', hlamR0, hd1, hd2]
  have hτnorm : ‖τ‖ = 1 := hb.2.1
  have hζr_le : ‖hz - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 := by
    have hh := hb.2.2.1 ζ hζr'; simpa [hhzdef] using hh
  have hρ : ‖hz - τ‖ ≤ 3 / 8 := by
    have heq : hz - τ = (hz - τ - h1 * ζ) + h1 * ζ := by ring
    have hd1 : ‖hz - τ‖ ≤ ‖hz - τ - h1 * ζ‖ + ‖h1 * ζ‖ := by
      nth_rewrite 1 [heq]; exact norm_add_le _ _
    rw [norm_mul] at hd1
    have hd2 : ‖h1‖ * ‖ζ‖ ≤ B * (4 / R) := mul_le_mul hh1 hζn' (norm_nonneg _) hB0
    have hd3 : A * ‖ζ‖ ^ 2 ≤ A * (16 / R ^ 2) := mul_le_mul_of_nonneg_left hζ2 hA
    have hd4 : B * (4 / R) + A * (16 / R ^ 2) = 4 * B / R + 16 * A / R ^ 2 := by ring
    linarith only [hd1, hd2, hd3, hd4, hAr, hζr_le]
  have hhz_le : ‖hz‖ ≤ 11 / 8 := by
    have heq : ‖hz‖ = ‖τ + (hz - τ)‖ := by congr 1; ring
    have hd1 : ‖hz‖ ≤ ‖τ‖ + ‖hz - τ‖ := by rw [heq]; exact norm_add_le τ (hz - τ)
    rw [hτnorm] at hd1; linarith only [hd1, hρ]
  have hhz2 : ‖hz‖ ≤ 2 := by linarith only [hhz_le]
  have hso : ‖Φ + hz - ζ * hz ^ 2‖ ≤ 32 * (‖ζ‖ ^ 2 + lam ^ 2) := by
    have hh := Work.Implosion.Approx.modelDisp_second_order a h u hane h4 hhz2
    have h' : ‖Φ + hz - ζ * hz ^ 2‖ ≤ 32 * (‖ζ‖ ^ 2 + ‖a‖ ^ 2) := by
      simpa [hΦdef, hζdef, hhzdef] using hh
    rwa [hna] at h'
  have hτ_re : (7:ℝ) / 8 ≤ τ.re := by
    have hh := Complex.abs_re_le_norm (τ - 1)
    rw [Complex.sub_re, Complex.one_re] at hh
    have hd2 : |τ.re - 1| ≤ 1 / 8 := le_trans hh hτ1
    linarith only [(abs_le.mp hd2).1]
  have hhz_re : (1:ℝ) / 2 ≤ hz.re := by
    have hd2 : -(3 / 8 : ℝ) ≤ (hz - τ).re := by
      have hh := (abs_le.mp (Complex.abs_re_le_norm (hz - τ))).1
      linarith only [hρ, hh]
    rw [Complex.sub_re] at hd2
    linarith only [hd2, hτ_re]
  have hsmall6 : 32 * (‖ζ‖ ^ 2 + lam ^ 2) + ‖ζ‖ * ‖hz‖ ^ 2 ≤ 1 / 6 := by
    have hσ : ‖ζ‖ ≤ 1 / 32 := by
      have hd : (4:ℝ) / R ≤ 4 / 128 := div_le_div₀ (by norm_num) le_rfl (by norm_num) hR
      linarith
    have hlam2 : lam ≤ 1 / 16384 := by
      have hd : (1:ℝ) / R ^ 2 ≤ 1 / 16384 := by
        apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16384); nlinarith only [hR]
      linarith only [hlamR0, hd]
    have hstep1 : ‖ζ‖ * ‖hz‖ ^ 2 ≤ (1/32) * (11/8)^2 := by
      have h0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
      have h1 : ‖hz‖^2 ≤ (11/8)^2 := by nlinarith only [hhz_le, norm_nonneg hz]
      nlinarith only [hσ, h1, h0]
    have hstep2 : 32 * (‖ζ‖ ^ 2 + lam ^ 2) ≤ 32 * ((1/32)^2 + (1/16384)^2) := by
      have h0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
      have h1 : ‖ζ‖^2 ≤ (1/32)^2 := by nlinarith only [hσ, h0]
      have h2 : lam^2 ≤ (1/16384)^2 := by nlinarith only [hlam2, le_of_lt hlam]
      linarith
    nlinarith only [hstep1, hstep2]
  have hA6 : 32 * (‖ζ‖ ^ 2 + lam ^ 2) ≤ 1 / 6 := by
    have h0 : (0:ℝ) ≤ ‖ζ‖ * ‖hz‖^2 := by positivity
    linarith only [hsmall6, h0]
  have hB6 : ‖ζ‖ * ‖hz‖ ^ 2 ≤ 1 / 6 := by
    have h0 : (0:ℝ) ≤ 32 * (‖ζ‖^2 + lam^2) := by positivity
    linarith only [hsmall6, h0]
  have hΦre : Φ.re = (Φ + hz - ζ * hz ^ 2).re - hz.re + (ζ * hz ^ 2).re := by
    have hs : Φ = (Φ + hz - ζ * hz ^ 2) - hz + ζ * hz ^ 2 := by ring
    rw [hs]; simp only [Complex.add_re, Complex.sub_re]; ring
  have hζhz : ‖ζ * hz ^ 2‖ ≤ ‖ζ‖ * ‖hz‖^2 := by rw [norm_mul, norm_pow]
  have hso2 : ‖Φ + hz - ζ * hz ^ 2‖ ≤ 32 * (‖ζ‖ ^ 2 + lam ^ 2) := by
    exact hso
  have hΦn : ‖Φ‖ ≤ 11 / 8 + 1 / 6 := by
    have heq : Φ = (Φ + hz - ζ * hz ^ 2) - hz + ζ * hz ^ 2 := by ring
    have htri : ‖Φ‖ ≤ ‖Φ + hz - ζ * hz ^ 2‖ + ‖hz‖ + ‖ζ * hz ^ 2‖ := by
      calc ‖Φ‖ = ‖(Φ + hz - ζ*hz^2) - hz + ζ*hz^2‖ := by rw [← heq]
        _ ≤ ‖(Φ + hz - ζ*hz^2) - hz‖ + ‖ζ*hz^2‖ := norm_add_le _ _
        _ ≤ (‖Φ + hz - ζ*hz^2‖ + ‖hz‖) + ‖ζ*hz^2‖ := by
              have hh := norm_sub_le (Φ + hz - ζ*hz^2) hz; linarith
    linarith only [htri, hso2, hζhz, hsmall6, hhz_le]
  rw [hΦre]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : -(32 * (‖ζ‖^2 + lam^2)) ≤ (Φ + hz - ζ*hz^2).re := by
      have hh := (abs_le.mp (Complex.abs_re_le_norm (Φ + hz - ζ*hz^2))).1
      linarith only [hh, hso2]
    have h2 : -(‖ζ * hz^2‖) ≤ (ζ*hz^2).re := (abs_le.mp (Complex.abs_re_le_norm _)).1
    have h3 : -(‖ζ‖ * ‖hz‖^2) ≤ (ζ*hz^2).re := by linarith only [h2, hζhz]
    have h4' : hz.re ≤ 11 / 8 := by linarith only [Complex.re_le_norm hz, hhz_le]
    linarith only [h1, h3, hA6, hB6, h4']
  · have h1 : (Φ + hz - ζ*hz^2).re ≤ 32 * (‖ζ‖^2 + lam^2) := by
      have hh := Complex.re_le_norm (Φ + hz - ζ*hz^2)
      linarith only [hh, hso2]
    have h2 : (ζ*hz^2).re ≤ ‖ζ‖ * ‖hz‖^2 := le_trans (Complex.re_le_norm _) hζhz
    linarith only [h1, h2, hsmall6, hhz_re]
  · have h1 : |Φ.im| ≤ ‖Φ‖ := Complex.abs_im_le_norm Φ
    linarith only [h1, hΦn]


/-- **The one-step bounds of the model displacement on the whole transit strip.**
The (E2) estimate of `PARIMPL2/Lavaurs/NOTES_LEAD_transit_exit_direct_S2.md` §3.3, valid on
`R/4 + 2 ≤ Re u ≤ π/λ - R/4` (both halves of the strip). -/
theorem modelDisp_step_bounds2 (lam R B : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hB0 : 0 ≤ B)
    (h : ℂ → ℂ) (τ h1 κ : ℂ) (A r : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hκ : κ = τ - h1 / τ) (hh1 : ‖h1‖ ≤ B)
    (hτ1 : ‖τ - 1‖ ≤ 1 / 8) (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
    (hκR : 64 * ‖κ‖ ≤ R)
    (u : ℂ) (hx1 : R / 4 + 2 ≤ u.re) (hx2 : u.re ≤ Real.pi / lam - R / 4)
    (hζn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hζr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    (-2 : ℝ) ≤ (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ∧
    (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ≤ -(1 / 3) ∧
    |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).im| ≤ 2 ∧
    (-2 : ℝ) ≤ (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ
        (u + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u)).re
      - (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re ∧
    (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ
        (u + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u)).re
      - (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re ≤ -(1 / 4) ∧
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Complex.sinh (((lam : ℂ) * Complex.I)
        * (u + (t : ℂ) * Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u))
        / ((lam : ℂ) * Complex.I) ∈ Complex.slitPlane) := by
  obtain ⟨hΦ1, hΦ2, hΦ3⟩ :=
    modelDisp_re_im lam R B hlam hR hlamR hB0 h τ h1 A r hA hb hh1 hτ1 hAr u hζn hζr
  -- the whole segment `u + [0,1]Φ` lies in the slit plane
  have hslit : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Complex.sinh (((lam : ℂ) * Complex.I)
        * (u + (t : ℂ) * Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u))
        / ((lam : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hvre : (u + (t : ℂ) * Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re
        = u.re + t * (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    have hv1 : R / 4 ≤ (u + (t : ℂ) * Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re := by
      rw [hvre]
      have h1 : t * (-2 : ℝ) ≤ t * (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re :=
        mul_le_mul_of_nonneg_left hΦ1 ht0
      have h2 : (-2 : ℝ) ≤ t * (-2) := by nlinarith only [ht1]
      linarith only [hx1, h1, h2]
    have hv2 : (u + (t : ℂ) * Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re
        ≤ Real.pi / lam - R / 4 := by
      rw [hvre]
      have h1 : t * (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith only [hΦ2])
      linarith only [hx2, h1]
    have hh := Work.Implosion.Approx.sinh_mul_I_div_re_pos lam (R / 4) hlam (by linarith)
      (u + (t : ℂ) * Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u) hv1 hv2
    exact Or.inl hh
  -- the step bound
  have hstep := approxEcal_step_le_aux lam R B hlam hR hlamR hB0 h τ h1 κ A r hA hb hh1 hκ
    hAr hκR u hx1 hx2 hζn hζr hΦ1 hΦ2
  have hτ_re : (7 : ℝ) / 8 ≤ τ.re := by
    have hh := Complex.abs_re_le_norm (τ - 1)
    rw [Complex.sub_re, Complex.one_re] at hh
    have hd2 : |τ.re - 1| ≤ 1 / 8 := le_trans hh hτ1
    linarith only [(abs_le.mp hd2).1]
  have habs : |(Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ
        (u + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u)
      - Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u + τ).re| ≤ 5 / 8 :=
    le_trans (Complex.abs_re_le_norm _) hstep
  have hkey : (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ
          (u + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u)).re
        - (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re
      = -τ.re + (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ
          (u + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u)
        - Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u + τ).re := by
    rw [Complex.add_re, Complex.sub_re]; ring
  refine ⟨hΦ1, hΦ2, hΦ3, ?_, ?_, hslit⟩
  · rw [hkey]
    have h1 := (abs_le.mp habs).1
    have h2 : τ.re ≤ 1 := by
      have h3 := Complex.re_le_norm τ
      rw [hb.2.1] at h3
      linarith only [h3]
    linarith only [h1, h2]
  · rw [hkey]
    have h1 := (abs_le.mp habs).2
    linarith only [h1, hτ_re]

end Work.PARIMPL2.Direct
