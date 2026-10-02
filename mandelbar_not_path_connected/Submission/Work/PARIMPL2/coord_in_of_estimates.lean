/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.coord_in_of_estimates`

**Verdict: the statement is TRUE, but VACUOUSLY so — its hypothesis `hmodel` is
unsatisfiable.**  This is a machine-checked fact: the proof below derives `False` from
`hmodel` (together with the definitions of the workspace and the proved theorem
`Work.Implosion.Approx.approxEcal_end_in_imaginary_neg`).  Consequently it does *not*
establish the intended coordinate identity `approxUin P c z = π/λ_c − φa z` on the window;
it only shows that no `P, φa, ...` satisfy the hypotheses as written.

## Why `hmodel` is unsatisfiable

`Win P R c = {z : Re (approxUin P c z) ∈ [π/λ_c − 2R, π/λ_c − R]}` constrains only the
*real* part of the model coordinate.  In the chart `ζ = chartZeta P c z` (so that
`z = P.m c + P.s c·ζ`), and on the scale `λ_c = P.lam c → 0`, it is the two-dimensional band
`Re (1/ζ) − Re (κ_c log ζ) ∈ [−2R, −R] + O(1)`; in particular it contains points with
`Im ζ < 0` arbitrarily close to the negative real axis (the band is symmetric about it —
for `Im κ_c = 0` exactly, `approxUin (conj ζ) = conj (approxUin ζ)`, so `Re approxUin` is
even in `Im ζ`).  But the asymptotic `approxUin ≈ π/λ_c + π i κ_c + 1/ζ − κ_c log ζ` of
`hmodel` *only holds where the branch is principal*, i.e. where the hypothesis
`Im (sinh (a·u)/a) < 0` of `Work.Implosion.Approx.approxEcal_end_in` holds, which is exactly
`Im ζ > 0`.  Across `Im ζ = 0` (with `Re ζ < 0`) the two sides of `hmodel` differ by
`−2π i κ_c`: on the lower half plane `approxUin ≈ π/λ_c − π i κ_c + 1/ζ − κ_c log ζ`, i.e.
`‖approxUin − (hmodel's right-hand side)‖ ≈ 2π`.  The workspace contains the mirror
statement `Work.Implosion.Approx.approxEcal_end_in_imaginary_neg`, which is what the proof
below applies at the explicit lower-half-plane test point `zetaT R`.

## The proof below

It picks `c ∈ P.Nm` close to `c₀` (possible since `c₀ ∈ closure P.Nm`) with `P.lam c ≤ 1`,
`‖P.κ c − 1‖ ≤ 1/20`, `C·(P.lam c)² ≤ 1/10`, and tests the hypothesis at
`z₀ = P.m c + P.s c·(zetaT R)`, `zetaT R = −e^{3R/2} − i`.  At `z₀`:

* `z₀ ∈ Win P R c` — the mirror asymptotic places `Re (approxUin P c z₀) − π/λ_c` at
  `−e^{3R/2}/(e^{3R}+1) − log ‖zetaT R‖ ≈ −3R/2`, the middle of `[−2R, −R]`;
* `‖approxUin P c z₀ − Bb‖ > 1` where `Bb` is the right-hand side of `hmodel` (the mirror
  estimate gives `‖approxUin − (Bb − 2π i κ_c)‖ ≤ 1/10`, and `‖2π i κ_c‖ ≥ 2π·(19/20) > 1.1`);
* `hmodel 1` gives `‖approxUin P c z₀ − Bb‖ ≤ 1`, a contradiction.

**Consequence for the caller.**  To obtain the intended (non-vacuous) identity one must
restrict the window to the branch-consistent part (`Im (chartZeta P c z) > 0`, equivalently
`(sinh (a·u)/a).im < 0` at `u = ecalCoord (P.a c) (chartZeta P c z)`), or state the model
asymptotics in the "sum form" `approxUin − π/λ_c + w − log w → 0` (`w = −lam/(z − z₁)`)
which does not split the `2πi`.  See `NOTES_VACUOUS_coord_in.md` in this directory.
-/
import Mathlib
import Submission.Work.PARIMPL2.MatchCore
import Submission.Work.Implosion.Approx.approxEcal_end_in_imaginary_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open Work.PARIMPL (ParNormal Win approxUin chartZeta)
open Work.Implosion (ecalCoord ecalE ecalPt coth mobius)

variable {c₀ : ℂ}

/-- The test point `ζ₀ = -e^{3R/2} - i` in the chart: it is in the lower half plane, far
from the origin, and `Re (1/ζ₀) - log ‖ζ₀‖ ≈ -3R/2`, in the middle of the window band
`[-2R, -R]`. -/
noncomputable def zetaT (R : ℝ) : ℂ := -((Real.exp (3 * R / 2) : ℝ) : ℂ) - Complex.I

lemma zetaT_re (R : ℝ) : (zetaT R).re = -Real.exp (3 * R / 2) := by
  simp only [zetaT, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re]
  ring

lemma zetaT_im (R : ℝ) : (zetaT R).im = -1 := by
  simp only [zetaT, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.I_im]
  ring

lemma exp_half_sq (R : ℝ) : (Real.exp (3 * R / 2)) ^ 2 = Real.exp (3 * R) := by
  rw [sq, ← Real.exp_add, show 3 * R / 2 + 3 * R / 2 = 3 * R by ring]

lemma zetaT_normSq (R : ℝ) : Complex.normSq (zetaT R) = Real.exp (3 * R) + 1 := by
  rw [Complex.normSq_apply, zetaT_re, zetaT_im]
  nlinarith [exp_half_sq R]

lemma zetaT_norm_sq (R : ℝ) : ‖zetaT R‖ ^ 2 = Real.exp (3 * R) + 1 := by
  rw [← Complex.normSq_eq_norm_sq, zetaT_normSq]

lemma zetaT_inv_re (R : ℝ) :
    (zetaT R)⁻¹.re = -Real.exp (3 * R / 2) / (Real.exp (3 * R) + 1) := by
  rw [Complex.inv_re, zetaT_re, zetaT_normSq]

lemma zetaT_inv_im (R : ℝ) : (zetaT R)⁻¹.im = 1 / (Real.exp (3 * R) + 1) := by
  rw [Complex.inv_im, zetaT_im, zetaT_normSq]
  ring

lemma zetaT_re_neg (R : ℝ) : (zetaT R).re < 0 := by
  rw [zetaT_re]; exact neg_lt_zero.mpr (Real.exp_pos _)

lemma zetaT_im_neg (R : ℝ) : (zetaT R).im < 0 := by
  rw [zetaT_im]; norm_num

lemma one_le_norm_zetaT (R : ℝ) : 1 ≤ ‖zetaT R‖ := by
  have h : (1:ℝ) ≤ Real.exp (3 * R) + 1 := by
    have := Real.exp_pos (3 * R); linarith
  have h2 : (1:ℝ) ^ 2 ≤ ‖zetaT R‖ ^ 2 := by rw [zetaT_norm_sq]; simpa using h
  nlinarith [norm_nonneg (zetaT R)]

lemma exp_le_norm_zetaT (R : ℝ) : Real.exp (3 * R / 2) ≤ ‖zetaT R‖ := by
  have h : (Real.exp (3 * R / 2)) ^ 2 ≤ ‖zetaT R‖ ^ 2 := by
    rw [zetaT_norm_sq, exp_half_sq]
    have := Real.exp_pos (3 * R); linarith
  nlinarith [Real.exp_pos (3 * R / 2), norm_nonneg (zetaT R)]

lemma norm_zetaT_pos (R : ℝ) : 0 < ‖zetaT R‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_zetaT R)

lemma norm_zetaT_le (R : ℝ) (hR : 0 ≤ R) :
    ‖zetaT R‖ ≤ Real.sqrt 2 * Real.exp (3 * R / 2) := by
  have hexp1 : (1:ℝ) ≤ Real.exp (3 * R) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have h2 : ‖zetaT R‖ ^ 2 ≤ 2 * Real.exp (3 * R) := by
    rw [zetaT_norm_sq]; linarith
  have h3 : Real.sqrt (‖zetaT R‖ ^ 2) ≤ Real.sqrt (2 * Real.exp (3 * R)) :=
    Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (norm_nonneg _)] at h3
  refine le_trans h3 (le_of_eq ?_)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  rw [← exp_half_sq R, Real.sqrt_sq (le_of_lt (Real.exp_pos _))]

/-- `log ‖ζ₀‖ ∈ [3R/2, 3R/2 + log 2 / 2]` (for `R ≥ 0`). -/
lemma log_norm_zetaT_bounds (R : ℝ) (hR : 0 ≤ R) :
    3 * R / 2 ≤ Real.log ‖zetaT R‖ ∧
      Real.log ‖zetaT R‖ ≤ 3 * R / 2 + Real.log 2 / 2 := by
  refine ⟨?_, ?_⟩
  · simpa using Real.log_le_log (Real.exp_pos (3 * R / 2)) (exp_le_norm_zetaT R)
  · calc Real.log ‖zetaT R‖ ≤ Real.log (Real.sqrt 2 * Real.exp (3 * R / 2)) :=
          Real.log_le_log (norm_zetaT_pos R) (norm_zetaT_le R hR)
      _ = Real.log 2 / 2 + 3 * R / 2 := by
          rw [Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (Real.exp_ne_zero _),
            Real.log_sqrt (by norm_num), Real.log_exp]
      _ = 3 * R / 2 + Real.log 2 / 2 := by ring

lemma hundred_lt_exp_three_halves (R : ℝ) (hR : 4 ≤ R) :
    (100:ℝ) < Real.exp (3 * R / 2) := by
  have h3 : (6:ℝ) ≤ 3 * R / 2 := by linarith
  have h4 : Real.exp 6 ≤ Real.exp (3 * R / 2) := Real.exp_le_exp.mpr h3
  have h5 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    simpa using Real.exp_nat_mul (1:ℝ) 6
  have h6 : (2.7182818283:ℝ) ^ 6 < (Real.exp 1) ^ 6 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h7 : (100:ℝ) < (2.7182818283:ℝ) ^ 6 := by norm_num
  linarith

/-- `‖cosh w - 1‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`. -/
lemma cosh_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := by
  have h1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hw
  have h2 : ‖Complex.exp (-w) - 1 - (-w)‖ ≤ ‖w‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -w) (by rwa [norm_neg])
    rwa [norm_neg] at h
  have hdecomp : Complex.cosh w - 1
      = ((Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))) / 2 := by
    rw [Complex.cosh]; ring
  rw [hdecomp, norm_div, Complex.norm_ofNat]
  have hsum : ‖(Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))‖ ≤ 2 * ‖w‖ ^ 2 := by
    calc ‖(Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))‖
        ≤ ‖Complex.exp w - 1 - w‖ + ‖Complex.exp (-w) - 1 - (-w)‖ := norm_add_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := add_le_add h1 h2
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-- For `a ≠ 0`, `ζ ∉ {0, a, -a}`: `sinh (a * ecalCoord a ζ) / a = cosh (a * ecalCoord a ζ) / ζ`. -/
lemma sinh_div_eq_cosh_div {a ζ : ℂ} (ha : a ≠ 0) (hζ : ζ ≠ 0) (h1 : ζ ≠ a) (h2 : ζ ≠ -a) :
    Complex.sinh (a * ecalCoord a ζ) / a = Complex.cosh (a * ecalCoord a ζ) / ζ := by
  set u : ℂ := ecalCoord a ζ with hu
  have hlog : 2 * a * u = Complex.log (mobius a ζ) := by
    rw [hu, ecalCoord]; field_simp
  have hm0 : mobius a ζ ≠ 0 := (Work.Implosion.mobius_ne_zero_iff a ζ).mpr ⟨h2, h1⟩
  have hm1 : mobius a ζ ≠ 1 := by
    intro h
    rw [mobius] at h
    have hd : ζ - a ≠ 0 := sub_ne_zero.mpr h1
    have heq := (div_eq_one_iff_eq hd).mp h
    exact ha (by linear_combination heq / 2)
  have hEne : ecalE a u ≠ 1 := by
    rw [ecalE, hlog, Complex.exp_log hm0]; exact hm1
  have hcoth : ecalPt a u = a * coth (a * u) :=
    Work.Implosion.Ecalle.ecallePt_eq_coth a u hEne
  have hpt : ecalPt a u = ζ := Work.Implosion.ecalPt_ecalCoord a ζ ha h1 h2
  have hζeq : ζ = a * (Complex.cosh (a * u) / Complex.sinh (a * u)) := by
    rw [← hpt, hcoth, coth]
  have hsinh : Complex.sinh (a * u) ≠ 0 := by
    intro h
    have hc : coth (a * u) = 0 := by rw [coth, h, div_zero]
    exact hζ (by rw [← hpt, hcoth, hc, mul_zero])
  have hmul : ζ * Complex.sinh (a * u) = a * Complex.cosh (a * u) := by
    rw [hζeq]; field_simp
  rw [div_eq_div_iff ha hζ]
  linear_combination hmul

variable {d : Work.EL.RootParabolic c₀} {P : ParNormal d} {R : ℝ}

/-- The branch condition of the mirror asymptotic at the test point: for `c ∈ Nm` with
`P.lam c ≤ 1`, `Im (sinh (a · u)/a) > 0` at `u = ecalCoord a (zetaT R)`, `a = i λ_c`. -/
lemma branch_cond (hR : 4 ≤ R) {c : ℂ} (hcNm : c ∈ P.Nm) (hclam1 : P.lam c ≤ 1) :
    0 < (Complex.sinh (((P.lam c : ℂ) * Complex.I) *
        ecalCoord ((P.lam c : ℂ) * Complex.I) (zetaT R)) /
      ((P.lam c : ℂ) * Complex.I)).im := by
  set lc : ℝ := P.lam c with hlc
  set a : ℂ := (lc : ℂ) * Complex.I with hadef
  set ζ₀ : ℂ := zetaT R with hζdef
  have hlampos : 0 < lc := P.lam_pos_of_mem_Nm hcNm
  have hlamC : (lc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlampos)
  have ha0 : a ≠ 0 := mul_ne_zero hlamC Complex.I_ne_zero
  have hnorma : ‖a‖ = lc := by
    rw [hadef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlampos]
  have hζne : ζ₀ ≠ 0 := by
    intro h
    have h1 := one_le_norm_zetaT R
    rw [hζdef] at h
    rw [h, norm_zero] at h1
    norm_num at h1
  have hζ1 : 1 ≤ ‖ζ₀‖ := by rw [hζdef]; exact one_le_norm_zetaT R
  have hzpos : (0:ℝ) < ‖ζ₀‖ := lt_of_lt_of_le zero_lt_one hζ1
  have htbig : (100:ℝ) < Real.exp (3 * R / 2) := hundred_lt_exp_three_halves R hR
  have htpos : (0:ℝ) < Real.exp (3 * R / 2) := Real.exp_pos _
  have hζnormbig : Real.exp (3 * R / 2) ≤ ‖ζ₀‖ := by rw [hζdef]; exact exp_le_norm_zetaT R
  have h4le : 4 * ‖a‖ ≤ ‖ζ₀‖ := by
    rw [hnorma]; have := hclam1; linarith
  have ha_lt : ‖a‖ < ‖ζ₀‖ := by
    rw [hnorma]; have := hclam1; linarith
  have ha1 : ζ₀ ≠ a := by intro h; rw [h] at ha_lt; exact absurd ha_lt (lt_irrefl _)
  have ha2 : ζ₀ ≠ -a := by
    intro h; rw [h, norm_neg] at ha_lt; exact absurd ha_lt (lt_irrefl _)
  have hw : Complex.sinh (a * ecalCoord a ζ₀) / a
      = Complex.cosh (a * ecalCoord a ζ₀) / ζ₀ :=
    sinh_div_eq_cosh_div ha0 hζne ha1 ha2
  rw [hw]
  have hsub : ‖ecalCoord a ζ₀ - 1 / ζ₀‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ₀‖ ^ 2 :=
    Work.Implosion.Approx.ecalCoord_sub_inv_le a ζ₀ ha0 hζ1 h4le
  have hnu : ‖ecalCoord a ζ₀‖ ≤ 2 / ‖ζ₀‖ := by
    have h1 : ‖ecalCoord a ζ₀‖ ≤ ‖ecalCoord a ζ₀ - 1 / ζ₀‖ + ‖(1:ℂ)/ζ₀‖ := by
      calc ‖ecalCoord a ζ₀‖ = ‖(ecalCoord a ζ₀ - 1/ζ₀) + 1/ζ₀‖ := by ring_nf
        _ ≤ ‖ecalCoord a ζ₀ - 1/ζ₀‖ + ‖(1:ℂ)/ζ₀‖ := norm_add_le _ _
    have h2 : ‖(1:ℂ)/ζ₀‖ = 1/‖ζ₀‖ := by rw [norm_div, norm_one]
    rw [h2] at h1
    have hb : 4 / 9 * ‖a‖ ^ 2 ≤ ‖ζ₀‖ := by
      rw [hnorma]
      nlinarith [hclam1, hlampos, h4le, hnorma]
    have h3 : 4 / 9 * ‖a‖ ^ 2 / ‖ζ₀‖ ^ 2 ≤ 1 / ‖ζ₀‖ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖ζ₀‖ ^ 2)]
      have heq : (1 / ‖ζ₀‖) * ‖ζ₀‖ ^ 2 = ‖ζ₀‖ := by
        field_simp
      rw [heq]
      exact hb
    have h4 : ‖ecalCoord a ζ₀ - 1 / ζ₀‖ ≤ 1 / ‖ζ₀‖ := le_trans hsub h3
    have h5 : ‖ecalCoord a ζ₀‖ ≤ 2 * (1 / ‖ζ₀‖) := by linarith [h1, h4]
    have h6 : (2:ℝ) / ‖ζ₀‖ = 2 * (1 / ‖ζ₀‖) := by ring
    linarith [h5, h6]
  have hau : ‖a * ecalCoord a ζ₀‖ ≤ 1 := by
    rw [norm_mul]
    have h1 : ‖a‖ * ‖ecalCoord a ζ₀‖ ≤ lc * (2/‖ζ₀‖) :=
      mul_le_mul (le_of_eq hnorma) hnu (norm_nonneg _) (by positivity)
    have h2 : lc * (2/‖ζ₀‖) ≤ 1 := by
      have heq : lc * (2/‖ζ₀‖) = 2 * lc / ‖ζ₀‖ := by ring
      rw [heq, div_le_one hzpos]
      nlinarith [hclam1, hζnormbig, htbig]
    linarith
  have hcosh : ‖Complex.cosh (a * ecalCoord a ζ₀) - 1‖ ≤ ‖a * ecalCoord a ζ₀‖ ^ 2 :=
    cosh_sub_one_le hau
  have hsplit : (Complex.cosh (a * ecalCoord a ζ₀) / ζ₀).im
      = (1 / ζ₀).im + ((Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀).im := by
    have heq : Complex.cosh (a * ecalCoord a ζ₀) / ζ₀
        = 1/ζ₀ + (Complex.cosh (a * ecalCoord a ζ₀) - 1)/ζ₀ := by
      field_simp; ring
    rw [heq, Complex.add_im]
  have himlower : -‖(Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀‖
      ≤ ((Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀).im := by
    have h := (abs_le.mp (Complex.abs_im_le_norm ((Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀))).1
    linarith
  have hclip : ‖(Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀‖
      ≤ ‖a * ecalCoord a ζ₀‖^2 / ‖ζ₀‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right hcosh (norm_nonneg _)
  have hupper : ‖a * ecalCoord a ζ₀‖^2 / ‖ζ₀‖ ≤ 1 / (4 * (Real.exp (3*R/2))^2) := by
    have h1 : ‖a * ecalCoord a ζ₀‖ ≤ 2 * lc / ‖ζ₀‖ := by
      rw [norm_mul]
      calc ‖a‖ * ‖ecalCoord a ζ₀‖ ≤ lc * (2/‖ζ₀‖) :=
            mul_le_mul (le_of_eq hnorma) hnu (norm_nonneg _) (by positivity)
        _ = 2 * lc / ‖ζ₀‖ := by ring
    have h2 : 2 * lc / ‖ζ₀‖ ≤ 2 / Real.exp (3*R/2) := by
      rw [div_le_iff₀ hzpos, div_mul_eq_mul_div, le_div_iff₀ htpos]
      nlinarith [hclam1, hζnormbig, hlampos, htpos]
    have h4 : ‖a * ecalCoord a ζ₀‖ ≤ 2 / Real.exp (3*R/2) := le_trans h1 h2
    have h5 : ‖a * ecalCoord a ζ₀‖ ^ 2 ≤ (2 / Real.exp (3*R/2))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) h4 2
    have h6 : ‖a * ecalCoord a ζ₀‖^2 / ‖ζ₀‖ ≤ (2 / Real.exp (3*R/2))^2 / ‖ζ₀‖ :=
      div_le_div_of_nonneg_right h5 hzpos.le
    have h7 : (2 / Real.exp (3*R/2))^2 / ‖ζ₀‖ ≤ (2 / Real.exp (3*R/2))^2 / Real.exp (3*R/2) :=
      div_le_div_of_nonneg_left (by positivity) htpos hζnormbig
    have h8 : (2 / Real.exp (3*R/2))^2 / Real.exp (3*R/2)
        ≤ 1 / (4 * (Real.exp (3*R/2))^2) := by
      rw [div_le_div_iff₀ htpos (by positivity), one_mul]
      have he : (2 / Real.exp (3*R/2))^2 * (4 * (Real.exp (3*R/2))^2) = 16 := by
        field_simp
        ring
      rw [he]
      linarith [htbig]
    linarith
  have himinv : 1 / (2 * (Real.exp (3*R/2))^2) ≤ (1/ζ₀).im := by
    have h1 : (1/ζ₀).im = 1 / (Real.exp (3*R) + 1) := by
      rw [hζdef, one_div]; exact zetaT_inv_im R
    rw [h1, one_div_le_one_div (by positivity) (by positivity)]
    rw [exp_half_sq]
    have h2 : (1:ℝ) ≤ Real.exp (3*R) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  rw [hsplit]
  have hfin : 1 / (2 * (Real.exp (3*R/2))^2) - 1 / (4 * (Real.exp (3*R/2))^2) ≤
      (1 / ζ₀).im + ((Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀).im := by
    have h5 : ‖(Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀‖ ≤ 1 / (4 * (Real.exp (3*R/2))^2) :=
      le_trans hclip hupper
    have h6 : 1 / (2 * (Real.exp (3*R/2))^2) - ‖(Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀‖
        ≤ (1 / ζ₀).im + ((Complex.cosh (a * ecalCoord a ζ₀) - 1) / ζ₀).im := by
      linarith [himinv, himlower]
    linarith [h6, h5]
  have hpos : (0:ℝ) < 1 / (2 * (Real.exp (3*R/2))^2) - 1 / (4 * (Real.exp (3*R/2))^2) := by
    have ht2 : (0:ℝ) < (Real.exp (3*R/2))^2 := by positivity
    have he : 1 / (2 * (Real.exp (3*R/2))^2) - 1 / (4 * (Real.exp (3*R/2))^2)
        = 1 / (4 * (Real.exp (3*R/2))^2) := by
      field_simp
      ring
    rw [he]
    positivity
  linarith


theorem coord_in_of_estimates {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {P : Work.PARIMPL.ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {R : ℝ} (hR : 4 ≤ R) {lam : ℂ} (hlam : lam ≠ 0)
    (hsc : P.s c₀ = lam) (hκ : P.κ c₀ = 1)
    (hflower : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, ∀ z : ℂ, z ∈ Work.PARIMPL.Win P R c →
        ‖φa z - ((-lam / (z - d.z₁)) - Complex.log (-lam / (z - d.z₁)))‖ ≤ η)
    (hmodel : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, ∀ z : ℂ, z ∈ Work.PARIMPL.Win P R c →
        ‖Work.PARIMPL.approxUin P c z
          - ((Real.pi / P.lam c : ℂ) + (Real.pi : ℂ) * Complex.I * P.κ c
              + 1 / Work.PARIMPL.chartZeta P c z
              - P.κ c * Complex.log (Work.PARIMPL.chartZeta P c z))‖ ≤ η) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, ∀ z : ℂ, z ∈ Work.PARIMPL.Win P R c →
        ‖Work.PARIMPL.approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)‖ ≤ η := by
  intro η hη
  -- The hypothesis `hmodel` is unsatisfiable; we derive a contradiction and finish.
  have hcontra : False := by
    obtain ⟨C, hC0, hC⟩ := Work.Implosion.Approx.approxEcal_end_in_imaginary_neg 2 (by norm_num)
    obtain ⟨ρ₁, hρ₁pos, hρ₁le, hM⟩ := hmodel 1 (by norm_num)
    have hne : (𝓝[P.Nm] c₀).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (Work.PARIMPL.Nm_mem_closure d P)
    have hNmEv : ∀ᶠ c in 𝓝[P.Nm] c₀, c ∈ P.Nm :=
      (Filter.eventually_principal.mpr (fun c hc => hc)).filter_mono inf_le_right
    have hballEv : ∀ᶠ c in 𝓝[P.Nm] c₀, c ∈ Metric.ball c₀ ρ₁ :=
      (show ∀ᶠ c in 𝓝 c₀, c ∈ Metric.ball c₀ ρ₁ from Metric.ball_mem_nhds c₀ hρ₁pos).filter_mono
        inf_le_left
    have hκEv : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.κ c - 1‖ ≤ 1/20 := by
      have hc : ContinuousAt P.κ c₀ :=
        P.cont_κ.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self P.hρ₀))
      have h1 : ∀ᶠ y in 𝓝 (P.κ c₀), ‖y - P.κ c₀‖ ≤ 1/20 := by
        have hcl : Metric.closedBall (P.κ c₀) (1/20) ∈ 𝓝 (P.κ c₀) :=
          Metric.closedBall_mem_nhds _ (by norm_num)
        filter_upwards [hcl] with y hy
        rw [Metric.mem_closedBall, dist_eq_norm] at hy
        simpa using hy
      have h2 := hc.tendsto.eventually h1
      rw [hκ] at h2
      exact h2.filter_mono inf_le_left
    have hl1Ev : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c ≤ 1 := by
      have hl : Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) :=
        P.tendsto_lam c₀ P.a2₀ (Metric.mem_ball_self P.hρ₀)
      have h1 : ∀ᶠ y in 𝓝 (0:ℝ), y ≤ 1 := by
        filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        linarith [(abs_lt.mp hy).2]
      exact hl.eventually h1
    have hl2Ev : ∀ᶠ c in 𝓝[P.Nm] c₀, C * P.lam c ^ 2 ≤ 1/10 := by
      have hl : Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) :=
        P.tendsto_lam c₀ P.a2₀ (Metric.mem_ball_self P.hρ₀)
      have hδ : (0:ℝ) < 1/(4*(C+1)) := by positivity
      have h1 : ∀ᶠ y in 𝓝 (0:ℝ), C * y ^ 2 ≤ 1/10 := by
        filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hy' : |y| < 1/(4*(C+1)) := by simpa using hy
        have habs : |y| ≤ 1/(4*(C+1)) := le_of_lt hy'
        have hy2 : y^2 ≤ (1/(4*(C+1)))^2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) habs 2
        have key : C * (1/(4*(C+1)))^2 ≤ 1/10 := by
          rw [div_pow, one_pow, mul_pow, mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg C, hC0]
        calc C * y^2 ≤ C * (1/(4*(C+1)))^2 := mul_le_mul_of_nonneg_left hy2 hC0
          _ ≤ 1/10 := key
      exact hl.eventually h1
    have hgood : ∀ᶠ c in 𝓝[P.Nm] c₀,
        c ∈ P.Nm ∧ c ∈ Metric.ball c₀ ρ₁ ∧ ‖P.κ c - 1‖ ≤ 1/20 ∧ P.lam c ≤ 1
          ∧ C * P.lam c ^ 2 ≤ 1/10 := by
      filter_upwards [hNmEv, hballEv, hκEv, hl1Ev, hl2Ev] with c h1 h2 h3 h4 h5
      exact ⟨h1,h2,h3,h4,h5⟩
    haveI : (𝓝[P.Nm] c₀).NeBot := hne
    obtain ⟨c, hcNm, hcball, hcκ, hclam1, hcC⟩ := hgood.exists
    have hlpos : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
    have hsne : P.s c ≠ 0 := P.s_ne c hcNm.1
    set a : ℂ := (P.lam c : ℂ) * Complex.I with ha
    set ζ₀ : ℂ := zetaT R with hζ0
    have ha0 : a ≠ 0 := by
      rw [ha]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlpos)) Complex.I_ne_zero
    have hPa : P.a c = a := by rw [ha]; exact P.a_of_mem_Nm hcNm
    have hζ0re : ζ₀.re < 0 := by rw [hζ0]; exact zetaT_re_neg R
    have hζ0im : ζ₀.im < 0 := by rw [hζ0]; exact zetaT_im_neg R
    have hζ0norm : 1 ≤ ‖ζ₀‖ := by rw [hζ0]; exact one_le_norm_zetaT R
    have hnorma : ‖a‖ = P.lam c := by
      rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hlpos]
    have hκnorm : ‖P.κ c‖ ≤ 2 := by
      have h1 : ‖P.κ c‖ ≤ ‖P.κ c - 1‖ + 1 := by
        have := norm_add_le (P.κ c - 1) 1
        rwa [sub_add_cancel, norm_one] at this
      linarith
    have hle1 : ‖a‖ ≤ 1 := by rw [hnorma]; exact hclam1
    have h4le : 4 * ‖a‖ ≤ ‖ζ₀‖ := by
      rw [hnorma]
      have h8 := exp_le_norm_zetaT R
      have h100 := hundred_lt_exp_three_halves R hR
      linarith
    have hbranch : 0 < (Complex.sinh (a * ecalCoord a ζ₀) / a).im := by
      rw [ha, hζ0]
      exact branch_cond (P := P) hR hcNm hclam1
    have hbranchE : 0 < (Complex.sinh (((P.lam c : ℂ) * Complex.I) *
        ecalCoord ((P.lam c : ℂ) * Complex.I) ζ₀) / ((P.lam c : ℂ) * Complex.I)).im := by
      simpa only [ha] using hbranch
    have hm := hC (P.lam c) (P.κ c) ζ₀ hlpos hζ0re hζ0norm hκnorm hbranchE
      (by simpa only [ha] using h4le) (by simpa only [ha] using hle1)
    have hzeta_eq : Work.PARIMPL.chartZeta P c (P.m c + P.s c * ζ₀) = ζ₀ := by
      rw [Work.PARIMPL.chartZeta]
      field_simp
      ring
    have hAeq : Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀)
        = Work.Implosion.approxEcal a (P.κ c)
            (ecalCoord a ζ₀ + Real.pi * Complex.I / a) := by
      simp only [Work.PARIMPL.approxUin, Work.PARIMPL.ecalUin, Work.PARIMPL.ecalU,
        hPa, hzeta_eq, ha]
    set M' : ℂ := (Real.pi : ℂ) * Complex.I / ((P.lam c : ℂ) * Complex.I)
        - (Real.pi : ℂ) * Complex.I * (P.κ c) + (1 / ζ₀ - (P.κ c) * Complex.log ζ₀) with hM'
    have hm' : ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - M'‖
        ≤ C * ‖(P.lam c : ℂ) * Complex.I‖ ^ 2 / ‖ζ₀‖ ^ 2 := by
      rw [hAeq, ha, hM']
      exact hm
    have hnormlam : ‖(P.lam c : ℂ) * Complex.I‖ = P.lam c := by
      rw [← ha]; exact hnorma
    have herr : C * ‖(P.lam c : ℂ) * Complex.I‖ ^ 2 / ‖ζ₀‖ ^ 2 ≤ 1/10 := by
      rw [hnormlam, div_le_iff₀ (by positivity : (0:ℝ) < ‖ζ₀‖^2)]
      have h1 : (1:ℝ) ≤ ‖ζ₀‖^2 := by nlinarith [hζ0norm]
      nlinarith [hcC, h1]
    have herr' : ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - M'‖ ≤ 1/10 :=
      le_trans hm' herr
    -- the real part of `M'`
    have hpi : (Real.pi : ℂ) * Complex.I / ((P.lam c : ℂ) * Complex.I)
        = ((Real.pi / P.lam c : ℝ) : ℂ) := by
      rw [div_eq_iff (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlpos))
        Complex.I_ne_zero)]
      push_cast
      field_simp
      rw [div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt hlpos))]
    have hM'pi : M' = ((Real.pi / P.lam c : ℝ) : ℂ) - (Real.pi : ℂ) * Complex.I * (P.κ c)
        + (1 / ζ₀ - (P.κ c) * Complex.log ζ₀) := by
      rw [hM', hpi]
    have hre : M'.re - Real.pi / P.lam c
        = -(Real.exp (3*R/2) / (Real.exp (3*R) + 1)) - (P.κ c).re * Real.log ‖ζ₀‖
          + (P.κ c).im * (Real.pi + ζ₀.arg) := by
      rw [hM'pi]
      simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, Complex.inv_re, Complex.inv_im, Complex.log_re, Complex.log_im,
        hζ0, zetaT_re, zetaT_im, zetaT_normSq, one_div, mul_one, mul_zero, zero_mul, add_zero,
        sub_zero, zero_sub, neg_zero]
      ring
    have hκre_ub : (P.κ c).re ≤ 21/20 := by
      have h := Complex.abs_re_le_norm (P.κ c - 1)
      have h' : (P.κ c - 1).re = (P.κ c).re - 1 := by simp [Complex.sub_re]
      rw [h'] at h
      have := (abs_le.mp h).2
      linarith [hcκ]
    have hκre_lb : 19/20 ≤ (P.κ c).re := by
      have h := Complex.abs_re_le_norm (P.κ c - 1)
      have h' : (P.κ c - 1).re = (P.κ c).re - 1 := by simp [Complex.sub_re]
      rw [h'] at h
      have := (abs_le.mp h).1
      linarith [hcκ]
    have hκim_ub : (P.κ c).im ≤ 1/20 := by
      have h := Complex.abs_im_le_norm (P.κ c - 1)
      have h' : (P.κ c - 1).im = (P.κ c).im := by simp [Complex.sub_im]
      rw [h'] at h
      have := (abs_le.mp h).2
      linarith [hcκ]
    have hκim_lb : -(1/20) ≤ (P.κ c).im := by
      have h := Complex.abs_im_le_norm (P.κ c - 1)
      have h' : (P.κ c - 1).im = (P.κ c).im := by simp [Complex.sub_im]
      rw [h'] at h
      have := (abs_le.mp h).1
      linarith [hcκ]
    have hlog_ub : Real.log ‖ζ₀‖ ≤ 3*R/2 + Real.log 2 / 2 := by
      rw [hζ0]; exact (log_norm_zetaT_bounds R (by linarith)).2
    have hlog_lb : 3*R/2 ≤ Real.log ‖ζ₀‖ := by
      rw [hζ0]; exact (log_norm_zetaT_bounds R (by linarith)).1
    have harg_ub : Real.pi + ζ₀.arg ≤ 2 * Real.pi := by
      have := Complex.arg_le_pi ζ₀; linarith
    have harg_lb : -(2 * Real.pi) ≤ Real.pi + ζ₀.arg := by
      have := Complex.neg_pi_lt_arg ζ₀; linarith
    have hMre_ub : M'.re - Real.pi / P.lam c
        ≤ -(19/20) * (3*R/2) + (1/20) * (2*Real.pi) := by
      rw [hre]
      have h1 : -(Real.exp (3*R/2) / (Real.exp (3*R) + 1)) ≤ 0 := by
        have hq : 0 ≤ Real.exp (3*R/2) / (Real.exp (3*R) + 1) := by positivity
        linarith
      have h2 : (P.κ c).im * (Real.pi + ζ₀.arg) ≤ (1/20) * (2*Real.pi) := by
        by_cases h : 0 ≤ (P.κ c).im
        · nlinarith [hκim_ub, harg_ub, h, Real.pi_pos]
        · push_neg at h
          nlinarith [hκim_lb, harg_lb, h, Real.pi_pos]
      have h3 : (19/20) * (3*R/2) ≤ (P.κ c).re * Real.log ‖ζ₀‖ := by
        nlinarith [hκre_lb, hlog_lb]
      linarith
    have hMre_lb : -(21/20) * (3*R/2 + Real.log 2 / 2) - 1/100 - (1/20) * (2*Real.pi)
        ≤ M'.re - Real.pi / P.lam c := by
      rw [hre]
      have ht : (100:ℝ) < Real.exp (3*R/2) := hundred_lt_exp_three_halves R hR
      have h1 : Real.exp (3*R/2) / (Real.exp (3*R) + 1) ≤ 1/100 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.exp (3*R) + 1)]
        rw [← exp_half_sq]
        nlinarith [ht, Real.exp_pos (3*R/2), sq_nonneg (Real.exp (3*R/2))]
      have h2 : -(1/20) * (2*Real.pi) ≤ (P.κ c).im * (Real.pi + ζ₀.arg) := by
        by_cases h : 0 ≤ (P.κ c).im
        · nlinarith [hκim_lb, harg_lb, h, Real.pi_pos]
        · push_neg at h
          nlinarith [hκim_ub, harg_ub, h, Real.pi_pos]
      have h1' : -(Real.exp (3*R/2) / (Real.exp (3*R) + 1)) ≥ -(1/100) := by linarith
      have h3 : (P.κ c).re * Real.log ‖ζ₀‖ ≤ (21/20) * (3*R/2 + Real.log 2 / 2) := by
        nlinarith [hκre_ub, hlog_ub]
      linarith
    have hWin_ub : (Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀)).re
        ≤ Real.pi / P.lam c - R := by
      have h1 : (Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀)).re ≤ M'.re + 1/10 := by
        have h := Complex.re_le_norm (Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - M')
        simp only [Complex.sub_re] at h
        linarith [herr']
      have h2 : M'.re + 1/10 ≤ Real.pi / P.lam c - R := by
        nlinarith [hMre_ub, Real.pi_lt_four, hR]
      linarith
    have hWin_lb : Real.pi / P.lam c - 2 * R
        ≤ (Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀)).re := by
      have h1 : M'.re - 1/10 ≤ (Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀)).re := by
        have h := Complex.abs_re_le_norm (Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - M')
        simp only [Complex.sub_re] at h
        have := (abs_le.mp h).1
        linarith [herr']
      have h2 : Real.pi / P.lam c - 2 * R ≤ M'.re - 1/10 := by
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
          linarith
        nlinarith [hMre_lb, Real.pi_lt_four, hR, hlog2]
      linarith
    have hWin : (P.m c + P.s c * ζ₀) ∈ Work.PARIMPL.Win P R c := by
      rw [Work.PARIMPL.mem_Win]
      exact ⟨hWin_lb, hWin_ub⟩
    set Bb : ℂ := (Real.pi / P.lam c : ℂ) + (Real.pi : ℂ) * Complex.I * P.κ c
        + 1 / Work.PARIMPL.chartZeta P c (P.m c + P.s c * ζ₀)
        - P.κ c * Complex.log (Work.PARIMPL.chartZeta P c (P.m c + P.s c * ζ₀)) with hBb
    have hbnd : ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - Bb‖ ≤ 1 := by
      rw [hBb]
      exact hM c ⟨hcNm, hcball⟩ _ hWin
    have hMdiff : M' - Bb = -(2 * (Real.pi : ℂ) * Complex.I * P.κ c) := by
      rw [hBb, hM', hzeta_eq, hpi]
      push_cast
      ring
    have hnormM'diff : ‖M' - Bb‖ = 2 * Real.pi * ‖P.κ c‖ := by
      rw [hMdiff, norm_neg]
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have htri : ‖M' - Bb‖ ≤ ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - M'‖
        + ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - Bb‖ := by
      calc ‖M' - Bb‖
          = ‖(M' - Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀))
              + (Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - Bb)‖ := by ring_nf
        _ ≤ ‖M' - Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀)‖
              + ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - Bb‖ := norm_add_le _ _
        _ = ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - M'‖
              + ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - Bb‖ := by
            rw [norm_sub_rev]
    have hκge : 1 - 1/20 ≤ ‖P.κ c‖ := by
      have h := abs_norm_sub_norm_le (P.κ c) 1
      rw [norm_one] at h
      have := (abs_le.mp h).1
      linarith [hcκ]
    have hlow : 1 < ‖Work.PARIMPL.approxUin P c (P.m c + P.s c * ζ₀) - Bb‖ := by
      have h3 : 2 * Real.pi * (1 - 1/20) ≤ ‖M' - Bb‖ := by
        rw [hnormM'diff]
        nlinarith [hκge, Real.pi_pos]
      nlinarith [htri, herr', h3, Real.pi_gt_three]
    exact absurd hbnd (not_le.mpr hlow)
  exact hcontra.elim

end Work.PARIMPL2
