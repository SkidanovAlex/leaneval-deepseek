/-
# `Submission.Work.FIArea6Hecke.R.HeckePrincipalLogDerivOffAxisSharp`

The **sharp off-axis logarithmic-derivative bound for the principal Hecke `L`-function**
`L(s, 1)` of `ℚ(i)`, i.e. for `L(s, principalStrict d) = Σ_n λ_d(n) n^{-s}`:

  `-Re(L'/L)(σ + iτ) ≤ 1/(2(σ-1)) + C·log(4d(2 + |τ|))`

for every `d ≥ 1`, every `1 < σ ≤ 2` and every `τ` with `σ - 1 ≤ |τ|`, with `C` absolute.

## Why this is the sharp form

The principal Hecke `L`-function factors classically as

  `L(s,1) = ζ(s)·L(s,χ₄)·G_d(s)`,   `G_d(s) = ∏_{p ∣ 4d}(1 - p^{-s})(1 - χ₄(p)p^{-s})`
  (`ζ·L(·,χ₄) = ζ_{ℚ(i)}` is the Dedekind zeta function of `ℚ(i)`),

which is `heckeLSeries_principalStrict_eq` of `R/heckeLSeries_principalStrict_eq`; the logarithmic
derivative therefore splits into the three logarithmic derivatives of `ζ`, `L(·,χ₄)` and `G_d`
(`logDeriv_heckeLSeries_principalStrict_eq` below, on `re s > 1`).

* `ζ`: the pole of `-ζ'/ζ` at `s = 1` contributes exactly `Re(1/(s-1)) = (σ-1)/((σ-1)²+τ²)`, which
  the hypothesis `σ - 1 ≤ |τ|` bounds by `1/(2(σ-1))` — this is where the constant `1/2` (the
  *sharp* part of the bound) comes from; everything else is `O(log(2+|τ|))`.  This is
  `zeta_logDeriv_re_offAxis_sharp` below, proved from the completed `ξ`-function bound
  `Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general` and the vertical digamma bound
  (`logDerivRe_eq`, `digamma_vertical_bound`).
* `L(·,χ₄)`: entire, non-vanishing on `re s ≥ 1`, with `-Re(L'/L)(σ+iτ) ≤ C(log(2+|τ|)+1)`
  (`R/Sharp/Chi4LSeriesOffAxisLogDerivReBound`).
* `G_d`: a finite product over the primes dividing `4d`, with `-Re(G_d'/G_d) ≤ C·log(4d)`
  (`R/Sharp/AxisBadPolyOffAxisLogDerivReBound`).

Adding the three and using `log(2+|τ|) ≤ log(4d(2+|τ|))` and `log(4d) ≤ log(4d(2+|τ|))` gives the
claimed bound with an absolute constant.

This is the off-axis companion of the real-axis bound `R/HeckeAxisLogDerivBound`
(`-Re(L'/L)(σ) ≤ 1/(σ-1) + C₁`) and the *sharpening* of the request
`R/HeckePrincipalLogDerivOffAxisBound`, which asks for the same conclusion under the weaker
hypothesis `1/(σ-1) ≤ |τ|` (a subset of the region `σ - 1 ≤ |τ|` treated here).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.Sharp.Chi4LSeriesOffAxisLogDerivReBound
import Submission.Work.FIArea6Hecke.R.Sharp.AxisBadPolyOffAxisLogDerivReBound
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIArea6Hecke.R

open Complex Filter
open scoped Topology

noncomputable section

/-- Elementary: for `s = σ + iτ` with `σ > 1` and `σ - 1 ≤ |τ|`, the real part of `1/(s-1)`
is at most `1/(2(σ-1))` (the pole of `-ζ'/ζ` at `s = 1`, `τ = 0` is quartered by the
off-axis hypothesis). -/
private lemma re_inv_sub_one_le (σ τ : ℝ) (hσ : 1 < σ) (hτ : σ - 1 ≤ |τ|) :
    (1 / (((σ : ℂ) + (τ : ℂ) * Complex.I) - 1)).re ≤ 1 / (2 * (σ - 1)) := by
  have ha : 0 < σ - 1 := by linarith
  have hre : (((σ : ℂ) + (τ : ℂ) * Complex.I) - 1).re = σ - 1 := by simp
  have him : (((σ : ℂ) + (τ : ℂ) * Complex.I) - 1).im = τ := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hre, him]
  have ht2 : (σ - 1) ^ 2 ≤ τ ^ 2 := by
    have h : σ - 1 ≤ |τ| := hτ
    nlinarith [h, abs_nonneg τ, sq_abs τ, ha]
  rw [div_le_div_iff₀ (by nlinarith [sq_nonneg (σ - 1), sq_nonneg τ]) (by linarith)]
  nlinarith [ht2, ha]

/-- **Sharp off-axis logarithmic-derivative bound for `ζ`.**  For `1 < σ ≤ 2` and
`σ - 1 ≤ |τ|`,

  `-Re(ζ'/ζ)(σ + iτ) ≤ 1/(2(σ-1)) + C·log(2 + |τ|)`,

with `C` absolute.  The pole term is exactly `Re(1/(s-1)) ≤ 1/(2(σ-1))`, the remaining
terms (the completed `ξ`-function and the digamma factor) contributing `O(log(2+|τ|))`. -/
theorem zeta_logDeriv_re_offAxis_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 → σ - 1 ≤ |τ| →
      (-deriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)
        / riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
        ≤ 1 / (2 * (σ - 1)) + C * Real.log (2 + |τ|) := by
  obtain ⟨Cξ, hCξpos, hξ⟩ := Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Cξ + 4) / Real.log 2 + 1, by positivity, ?_⟩
  intro σ τ hσ1 hσ2 hτ
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have h1s : (1 : ℝ) < s.re := by rw [hsre]; exact hσ1
  have hlogpi : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    rw [show Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) from
      (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm]
    simp
  have hd : (1 / 2 : ℝ) * (Complex.digamma (1 + s / 2)).re
      ≤ (1 / 2 : ℝ) * (Real.log (2 + |τ|) + 8) := by
    have harg : 1 + s / 2 = ((1 + σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; apply Complex.ext <;> simp <;> ring
    rw [harg]
    have hb := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      (1 + σ / 2) (τ / 2) (by linarith) (by linarith)
    have hrele : (Complex.digamma (((1 + σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re
        ≤ Real.log (2 + |τ / 2|) + 8 := le_trans (Complex.re_le_norm _) hb
    have hlog : Real.log (2 + |τ / 2|) ≤ Real.log (2 + |τ|) := by
      apply Real.log_le_log (by positivity)
      have h : |τ / 2| ≤ |τ| := by rw [abs_div]; norm_num
      linarith
    linarith
  have hxi : -Cξ ≤ (logDeriv Commons.NumberTheory.Zeta.xi s).re := hξ s h1s
  have hinv : (1 / (s - 1)).re ≤ 1 / (2 * (σ - 1)) := by
    rw [hs]
    exact re_inv_sub_one_le σ τ hσ1 hτ
  have hlogpi0 : 0 ≤ (Complex.log (Real.pi : ℂ)).re := by
    rw [hlogpi]; exact Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hLge : Real.log 2 ≤ Real.log (2 + |τ|) := by
    apply Real.log_le_log (by norm_num); linarith [abs_nonneg τ]
  have hLpos : 0 < Real.log (2 + |τ|) := lt_of_lt_of_le hlog2pos hLge
  have hkey : Cξ + (1 / 2 : ℝ) * (Real.log (2 + |τ|) + 8)
      ≤ ((Cξ + 4) / Real.log 2 + 1) * Real.log (2 + |τ|) := by
    have h1 : Cξ + 4 = ((Cξ + 4) / Real.log 2) * Real.log 2 := by
      rw [div_mul_cancel₀]; exact ne_of_gt hlog2pos
    have h2 : ((Cξ + 4) / Real.log 2) * Real.log 2 ≤ ((Cξ + 4) / Real.log 2) * Real.log (2 + |τ|) :=
      mul_le_mul_of_nonneg_left hLge (by positivity)
    nlinarith [h1, h2, hLpos, hLge, hCξpos, hlog2pos]
  have hre := Commons.NumberTheory.Zeta.logDerivRe_eq s h1s
  rw [hre]
  linarith [hxi, hd, hinv, hlogpi0, hkey]

/-! ## 2. The logarithmic derivative of the principal Hecke `L`-series -/

/-- The logarithmic derivative of the principal Hecke `L`-series splits as the sum of the
logarithmic derivatives of `ζ`, `L(·,χ₄)` and the bad-prime correction `G_d` on `re s > 1`
(the logarithmic derivative of the factorisation
`L(s,1) = ζ(s)·L(s,χ₄)·G_d(s)`). -/
lemma logDeriv_heckeLSeries_principalStrict_eq {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0) s
      = logDeriv riemannZeta s + logDeriv (LSeries Work.FIArea6Hecke.R.axisChi4) s
        + logDeriv (Work.FIArea6Hecke.R.axisBadPoly d) s := by
  have hL : Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0
      =ᶠ[nhds s] (fun z => riemannZeta z * LSeries Work.FIArea6Hecke.R.axisChi4 z
        * Work.FIArea6Hecke.R.axisBadPoly d z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq d hd hz
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hL4 : LSeries Work.FIArea6Hecke.R.axisChi4 s ≠ 0 :=
    Work.FIArea6Hecke.R.LSeries_axisChi4_ne_zero hs
  have hG : Work.FIArea6Hecke.R.axisBadPoly d s ≠ 0 :=
    Work.FIArea6Hecke.R.axisBadPoly_ne_zero d hs
  have hζd : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (by
      intro h
      have h1 : s.re = 1 := by rw [h]; simp
      linarith)
  have hL4d : DifferentiableAt ℂ (LSeries Work.FIArea6Hecke.R.axisChi4) s :=
    Work.FIArea6Hecke.R.differentiableAt_LSeries_axisChi4 hs
  have hGd : DifferentiableAt ℂ (Work.FIArea6Hecke.R.axisBadPoly d) s :=
    Work.FIArea6Hecke.R.differentiableAt_axisBadPoly d s
  rw [show logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0) s
      = logDeriv (fun z => riemannZeta z * LSeries Work.FIArea6Hecke.R.axisChi4 z
          * Work.FIArea6Hecke.R.axisBadPoly d z) s
      from (logDeriv_congr_nhds hL).eq_of_nhds]
  rw [Submission.Port.logDeriv_mul_fun (f := fun z => riemannZeta z * LSeries Work.FIArea6Hecke.R.axisChi4 z)
        (g := Work.FIArea6Hecke.R.axisBadPoly d) s (mul_ne_zero hζ hL4) hG
        (hζd.mul hL4d) hGd,
      Submission.Port.logDeriv_mul_fun (f := riemannZeta) (g := fun z => LSeries Work.FIArea6Hecke.R.axisChi4 z) s
        hζ hL4 hζd hL4d]

/-! ## 3. The target -/

/-- **The sharp off-axis logarithmic-derivative bound for the principal Hecke `L`-function of
`ℚ(i)`** (see the module docstring). -/
theorem HeckePrincipalLogDerivOffAxisSharp :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 → σ - 1 ≤ |τ| →
        (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)
          / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0
            ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
          ≤ 1 / (2 * (σ - 1)) + C * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
  obtain ⟨Cζ, hCζpos, hζ⟩ := zeta_logDeriv_re_offAxis_sharp
  obtain ⟨Cχ, hCχpos, hχ⟩ := Sharp.Chi4LSeriesOffAxisLogDerivReBound
  obtain ⟨CG, hCGpos, hG⟩ := Sharp.AxisBadPolyOffAxisLogDerivReBound
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Cζ + Cχ * (1 + 1 / Real.log 2) + CG, by positivity, ?_⟩
  intro d hd σ τ hσ1 hσ2 hτ
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : 1 < s.re := by rw [hsdef]; simp; exact hσ1
  have hld := logDeriv_heckeLSeries_principalStrict_eq hd hsre
  have key : -(logDeriv (Work.FIArea5.S16Hecke.heckeLSeries
        (Work.FIArea6Hecke.principalStrict d) 0) s)
      = -logDeriv riemannZeta s + -logDeriv (LSeries Work.FIArea6Hecke.R.axisChi4) s
        + -logDeriv (Work.FIArea6Hecke.R.axisBadPoly d) s := by
    rw [hld]; ring
  have e0 : -deriv (Work.FIArea5.S16Hecke.heckeLSeries
        (Work.FIArea6Hecke.principalStrict d) 0) s
      / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s
      = -(logDeriv (Work.FIArea5.S16Hecke.heckeLSeries
        (Work.FIArea6Hecke.principalStrict d) 0) s) := by
    rw [logDeriv_apply, neg_div]
  have e1 : -deriv riemannZeta s / riemannZeta s = -(logDeriv riemannZeta s) := by
    rw [logDeriv_apply, neg_div]
  have e2 : -deriv (LSeries Work.FIArea6Hecke.R.axisChi4) s
      / LSeries Work.FIArea6Hecke.R.axisChi4 s
      = -(logDeriv (LSeries Work.FIArea6Hecke.R.axisChi4) s) := by
    rw [logDeriv_apply, neg_div]
  have e3 : -deriv (Work.FIArea6Hecke.R.axisBadPoly d) s
      / Work.FIArea6Hecke.R.axisBadPoly d s
      = -(logDeriv (Work.FIArea6Hecke.R.axisBadPoly d) s) := by
    rw [logDeriv_apply, neg_div]
  have hdec : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries
        (Work.FIArea6Hecke.principalStrict d) 0) s
      / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s).re
      = (-deriv riemannZeta s / riemannZeta s).re
        + (-deriv (LSeries Work.FIArea6Hecke.R.axisChi4) s
            / LSeries Work.FIArea6Hecke.R.axisChi4 s).re
        + (-deriv (Work.FIArea6Hecke.R.axisBadPoly d) s
            / Work.FIArea6Hecke.R.axisBadPoly d s).re := by
    rw [e0, e1, e2, e3, key]
    simp only [Complex.add_re]
  rw [hdec]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hτnn : 0 ≤ |τ| := abs_nonneg τ
  have hLpos : 0 < Real.log (2 + |τ|) := Real.log_pos (by linarith)
  have hMpos : 0 < Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    apply Real.log_pos; nlinarith [hτnn, hd1]
  have hLM : Real.log (2 + |τ|) ≤ Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    apply Real.log_le_log (by linarith)
    nlinarith [hτnn, hd1]
  have h4dM : Real.log (4 * (d : ℝ)) ≤ Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [hτnn]
  have hLge : Real.log 2 ≤ Real.log (2 + |τ|) := by
    refine Real.log_le_log (by norm_num) (by linarith [hτnn])
  have hLratio : (1 : ℝ) ≤ Real.log (2 + |τ|) / Real.log 2 :=
    (one_le_div hlog2pos).mpr hLge
  have hb1 : (-deriv riemannZeta s / riemannZeta s).re
      ≤ 1 / (2 * (σ - 1)) + Cζ * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    have h := hζ σ τ hσ1 hσ2 hτ
    rw [← hsdef] at h
    have : Cζ * Real.log (2 + |τ|) ≤ Cζ * Real.log (4 * (d : ℝ) * (2 + |τ|)) :=
      mul_le_mul_of_nonneg_left hLM (le_of_lt hCζpos)
    linarith [h, this]
  have hb2 : (-deriv (LSeries Work.FIArea6Hecke.R.axisChi4) s
        / LSeries Work.FIArea6Hecke.R.axisChi4 s).re
      ≤ Cχ * (1 + 1 / Real.log 2) * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    have h := hχ σ τ hσ1 hσ2
    rw [← hsdef] at h
    have hstep : Real.log (2 + |τ|) + 1 ≤ (1 + 1 / Real.log 2) * Real.log (2 + |τ|) := by
      have h1 : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (2 + |τ|) := by
        simpa [div_eq_inv_mul, one_div, mul_comm] using hLratio
      have h2 : (1 + 1 / Real.log 2) * Real.log (2 + |τ|)
          = Real.log (2 + |τ|) + (1 / Real.log 2) * Real.log (2 + |τ|) := by ring
      linarith [h1, h2.le, h2.ge]
    have h1 : Cχ * (Real.log (2 + |τ|) + 1)
        ≤ Cχ * ((1 + 1 / Real.log 2) * Real.log (2 + |τ|)) :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt hCχpos)
    have h2 : Cχ * ((1 + 1 / Real.log 2) * Real.log (2 + |τ|))
        ≤ Cχ * (1 + 1 / Real.log 2) * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
      have h3 : (0 : ℝ) ≤ Cχ * (1 + 1 / Real.log 2) := by positivity
      calc Cχ * ((1 + 1 / Real.log 2) * Real.log (2 + |τ|))
          = Cχ * (1 + 1 / Real.log 2) * Real.log (2 + |τ|) := by ring
        _ ≤ Cχ * (1 + 1 / Real.log 2) * Real.log (4 * (d : ℝ) * (2 + |τ|)) :=
            mul_le_mul_of_nonneg_left hLM h3
    linarith [h, h1, h2]
  have hb3 : (-deriv (Work.FIArea6Hecke.R.axisBadPoly d) s
        / Work.FIArea6Hecke.R.axisBadPoly d s).re
      ≤ CG * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    have h := hG d hd σ τ hσ1 hσ2
    rw [← hsdef] at h
    have : CG * Real.log (4 * (d : ℝ)) ≤ CG * Real.log (4 * (d : ℝ) * (2 + |τ|)) :=
      mul_le_mul_of_nonneg_left h4dM (le_of_lt hCGpos)
    linarith [h, this]
  linarith [hb1, hb2, hb3]

end

end Work.FIArea6Hecke.R
