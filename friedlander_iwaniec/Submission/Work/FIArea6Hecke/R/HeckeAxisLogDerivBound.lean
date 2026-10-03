/-
# `Submission.Work.FIArea6Hecke.R.HeckeAxisLogDerivBound`

The real-axis logarithmic-derivative bound for the principal Hecke `L`-function
`L(s,1) = LSeries (heckeLam (principalStrict d) 0)` of `ℚ(i)`:

  `-Re(L'/L)(σ) ≤ 1/(σ-1) + C₁`   for `1 < σ ≤ 2` and every `d ≥ 1`,
with `C₁` an absolute constant.

This is item 3 of the plan for the real-axis zero-free region
(`Submission/Work/FIArea6Hecke/R/heckeZFRrealAxis.lean`), where it is used together with the
`(3,4,1)` inequality and `HeckeLambdaLogDerivBounds`.

## Proof

The classical decomposition of the principal Hecke `L`-function

  `L(s,1) = ζ(s)·L(s,χ₄)·G_d(s)`,   `G_d(s) = ∏_{p ∣ 4d} (1 - p^{-s})(1 - χ₄(p)p^{-s})`

(`ζ·L(·,χ₄) = ζ_{ℚ(i)}`, the Dedekind zeta function of `ℚ(i)`; `G_d` removes the Euler factors
at the primes dividing `4d`, at which `principalStrict d` vanishes) turns the logarithmic
derivative into a sum of three logarithmic derivatives, for `1 < σ ≤ 2`:

* `-Re(ζ'/ζ)(σ) ≤ 1/(σ-1) + C_ζ` — `Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound`;
* `-Re(L(·,χ₄)'/L(·,χ₄))(σ) ≤ C_χ` — the log-derivative of the entire function `L(·,χ₄)` near
  the compact segment `[1,2]`, on which `L(·,χ₄)` does not vanish
  (`Work.FIArea6Hecke.R.axisChi4_LSeries_facts`);
* `-Re(G_d'/G_d)(σ) ≤ 0` — each Euler factor `(1-p^{-σ})(1-χ₄(p)p^{-σ})` is increasing in `σ`
  (`Work.FIArea6Hecke.R.axisBadPoly_logDeriv_re_nonpos`).

The identity itself is `Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq`, proved from the
Euler products of `L(·,1)` and of ζ, `L(·,χ₄)`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.axisBadPoly_logDeriv_re_nonpos
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Port.LogDerivCompat

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Filter
open scoped BigOperators Topology

noncomputable section

theorem HeckeAxisLogDerivBound :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (d : ℕ), 1 ≤ d → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
          ((σ : ℂ)) / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0
          ((σ : ℂ))).re ≤ 1 / (σ - 1) + C₁ := by
  obtain ⟨Cζ, hCζpos, hζ⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  obtain ⟨hχdiff, hχne, Cχ, hCχ0, hχ⟩ := axisChi4_LSeries_facts
  refine ⟨max 0 (Cζ + Cχ), le_max_left 0 _, ?_⟩
  intro d hd σ hσ1 hσ2
  have hσre : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ1
  -- the product decomposition of `L(s,1)` near `s = σ`
  have hL : Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 =ᶠ[𝓝 (σ : ℂ)]
      (fun s => riemannZeta s * LSeries axisChi4 s * axisBadPoly d s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσre] with s hs
    exact heckeLSeries_principalStrict_eq d hd hs
  have hζne : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hσre
  have hχne' : LSeries axisChi4 (σ : ℂ) ≠ 0 := hχne (σ : ℂ) hσre
  have hGne : axisBadPoly d (σ : ℂ) ≠ 0 := axisBadPoly_ne_zero d hσre
  have hζdiff : DifferentiableAt ℂ riemannZeta (σ : ℂ) :=
    differentiableAt_riemannZeta (by
      intro h
      have h1 : (σ : ℂ).re = 1 := by rw [h]; simp
      rw [Complex.ofReal_re] at h1
      linarith)
  have hχdiff' : DifferentiableAt ℂ (LSeries axisChi4) (σ : ℂ) := hχdiff (σ : ℂ) hσre
  have hGdiff : DifferentiableAt ℂ (axisBadPoly d) (σ : ℂ) :=
    differentiableAt_axisBadPoly d (σ : ℂ)
  -- the logarithmic derivative of the product
  have hlog : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
        (σ : ℂ)
      = logDeriv riemannZeta (σ : ℂ) + logDeriv (LSeries axisChi4) (σ : ℂ)
        + logDeriv (axisBadPoly d) (σ : ℂ) := by
    rw [show logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
          (σ : ℂ) = logDeriv (fun s => riemannZeta s * LSeries axisChi4 s * axisBadPoly d s)
          (σ : ℂ) from (logDeriv_congr_nhds hL).eq_of_nhds]
    rw [Submission.Port.logDeriv_mul_fun (f := fun s => riemannZeta s * LSeries axisChi4 s) (g := axisBadPoly d) (σ : ℂ)
        (mul_ne_zero hζne hχne') hGne (hζdiff.mul hχdiff') hGdiff,
      Submission.Port.logDeriv_mul_fun (f := riemannZeta) (g := fun s => LSeries axisChi4 s) (σ : ℂ)
        hζne hχne' hζdiff hχdiff']
  have e1 : logDeriv riemannZeta (σ : ℂ) = deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) :=
    logDeriv_apply riemannZeta (σ : ℂ)
  have e2 : logDeriv (LSeries axisChi4) (σ : ℂ)
      = deriv (LSeries axisChi4) (σ : ℂ) / LSeries axisChi4 (σ : ℂ) :=
    logDeriv_apply (LSeries axisChi4) (σ : ℂ)
  have e3 : logDeriv (axisBadPoly d) (σ : ℂ)
      = deriv (axisBadPoly d) (σ : ℂ) / axisBadPoly d (σ : ℂ) :=
    logDeriv_apply (axisBadPoly d) (σ : ℂ)
  -- the three logarithmic derivatives, bounded
  have hfinal : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
        (σ : ℂ) / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 (σ : ℂ)).re
      ≤ 1 / (σ - 1) + (Cζ + Cχ) := by
    have hlog2 : -(deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
          (σ : ℂ) / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 (σ : ℂ))
        = -(logDeriv riemannZeta (σ : ℂ) + logDeriv (LSeries axisChi4) (σ : ℂ)
            + logDeriv (axisBadPoly d) (σ : ℂ)) := by
      rw [← logDeriv_apply (Work.FIArea5.S16Hecke.heckeLSeries
        (Work.FIArea6Hecke.principalStrict d) 0) (σ : ℂ), hlog]
    rw [neg_div, hlog2]
    simp only [Complex.neg_re, Complex.add_re]
    rw [e1, e2, e3]
    have h1 := hζ σ hσ1 hσ2
    have h2 := hχ σ hσ1 hσ2
    have h3 := axisBadPoly_logDeriv_re_nonpos d hd hσ1
    rw [neg_div, Complex.neg_re] at h1 h2 h3
    linarith
  calc (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
        (σ : ℂ) / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 (σ : ℂ)).re
      ≤ 1 / (σ - 1) + (Cζ + Cχ) := hfinal
    _ ≤ 1 / (σ - 1) + max 0 (Cζ + Cχ) := by
        have := le_max_right (0 : ℝ) (Cζ + Cχ)
        linarith

end

end Work.FIArea6Hecke.R
