import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea6Hecke.R.baseLowerNegTwoUniform
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound
import Submission.Work.FIArea5.HeckeZFR.DigammaShift
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea6Hecke.R.digamma_re_ge_of_half_le
import Submission.Port.LogDerivCompat

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex
open scoped Topology

noncomputable section

/-- Arithmetic absorption at the base line: for `C > 0`,
`log(2+|γ|) + 8 + C ≤ (C+9)·log(4d(|m|+|γ|+3))`.  (Local copy of the arithmetic step of
`R/baseLowerTwo`.) -/
private lemma log_absorb_two_local (d : ℕ) (m : ℤ) (γ C : ℝ) (hd : 1 ≤ d) (hC : 0 < C) :
    Real.log (2 + |γ|) + 8 + C ≤ (C + 9) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
  set L : ℝ := Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) with hL
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
  have h12 : (12 : ℝ) ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3) := by nlinarith
  have hL1 : 1 ≤ L := by
    have hlog : Real.log 12 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) :=
      Real.log_le_log (by norm_num) h12
    have h1 : (1 : ℝ) ≤ Real.log 12 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 12)]
      linarith [Real.exp_one_lt_d9]
    rw [hL]; linarith
  have hLge : Real.log (2 + |γ|) ≤ L := by
    have hle : 2 + |γ| ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3) := by nlinarith
    have hlog := Real.log_le_log (by positivity) hle
    rw [hL]; exact hlog
  have h2 : 0 ≤ (C + 8) * (L - 1) := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ L - Real.log (2 + |γ|) := by linarith
  nlinarith [h2, h3]

/-- **The *uniform* lower bound for `Re (Λ'/Λ)` at the base line `re s = 2`.**  The per-datum version is `Work.FIArea6Hecke.R.baseLowerTwo` (proved, `R/baseLowerTwo.lean`), whose constant depends on the datum; the weighted zero sum of `wzsOfPfDiff` and hence the target `logDerivReLower` need a constant valid simultaneously for all data.  Route: on `re s = 2` one has `Λ = heckeArch · L` (identity theorem, `Lam_eq_heckeArch_mul_of_one_lt_re`), `logDeriv Λ = logDeriv heckeArch + logDeriv L`, the archimedean term is `log(4d/π) + ψ(2+|m|/2+iγ)` with `Re ψ(2+|m|/2+iγ) ≥ -(log(2+|γ|) + 8)` (`Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound`, as used privately in `R/baseLowerTwo`), and `|Re (L'/L)(2+iγ)| ≤ ‖(L'/L)(2+iγ)‖ ≤ C` with the *uniform* constant `Work.FIArea6Hecke.R.logDerivLSeriesUniformReGeTwo` (`R/baseLowerNegTwoUniform`); the leftover `log(2+|γ|) + 8 + log(4d/π)` is absorbed by `Work.FIArea6Hecke.R.log_absorb_three` (`R/baseLowerNegTwo.lean`). -/
theorem baseLowerTwoUniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      Work.FIArea6Hecke.R.IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨CL, hCLpos, hCL⟩ := logDerivLSeriesUniformReGeTwo
  refine ⟨CL + 9, by linarith, ?_⟩
  intro d chi m Lam hadm γ
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  set s : ℂ := (2 : ℂ) + (γ : ℂ) * Complex.I with hs
  have hsre : s.re = 2 := by simp [s]
  have hs1 : (1 : ℝ) < s.re := by rw [hsre]; norm_num
  have hspos : 0 < s.re := by rw [hsre]; norm_num
  have hlogpos : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
    nlinarith
  by_cases hzero : Lam s = 0
  · rw [hzero, div_zero]
    simp only [Complex.zero_re]
    have : 0 ≤ (CL + 9) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) :=
      mul_nonneg (by linarith) hlogpos
    linarith
  · have hmodel : Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
      Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hs1
    have hev : Lam =ᶠ[𝓝 s] (fun z => Work.FITop4.Bridge.heckeArch d m z *
        Work.FIArea5.S16Hecke.heckeLSeries chi m z) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with z hz
      exact Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hz
    have hder : deriv Lam s = deriv (fun z => Work.FITop4.Bridge.heckeArch d m z *
        Work.FIArea5.S16Hecke.heckeLSeries chi m z) s := Filter.EventuallyEq.deriv_eq hev
    rw [hder, hmodel]
    have hfne : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
      fun h0 => hzero (by rw [hmodel, h0, zero_mul])
    have hgne : Work.FIArea5.S16Hecke.heckeLSeries chi m s ≠ 0 :=
      Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs1
    have hdf : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s :=
      heckeArch_differentiableAt_of_pos hd m hspos
    have habs : LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (s.re : EReal) :=
      lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
        (EReal.coe_lt_coe_iff.mpr (by rw [hsre]; norm_num))
    have hdg : DifferentiableAt ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m) s :=
      (LSeries_hasDerivAt (f := Work.FIArea5.S16Hecke.heckeLam chi m) (s := s) habs).differentiableAt
    have hsplit' : deriv (fun z => Work.FITop4.Bridge.heckeArch d m z *
          Work.FIArea5.S16Hecke.heckeLSeries chi m z) s
          / (Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
        = logDeriv (Work.FITop4.Bridge.heckeArch d m) s
          + logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s := by
      rw [← logDeriv_apply, Submission.Port.logDeriv_mul_fun s hfne hgne hdf hdg]
    rw [hsplit']
    have hne : ∀ n : ℕ, s + ((|(m : ℝ)| / 2 : ℝ) : ℂ) ≠ -((n : ℕ) : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.natCast_re] at hre
      have hmm : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
      have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hsre] at hre
      linarith
    have harch : logDeriv (Work.FITop4.Bridge.heckeArch d m) s
        = Complex.log (4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))
          + Complex.digamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) :=
      logDeriv_heckeArch d hd m hne
    rw [harch, Complex.add_re, Complex.add_re]
    have hlogarch : 0 ≤ (Complex.log (4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))).re := by
      rw [Complex.log_re]
      refine Real.log_nonneg ?_
      have hnorm : ‖(4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))‖ = 4 * (d : ℝ) / Real.pi := by
        rw [show (4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))
            = ((4 * (d : ℝ) / Real.pi : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hnorm, le_div_iff₀ Real.pi_pos]
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith [Real.pi_lt_four]
    have hdig : -(Real.log (2 + |γ|) + 8)
        ≤ (Complex.digamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ))).re := by
      have harg : s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)
          = (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I := by
        rw [hs]; push_cast; ring
      rw [harg]
      exact digamma_re_ge_of_half_le (2 + |(m : ℝ)| / 2) γ
        (by have h := abs_nonneg (m : ℝ); linarith)
    have hLd : -CL ≤ (logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s).re := by
      rw [logDeriv_apply]
      have h1' : ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
          / Work.FIArea5.S16Hecke.heckeLSeries chi m s‖ ≤ CL :=
        hCL d chi m hd hchi s (by rw [hsre])
      have h2 : -(‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
          / Work.FIArea5.S16Hecke.heckeLSeries chi m s‖)
          ≤ (deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
            / Work.FIArea5.S16Hecke.heckeLSeries chi m s).re :=
        (abs_le.mp (Complex.abs_re_le_norm _)).1
      linarith
    have habsorb := log_absorb_two_local d m γ CL hd hCLpos
    linarith

end

end Work.FIArea6Hecke.R
