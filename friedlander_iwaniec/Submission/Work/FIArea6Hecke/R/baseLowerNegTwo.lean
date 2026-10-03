import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea5.HeckeZFR.FELogDeriv
import Submission.Work.FIArea6Hecke.R.noCompletionOfPsiTrivial
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea5.HeckeZFR.DigammaShift
import Submission.Work.FIArea6Hecke.R.HasConductorFEDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.mellin_cut_props
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs
import Submission.Work.FIArea6Hecke.R.thetaHol_meas_li
import Submission.Work.FIArea6Hecke.R.levCutFacts
import Submission.Work.FIArea6Hecke.R.levLowConv
import Submission.Work.FIArea6Hecke.R.levLowMellin
import Submission.Work.FIArea6Hecke.R.levMellinSplit
import Submission.Work.FIArea6Hecke.R.levXiReflect
import Submission.Work.FIArea6Hecke.R.thetaLamAgree
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay
import Submission.Work.FIArea6Hecke.R.levelThetaFE
import Submission.Work.FIArea6Hecke.R.conductorFECleanNoDep
import Submission.Work.FIArea6Hecke.R.sum_log_primes_le
import Submission.Work.FIArea6Hecke.R.cpow_norm_eval_points
import Submission.Work.FIArea6Hecke.R.norm_logDeriv_one_sub_mul_cpow_le
import Submission.Port.LogDerivCompat

/-!
# `Submission.Work.FIArea6Hecke.R.baseLowerNegTwo`

The lower bound for the real part of `Λ'/Λ` at the auxiliary base point `re s = -2`.

For a strict character `χ` mod `4d` and any `m : ℤ`, let `Λ` be an entire completion of
`Λ(s,ψ) = (4d/π)^sΓ(s+|m|/2)L(s,ψ)`, `ψ(z) = χ(z)(z/|z|)^m` (the hypothesis `IsCompleted`).
The bound `Re (Λ'/Λ)(-2+iγ) ≥ -C log(4d(|m|+|γ|+3))` is equivalent, through Hecke's functional
equation `Λ s = W·conj(Λ(conj(1-s)))`, to the bound at `re s = 3` (`Λ'/Λ(-2+iγ) = -conj(Λ'/Λ(3+iγ))`),
where the logarithmic derivative is bounded by the absolutely convergent Dirichlet series.

For an *imprimitive* `χ` the completion at the modulus `4d` does **not** satisfy the unimodular
functional equation: only the primitive partner `χ'` of conductor `𝔪 | (4d)` does, and the passage
from `χ'` to `χ` multiplies by the finitely many Euler factors at the primes `𝔭 | 4d`, `𝔭 ∤ 𝔪`
(they cannot be absorbed into a change of base: the discrepancy is a genuine Euler product, not a
monomial).  This is the input `Work.FIArea6Hecke.R.conductorFEAtBase` (the honest crux, `HasConductorFE`): an entire `Φ` with
the reflected functional equation whose restriction to `re s > 1+|m|/2` is
`(X/π)^sΓ(s+|m|/2)·L(s,ψ)·∏_{p∈S}(1-c₁(p)p^{-s})^{-1}(1-c₂(p)p^{-s})^{-1}`, `X ∈ [1,4d]`, the
`cᵢ(p)` of modulus `1` (or `0`).  Writing `Λ = ((4d/X)^s·corrFac)·Φ` (an identity of entire
functions by the identity theorem) and applying the reflection to `Φ`, the bound at `-2` follows
from the bound at `3` together with the elementary estimate `|Re logDeriv corrFac| ≤ 3 log(4d)` at
the two points `-2+iγ`, `3+iγ` (proved below as `corrFacLogDerivReBound`).

The reduction from that functional-equation package to the target is the lemma
`baseLowerNegTwo_of_FEdata`; it is stated separately so that its (purely analytic) content is
independent of the analytic input proving the conductor-normalised functional equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R
open Complex
open scoped Topology

noncomputable section

open scoped BigOperators

/-- **Two entire functions agreeing on a right half-plane are equal.**  (This is
`Work.FIArea6Hecke.R.eq_of_agrees_right'` of `R/lamGrowth`, reproduced here so that this file does
not depend on an in-flux module.) -/
lemma eq_of_agrees_right_local {G Lam : ℂ → ℂ} {T : ℝ}
    (hG : AnalyticOn ℂ G Set.univ) (hL : AnalyticOn ℂ Lam Set.univ)
    (h : ∀ s : ℂ, T < s.re → Lam s = G s) : Lam = G := by
  have hG' : AnalyticOnNhd ℂ G Set.univ := analyticOn_univ.mp hG
  have hL' : AnalyticOnNhd ℂ Lam Set.univ := analyticOn_univ.mp hL
  have hev : (fun s : ℂ => Lam s - G s) =ᶠ[𝓝 (((T + 1 : ℝ)) : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (((T + 1 : ℝ)) : ℂ) (by norm_num : (0 : ℝ) < 1)]
      with s hs
    have h1 : ‖s - (((T + 1 : ℝ)) : ℂ)‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
    have h2 : |s.re - (T + 1)| ≤ ‖s - (((T + 1 : ℝ)) : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (s - (((T + 1 : ℝ)) : ℂ))
    have h3 : T < s.re := by
      have h4 := lt_of_le_of_lt h2 h1
      rw [abs_lt] at h4
      linarith [h4.1]
    simp [h s h3]
  have hzero : (fun s : ℂ => Lam s - G s) = 0 :=
    AnalyticOnNhd.eq_of_eventuallyEq (hL'.sub hG') (fun z _ => analyticAt_const) hev
  funext s
  exact sub_eq_zero.mp (congrFun hzero s)

/-- Arithmetic absorption for the `re = 3` bound. -/
lemma log_absorb_three (d : ℕ) (m : ℤ) (γ C : ℝ) (hd : 1 ≤ d) (hC : 0 < C) :
    Real.log (2 + |γ|) + 2 * Real.log (12 + 2 * |(m : ℝ)|) + 6 + Real.log (4 * (d : ℝ)) + C
      ≤ (C + 20) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
  set L : ℝ := Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) with hL
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
  have h12 : (12 : ℝ) ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3) := by nlinarith
  have hL12 : Real.log 12 ≤ L := by
    rw [hL]
    exact Real.log_le_log (by norm_num) h12
  have hL1 : 1 ≤ L := by
    have he : Real.exp 1 < 12 := by linarith [Real.exp_one_lt_d9]
    have h1 : (1 : ℝ) ≤ Real.log 12 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 12)]
      exact le_of_lt he
    linarith
  have h1 : Real.log (2 + |γ|) ≤ L := by
    have hle : 2 + |γ| ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3) := by nlinarith
    rw [hL]
    exact Real.log_le_log (by positivity) hle
  have h2 : Real.log (12 + 2 * |(m : ℝ)|) ≤ L := by
    have hle : 12 + 2 * |(m : ℝ)| ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3) := by nlinarith
    rw [hL]
    exact Real.log_le_log (by positivity) hle
  have h3 : Real.log (4 * (d : ℝ)) ≤ L := by
    rw [hL]
    refine Real.log_le_log (by positivity) ?_
    nlinarith
  have h6 : (6 : ℝ) ≤ 6 * L := by linarith
  have hC' : C ≤ C * L := by nlinarith
  have hexp : (C + 20) * L = C * L + 20 * L := by ring
  rw [hexp]
  linarith


/-- **The log-derivative of the completion at `re s = 3`.** -/
lemma logDeriv_completion_at_three_le (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hadm : IsCompleted d chi m Lam)
    (hLb : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
        / Work.FIArea5.S16Hecke.heckeLSeries chi m s‖ ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ,
      (deriv Lam ((3 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((3 : ℂ) + (γ : ℂ) * Complex.I)).re
        ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  obtain ⟨CL, hCLpos, hCL⟩ := hLb
  refine ⟨CL + 20, by linarith, fun γ => ?_⟩
  set s : ℂ := (3 : ℂ) + (γ : ℂ) * Complex.I with hs
  have hsre : s.re = 3 := by simp [s]
  have hs1 : (1 : ℝ) < s.re := by rw [hsre]; norm_num
  have hlogpos : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
    nlinarith
  by_cases hzero : Lam s = 0
  · rw [hzero, div_zero]
    simp only [Complex.zero_re]
    have : (0:ℝ) ≤ (CL + 20) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) :=
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
      heckeArch_ne_zero_of_one_lt_re hd m hs1
    have hgne : Work.FIArea5.S16Hecke.heckeLSeries chi m s ≠ 0 :=
      Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs1
    have hdf : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s :=
      heckeArch_differentiableAt_of_pos hd m (by linarith)
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
        = Complex.log (4 * (d : ℂ) / (Real.pi : ℂ))
          + Complex.digamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) :=
      logDeriv_heckeArch d hd m hne
    rw [harch, Complex.add_re, Complex.add_re]
    have hlogarch : (Complex.log (4 * (d : ℂ) / (Real.pi : ℂ))).re ≤ Real.log (4 * (d : ℝ)) := by
      rw [Complex.log_re]
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hnorm : ‖(4 * (d : ℂ) / (Real.pi : ℂ))‖ = 4 * (d : ℝ) / Real.pi := by
        rw [show (4 * (d : ℂ) / (Real.pi : ℂ)) = ((4 * (d : ℝ) / Real.pi : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
      rw [hnorm]
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ Real.pi_pos]
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith [Real.pi_gt_three]
    have hdig : (Complex.digamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ))).re
        ≤ Real.log (2 + |γ|) + 2 * Real.log (12 + 2 * |(m : ℝ)|) + 6 := by
      have harg : s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)
          = (((3 + |(m : ℝ)| / 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I := by
        rw [hs]; push_cast; ring
      rw [harg]
      have h := Work.FIArea5.S16Hecke.digamma_re_le_of_half_le (3 + |(m : ℝ)| / 2) γ
        (by have h := abs_nonneg (m : ℝ); linarith)
      have hlog : Real.log (4 * (3 + |(m : ℝ)| / 2)) = Real.log (12 + 2 * |(m : ℝ)|) := by
        congr 1; ring
      rw [hlog] at h
      exact h
    have hLd : (logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s).re ≤ CL := by
      rw [logDeriv_apply]
      have h1' : ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
          / Work.FIArea5.S16Hecke.heckeLSeries chi m s‖ ≤ CL := hCL s (by rw [hsre]; norm_num)
      have h2 := (abs_le.mp (Complex.abs_re_le_norm (deriv
        (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
        / Work.FIArea5.S16Hecke.heckeLSeries chi m s))).2
      linarith
    have habsorb := log_absorb_three d m γ CL hd hCLpos
    linarith

/-- The finite Euler-factor correction `∏_{p ∈ S} (1-c₁(p)p^{-s})(1-c₂(p)p^{-s})`. -/
def corrFac (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, ((1 - c₁ p * (p : ℂ) ^ (-s)) * (1 - c₂ p * (p : ℂ) ^ (-s)))

lemma norm_natCast_cpow_neg {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖((n : ℂ) ^ (-s))‖ = (n : ℝ) ^ (-s.re) :=
  Complex.norm_natCast_cpow_of_pos hn (-s)

lemma sub_mul_ne_zero {c w : ℂ} (hc : ‖c‖ = 1 ∨ c = 0) (hw : ‖w‖ ≠ 1) : 1 - c * w ≠ 0 := by
  intro h
  have h1 : c * w = 1 := (sub_eq_zero.mp h).symm
  rcases hc with hc | hc
  · have : ‖c * w‖ = 1 := by rw [h1]; simp
    rw [norm_mul, hc, one_mul] at this
    exact hw this
  · rw [hc, zero_mul] at h1; exact one_ne_zero h1.symm

/-- Every factor of the correction is nonzero when `re s > 1`. -/
lemma corrFac_ne_zero_of_one_lt_re {c₁ c₂ : ℕ → ℂ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0))
    {s : ℂ} (hs : 1 < s.re) : corrFac c₁ c₂ S s ≠ 0 := by
  unfold corrFac
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  obtain ⟨hpp, h1, h2⟩ := hS p hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hlt : (p : ℝ) ^ (-s.re) < 1 := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hneg : -s.re < 0 := by linarith
    exact (Real.rpow_lt_one_iff_of_pos hp0).mpr (Or.inl ⟨hp1, hneg⟩)
  have hne : ‖(((p : ℂ) ^ (-s)) : ℂ)‖ ≠ 1 := by
    rw [norm_natCast_cpow_neg hpp.pos]
    exact ne_of_lt hlt
  exact mul_ne_zero (sub_mul_ne_zero h1 hne) (sub_mul_ne_zero h2 hne)

/-- Every factor of the correction is nonzero at points with `re s ≤ -1`. -/
lemma corrFac_ne_zero_of_re_le_neg_one {c₁ c₂ : ℕ → ℂ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0))
    {s : ℂ} (hs : s.re ≤ -1) : corrFac c₁ c₂ S s ≠ 0 := by
  unfold corrFac
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  obtain ⟨hpp, h1, h2⟩ := hS p hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hgt : 1 < (p : ℝ) ^ (-s.re) := by
    have h0 : (0 : ℝ) < -s.re := by linarith
    exact Real.one_lt_rpow hp1 h0
  have hne : ‖(((p : ℂ) ^ (-s)) : ℂ)‖ ≠ 1 := by
    rw [norm_natCast_cpow_neg hpp.pos]
    exact ne_of_gt hgt
  exact mul_ne_zero (sub_mul_ne_zero h1 hne) (sub_mul_ne_zero h2 hne)

/-- A single local factor `u ↦ 1 - c a^{-u}` is differentiable. -/
lemma differentiableAt_locFac (c : ℂ) {a : ℕ} (ha : a ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (fun u : ℂ => 1 - c * (a : ℂ) ^ (-u)) s := by
  have hane : ((a : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact ha
  exact (DifferentiableAt.sub (differentiableAt_const (1 : ℂ))
    (DifferentiableAt.mul (differentiableAt_const c)
      (((hasDerivAt_neg s).const_cpow (Or.inl hane)).differentiableAt)))

/-- The correction factors are differentiable. -/
lemma differentiableAt_corrFac (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ)
    (hSpos : ∀ p ∈ S, p ≠ 0) (s : ℂ) : DifferentiableAt ℂ (corrFac c₁ c₂ S) s := by
  classical
  induction S using Finset.induction with
  | empty =>
      have h : corrFac c₁ c₂ ∅ = fun _ : ℂ => (1 : ℂ) := by
        funext u; simp [corrFac]
      rw [h]
      exact differentiableAt_const 1
  | insert a S ha ih =>
      have h1 : corrFac c₁ c₂ (insert a S) =
          (fun u : ℂ => (1 - c₁ a * (a : ℂ) ^ (-u))) *
            (fun u : ℂ => (1 - c₂ a * (a : ℂ) ^ (-u))) * corrFac c₁ c₂ S := by
        funext u
        simp only [corrFac, Finset.prod_insert ha, Pi.mul_apply]
      rw [h1]
      exact (differentiableAt_locFac (c₁ a) (hSpos a (Finset.mem_insert_self a S)) s).mul
        (differentiableAt_locFac (c₂ a) (hSpos a (Finset.mem_insert_self a S)) s) |>.mul
        (ih (fun p hp => hSpos p (Finset.mem_insert_of_mem hp)))

/-! ## The logarithmic-derivative bound for the correction product

`corrFac c₁ c₂ S s = ∏_{p∈S}(1-c₁(p)p^{-s})(1-c₂(p)p^{-s})` is the finite product of local Euler
factors encoding the passage from the primitive partner's completion to the completion of `ψ_χ`.
We need `|Re (corrFac'/corrFac)(s)| ≤ 3 log(4d)` at the two points `s = -2+iγ` and `s = 3+iγ`.

The logarithmic derivative of the product is the sum of the logarithmic derivatives of the local
factors `1-c p^{-s}`; each of those has norm `‖c‖ p^{-σ} log p / ‖1-c p^{-s}‖`, and at `σ = -2`
(resp. `σ = 3`) the reverse triangle inequality gives `‖1 - c p^{-s}‖ ≥ p² - 1 ≥ 3` (resp.
`≥ 1 - p^{-3} ≥ 7/8`), so that each term is at most `(4/3) log p`.  Summing over the (at most two
per prime) factors of `S` and using that `∏_{p ∈ S} p ∣ 4d` gives
`(8/3)·∑_{p ∈ S} log p ≤ (8/3)·log(4d) ≤ 3·log(4d)`. -/

/-- A single local Euler factor `1 - c p^{-s}` of the correction product `corrFac`. -/
def locFac (c : ℂ) (p : ℕ) (s : ℂ) : ℂ := 1 - c * (p : ℂ) ^ (-s)

/-- `corrFac` is the product of the local factors `1 - cᵢ(p) p^{-s}`. -/
lemma corrFac_eq_prod_locFac (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) :
    corrFac c₁ c₂ S = fun x : ℂ => ∏ p ∈ S, (locFac (c₁ p) p x * locFac (c₂ p) p x) := by
  funext x
  simp only [corrFac, locFac]

/-- The logarithmic derivative of the correction product is the sum of the logarithmic derivatives
of the local factors. -/
lemma logDeriv_corrFac_split {c₁ c₂ : ℕ → ℂ} {S : Finset ℕ} {s : ℂ}
    (hpp : ∀ p ∈ S, p ≠ 0)
    (hfac : ∀ p ∈ S, locFac (c₁ p) p s ≠ 0 ∧ locFac (c₂ p) p s ≠ 0) :
    logDeriv (corrFac c₁ c₂ S) s
      = ∑ p ∈ S, (logDeriv (locFac (c₁ p) p) s + logDeriv (locFac (c₂ p) p) s) := by
  rw [corrFac_eq_prod_locFac]
  rw [Submission.Port.logDeriv_prod_fun]
  · exact Finset.sum_congr rfl fun p hp =>
      Submission.Port.logDeriv_mul_fun s (hfac p hp).1 (hfac p hp).2
        (differentiableAt_locFac (c₁ p) (hpp p hp) s)
        (differentiableAt_locFac (c₂ p) (hpp p hp) s)
  · exact fun p hp => mul_ne_zero (hfac p hp).1 (hfac p hp).2
  · exact fun p hp =>
      (differentiableAt_locFac (c₁ p) (hpp p hp) s).mul
        (differentiableAt_locFac (c₂ p) (hpp p hp) s)

/-- A local factor `1 - c p^{-s}` does not vanish as soon as `‖c p^{-s}‖ ≠ 1`. -/
lemma locFac_ne_zero_of_norm_ne_one {c : ℂ} {p : ℕ} {s : ℂ}
    (h : ‖c * (p : ℂ) ^ (-s)‖ ≠ 1) : locFac c p s ≠ 0 := by
  intro h0
  have h1 : c * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
  exact h (by rw [h1, norm_one])

/-- **The logarithmic derivative of the correction product is `O(log 4d)`.**  For every `d ≥ 1`,
every finite set `S` of primes dividing `4d` and every choice of coefficients `c₁, c₂` of modulus
`1` (or `0`) on `S`, the real part of `logDeriv (corrFac c₁ c₂ S)` is bounded by `3 log(4d)` in
absolute value on the two vertical lines `re s = -2` and `re s = 3`. -/
lemma corrFacLogDerivReBound (d : ℕ) (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) (hd : 1 ≤ d)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0)) :
    (∀ γ : ℝ,
      |(logDeriv (corrFac c₁ c₂ S) ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re|
        ≤ 3 * Real.log (4 * (d : ℝ)))
    ∧ (∀ γ : ℝ,
      |(logDeriv (corrFac c₁ c₂ S) ((3 : ℂ) + (γ : ℂ) * Complex.I)).re|
        ≤ 3 * Real.log (4 * (d : ℝ))) := by
  have hlog4d : 0 ≤ Real.log (4 * (d : ℝ)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hsum : ∑ p ∈ S, Real.log p ≤ Real.log (4 * (d : ℝ)) :=
    sum_log_primes_le d S hd fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
  have key : ∀ s : ℂ,
      (∀ p ∈ S, (‖c₁ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 ∨ 4 ≤ ‖c₁ p * (p : ℂ) ^ (-s)‖) ∧
                (‖c₂ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 ∨ 4 ≤ ‖c₂ p * (p : ℂ) ^ (-s)‖)) →
      |(logDeriv (corrFac c₁ c₂ S) s).re| ≤ 3 * Real.log (4 * (d : ℝ)) := by
    intro s hrho
    have hpp : ∀ p ∈ S, p ≠ 0 := fun p hp => (Nat.Prime.pos (hS p hp).1).ne'
    have hne1 : ∀ p ∈ S, ‖c₁ p * (p : ℂ) ^ (-s)‖ ≠ 1 := fun p hp =>
      (hrho p hp).1.elim (fun h => ne_of_lt (by linarith)) (fun h => ne_of_gt (by linarith))
    have hne2 : ∀ p ∈ S, ‖c₂ p * (p : ℂ) ^ (-s)‖ ≠ 1 := fun p hp =>
      (hrho p hp).2.elim (fun h => ne_of_lt (by linarith)) (fun h => ne_of_gt (by linarith))
    have hfac : ∀ p ∈ S, locFac (c₁ p) p s ≠ 0 ∧ locFac (c₂ p) p s ≠ 0 := fun p hp =>
      ⟨locFac_ne_zero_of_norm_ne_one (hne1 p hp), locFac_ne_zero_of_norm_ne_one (hne2 p hp)⟩
    have hbd : ∀ p ∈ S, ‖logDeriv (locFac (c₁ p) p) s‖ ≤ (4 / 3) * Real.log p ∧
        ‖logDeriv (locFac (c₂ p) p) s‖ ≤ (4 / 3) * Real.log p := fun p hp =>
      ⟨by
        show ‖logDeriv (fun u : ℂ => 1 - c₁ p * (p : ℂ) ^ (-u)) s‖ ≤ (4 / 3) * Real.log p
        exact norm_logDeriv_one_sub_mul_cpow_le (c := c₁ p) (hS p hp).1.two_le (hrho p hp).1,
       by
        show ‖logDeriv (fun u : ℂ => 1 - c₂ p * (p : ℂ) ^ (-u)) s‖ ≤ (4 / 3) * Real.log p
        exact norm_logDeriv_one_sub_mul_cpow_le (c := c₂ p) (hS p hp).1.two_le (hrho p hp).2⟩
    have hsplit := logDeriv_corrFac_split hpp hfac
    have hnorm : ‖logDeriv (corrFac c₁ c₂ S) s‖
        ≤ ∑ p ∈ S, ((4 / 3) * Real.log p + (4 / 3) * Real.log p) := by
      rw [hsplit]
      exact le_trans (norm_sum_le _ _)
        (Finset.sum_le_sum fun p hp =>
          le_trans (norm_add_le _ _) (add_le_add (hbd p hp).1 (hbd p hp).2))
    have hsumeq : ∑ p ∈ S, ((4 / 3) * Real.log p + (4 / 3) * Real.log p)
        = (8 / 3) * ∑ p ∈ S, Real.log p := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    calc |(logDeriv (corrFac c₁ c₂ S) s).re| ≤ ‖logDeriv (corrFac c₁ c₂ S) s‖ :=
          Complex.abs_re_le_norm _
      _ ≤ (8 / 3) * ∑ p ∈ S, Real.log p := by rw [← hsumeq]; exact hnorm
      _ ≤ (8 / 3) * Real.log (4 * (d : ℝ)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ 3 * Real.log (4 * (d : ℝ)) := by linarith [hlog4d]
  constructor
  · intro γ
    set s : ℂ := (-2 : ℂ) + (γ : ℂ) * Complex.I with hs
    have hsre : s.re = -2 := by simp [hs]
    refine key s fun p hp => ?_
    exact ⟨(cpow_norm_eval_points (c := c₁ p) (hS p hp).1.two_le (hS p hp).2.2.1).1 s hsre,
           (cpow_norm_eval_points (c := c₂ p) (hS p hp).1.two_le (hS p hp).2.2.2).1 s hsre⟩
  · intro γ
    set s : ℂ := (3 : ℂ) + (γ : ℂ) * Complex.I with hs
    have hsre : s.re = 3 := by simp [hs]
    refine key s fun p hp => ?_
    exact ⟨Or.inl ((cpow_norm_eval_points (c := c₁ p) (hS p hp).1.two_le (hS p hp).2.2.1).2 s hsre),
           Or.inl ((cpow_norm_eval_points (c := c₂ p) (hS p hp).1.two_le (hS p hp).2.2.2).2 s hsre)⟩

/-- **The assembly**: from the functional-equation package for the completion (with the finite
Euler-factor correction) and the bound at `re s = 3`, the lower bound at `re s = -2` follows. -/
lemma baseLowerNegTwo_of_FEdata (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hadm : IsCompleted d chi m Lam)
    (h3 : ∃ C3 : ℝ, 0 < C3 ∧ ∀ γ : ℝ,
      (deriv Lam ((3 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((3 : ℂ) + (γ : ℂ) * Complex.I)).re
        ≤ C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
    (X : ℝ) (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) (Phi : ℂ → ℂ) (W : ℂ)
    (hX1 : 1 ≤ X) (hX4 : X ≤ 4 * (d : ℝ))
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧
      (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0))
    (hW : W ≠ 0) (hPhian : AnalyticOn ℂ Phi Set.univ)
    (hFE : ∀ s : ℂ, Phi s = W * star (Phi (star (1 - s))))
    (hPagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Phi s = ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s * (corrFac c₁ c₂ S s)⁻¹)
    (hB1 : ∀ γ : ℝ, |(logDeriv (corrFac c₁ c₂ S) ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re|
      ≤ 3 * Real.log (4 * (d : ℝ)))
    (hB2 : ∀ γ : ℝ, |(logDeriv (corrFac c₁ c₂ S) ((3 : ℂ) + (γ : ℂ) * Complex.I)).re|
      ≤ 3 * Real.log (4 * (d : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ,
      -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
        ≤ (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
            / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  obtain ⟨C3, hC3, h3b⟩ := h3
  set A : ℝ := 4 * (d : ℝ) / X with hA
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
  have hApos : (0 : ℝ) < A := by rw [hA]; positivity
  have hAne : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hApos)
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ hXpos]; linarith
  have hAle : A ≤ 4 * (d : ℝ) := by
    rw [hA, div_le_iff₀ hXpos]; nlinarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hlogAle : Real.log A ≤ Real.log (4 * (d : ℝ)) := Real.log_le_log hApos hAle
  -- differentiability bookkeeping
  have hSpos : ∀ p ∈ S, p ≠ 0 := fun p hp => (hS p hp).1.pos.ne'
  have hdiffc : ∀ u : ℂ, DifferentiableAt ℂ (corrFac c₁ c₂ S) u :=
    fun u => differentiableAt_corrFac c₁ c₂ S hSpos u
  have hdiffA : ∀ u : ℂ, DifferentiableAt ℂ (fun z : ℂ => (A : ℂ) ^ z) u := fun u =>
    (hasStrictDerivAt_const_cpow (Or.inl hAne)).hasDerivAt.differentiableAt
  have hdiffE : ∀ u : ℂ,
      DifferentiableAt ℂ (fun z : ℂ => (A : ℂ) ^ z * corrFac c₁ c₂ S z) u :=
    fun u => (hdiffA u).mul (hdiffc u)
  have hPdiffat : ∀ u : ℂ, DifferentiableAt ℂ Phi u :=
    fun u => (hPhian.analyticAt (Filter.univ_mem)).differentiableAt
  have hPdiff : Differentiable ℂ Phi := differentiableOn_univ.mp hPhian.differentiableOn
  -- the global identity
  have hLam_fun : Lam = fun s : ℂ => ((A : ℂ) ^ s * corrFac c₁ c₂ S s) * Phi s := by
    refine eq_of_agrees_right_local (T := 1 + |(m : ℝ)| / 2) ?_ hAn ?_
    · refine ((DifferentiableOn.analyticOn ?_ isOpen_univ).mul hPhian)
      intro s _
      exact ((hdiffA s).mul (hdiffc s)).differentiableWithinAt
    · intro s hs
      have hs1 : (1 : ℝ) < s.re := by
        have hm0 : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
        linarith
      have hcs : corrFac c₁ c₂ S s ≠ 0 :=
        corrFac_ne_zero_of_one_lt_re (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩) hs1
      rw [hagr s hs, hPagr s hs, heckeArch_eq]
      have hsplit : ((A : ℂ) ^ s) * (((X / Real.pi : ℝ) : ℂ) ^ s)
          = ((4 * (d : ℝ) / Real.pi : ℝ) : ℂ) ^ s := by
        rw [← Complex.mul_cpow_ofReal_nonneg (le_of_lt hApos)
          (by positivity : (0:ℝ) ≤ X / Real.pi) s, ← Complex.ofReal_mul]
        congr 1
        rw [hA]
        field_simp
      rw [show ((A : ℂ) ^ s * corrFac c₁ c₂ S s) *
            (((X / Real.pi : ℝ) : ℂ) ^ s * Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
              Work.FIArea5.S16Hecke.heckeLSeries chi m s * (corrFac c₁ c₂ S s)⁻¹)
          = (((A : ℂ) ^ s) * (((X / Real.pi : ℝ) : ℂ) ^ s)) *
              (Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
                Work.FIArea5.S16Hecke.heckeLSeries chi m s) *
              (corrFac c₁ c₂ S s * (corrFac c₁ c₂ S s)⁻¹) from by ring]
      rw [mul_inv_cancel₀ hcs, mul_one, hsplit]
      rw [show (4 * (d : ℂ) / (Real.pi : ℂ)) = ((4 * (d : ℝ) / Real.pi : ℝ) : ℂ) by
        push_cast; ring]
      ring
  -- the log-derivative splitting
  have hLam_pt : ∀ s : ℂ, Lam s = ((A : ℂ) ^ s * corrFac c₁ c₂ S s) * Phi s :=
    fun s => congrFun hLam_fun s
  have hsplit (u : ℂ) (hLu : Lam u ≠ 0) (hPu : Phi u ≠ 0) :
      deriv Lam u / Lam u
        = Complex.log (A : ℂ) + deriv (corrFac c₁ c₂ S) u / corrFac c₁ c₂ S u
          + deriv Phi u / Phi u := by
    have hAu : (A : ℂ) ^ u ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]; exact Or.inl hAne
    have hcu : corrFac c₁ c₂ S u ≠ 0 := fun h0 => hLu (by simp [hLam_pt u, h0])
    have hder : deriv Lam u
        = (((A : ℂ) ^ u * Complex.log (A : ℂ)) * corrFac c₁ c₂ S u
            + (A : ℂ) ^ u * deriv (corrFac c₁ c₂ S) u) * Phi u
          + ((A : ℂ) ^ u * corrFac c₁ c₂ S u) * deriv Phi u := by
      have h : HasDerivAt (fun z : ℂ => ((A : ℂ) ^ z * corrFac c₁ c₂ S z) * Phi z)
          ((((A : ℂ) ^ u * Complex.log (A : ℂ)) * corrFac c₁ c₂ S u
              + (A : ℂ) ^ u * deriv (corrFac c₁ c₂ S) u) * Phi u
            + ((A : ℂ) ^ u * corrFac c₁ c₂ S u) * deriv Phi u) u :=
        ((((hasStrictDerivAt_const_cpow (Or.inl hAne)).hasDerivAt).mul
          ((hdiffc u).hasDerivAt)).mul ((hPdiffat u).hasDerivAt))
      rw [show deriv Lam u = deriv (fun z : ℂ => ((A : ℂ) ^ z * corrFac c₁ c₂ S z) * Phi z) u from by
        rw [hLam_fun]]
      exact h.deriv
    rw [hder, hLam_pt u]
    field_simp
    try ring
  refine ⟨C3 + 6, by linarith, fun γ => ?_⟩
  set z : ℂ := (3 : ℂ) + (γ : ℂ) * Complex.I with hz
  set w : ℂ := (-2 : ℂ) + (γ : ℂ) * Complex.I with hw
  have hwz : star (1 - w) = z := by
    rw [hw, hz]
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  have hzre : z.re = 3 := by simp [hz]
  have hwre : w.re = -2 := by simp [hw]
  have hcz : corrFac c₁ c₂ S z ≠ 0 :=
    corrFac_ne_zero_of_one_lt_re (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩)
      (by rw [hzre]; norm_num)
  have hcw : corrFac c₁ c₂ S w ≠ 0 :=
    corrFac_ne_zero_of_re_le_neg_one (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩)
      (by rw [hwre]; norm_num)
  have hlogpos : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    refine Real.log_nonneg ?_
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
    nlinarith
  have hlogge : Real.log (4 * (d : ℝ)) ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    refine Real.log_le_log (by positivity) ?_
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
    nlinarith
  by_cases hz0 : Lam z = 0
  · have hPz : Phi z = 0 := by
      have h := hLam_pt z
      rw [hz0] at h
      have h2 : (A : ℂ) ^ z * corrFac c₁ c₂ S z * Phi z = 0 := h.symm
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (mul_ne_zero (by rw [Complex.cpow_ne_zero_iff]; exact Or.inl hAne) hcz)
      · exact h3
    have hPw : Phi w = 0 := by
      have h := hFE w
      rw [hwz, hPz, star_zero, mul_zero] at h
      exact h
    have hLw : Lam w = 0 := by
      rw [hLam_pt w, hPw, mul_zero]
    rw [hLw, div_zero]
    simp only [Complex.zero_re]
    have := mul_nonneg (by linarith : (0:ℝ) ≤ C3 + 6) hlogpos
    linarith
  · by_cases hw0 : Lam w = 0
    · rw [hw0, div_zero]
      simp only [Complex.zero_re]
      have := mul_nonneg (by linarith : (0:ℝ) ≤ C3 + 6) hlogpos
      linarith
    · have hPz : Phi z ≠ 0 := by
        intro h0
        exact hz0 (by rw [hLam_pt z, h0, mul_zero])
      have hPw : Phi w ≠ 0 := by
        intro h0
        exact hw0 (by rw [hLam_pt w, h0, mul_zero])
      have hsplitW := hsplit w hw0 hPw
      have hsplitZ := hsplit z hz0 hPz
      have hlogP : deriv Phi w / Phi w = -star (deriv Phi z / Phi z) := by
        have h := Work.FIArea5.S16Hecke.logDeriv_FE hW hFE hPdiff hPw
          (by rw [hwz]; exact hPz)
        rw [hwz] at h
        exact h
      have hbw := hB1 γ
      have hbz := hB2 γ
      rw [logDeriv_apply] at hbw hbz
      have hlogAre : (Complex.log (A : ℂ)).re = Real.log A := by
        rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
      have h1 := congrArg Complex.re hsplitW
      have h2 := congrArg Complex.re hsplitZ
      have h3 : (deriv Phi w / Phi w).re = -(deriv Phi z / Phi z).re := by
        rw [hlogP, Complex.neg_re]
        congr 1
      have h1' : (deriv Lam w / Lam w).re
          = (Complex.log (A : ℂ)).re + (deriv (corrFac c₁ c₂ S) w / corrFac c₁ c₂ S w).re
            + (deriv Phi w / Phi w).re := by
        simpa only [Complex.add_re] using h1
      have h2' : (deriv Lam z / Lam z).re
          = (Complex.log (A : ℂ)).re + (deriv (corrFac c₁ c₂ S) z / corrFac c₁ c₂ S z).re
            + (deriv Phi z / Phi z).re := by
        simpa only [Complex.add_re] using h2
      have hbw := hB1 γ
      have hbz := hB2 γ
      rw [logDeriv_apply] at hbw hbz
      have hbwl : -(3 * Real.log (4 * (d : ℝ)))
          ≤ (deriv (corrFac c₁ c₂ S) w / corrFac c₁ c₂ S w).re := neg_le_of_abs_le hbw
      have hbwu : (deriv (corrFac c₁ c₂ S) w / corrFac c₁ c₂ S w).re
          ≤ 3 * Real.log (4 * (d : ℝ)) := le_of_abs_le hbw
      have hbzl : -(3 * Real.log (4 * (d : ℝ)))
          ≤ (deriv (corrFac c₁ c₂ S) z / corrFac c₁ c₂ S z).re := neg_le_of_abs_le hbz
      have hbzu : (deriv (corrFac c₁ c₂ S) z / corrFac c₁ c₂ S z).re
          ≤ 3 * Real.log (4 * (d : ℝ)) := le_of_abs_le hbz
      have h3' := h3b γ
      have hlogAre : (Complex.log (A : ℂ)).re = Real.log A := by
        rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
      have hbound : -(6 * Real.log (4 * (d : ℝ))
            + C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam w / Lam w).re := by
        linarith [h1', h2', h3, hbwl, hbwu, hbzl, hbzu, h3', hlogA0, hlogAle, hlogAre]
      have hfinal2 : 6 * Real.log (4 * (d : ℝ))
            + C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))
          ≤ (C3 + 6) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
        nlinarith [hlogge, hlogpos]
      linarith [hbound, hfinal2]

/-- **The assembly through the *twisted* functional equation.**  Given the completion `G` of
`Λ(s,ψ)` with Hecke's functional equation in the conductor-normalised form
`G s = W·B^{s-1/2}·conj(G(conj(1-s)))` — the shape produced by the *uncorrected* twisted
form, which is **false** for odd Hecke conductor (see
`_scratch_bLN/NOTES_bLN_session4.md`); this lemma is kept only as a generic analytic helper and is
**not** used by the target `baseLowerNegTwo` below,
the reflection `G'/G(-2+iγ) = log B - conj(G'/G(3+iγ))` (with `log B ≥ 0`) reduces the bound at `-2`
to the bound at `3`. -/
lemma baseLowerNegTwo_of_twist (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hadm : IsCompleted d chi m Lam)
    (h3 : ∃ C3 : ℝ, 0 < C3 ∧ ∀ γ : ℝ,
      (deriv Lam ((3 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((3 : ℂ) + (γ : ℂ) * Complex.I)).re
        ≤ C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
    (G : ℂ → ℂ) (hGan : AnalyticOn ℂ G Set.univ)
    (hGagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      G s = Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    (W : ℂ) (B : ℝ) (hBpos : 0 < B) (hB1 : 1 ≤ B)
    (hGFE : ∀ s : ℂ, G s = W * ((B : ℂ) ^ (s - 1 / 2)) * star (G (star (1 - s))))
    (hreflect : ∀ s : ℂ, G s ≠ 0 → G (star (1 - s)) ≠ 0 →
      deriv G s / G s
        = Complex.log (B : ℂ) - star (deriv G (star (1 - s)) / G (star (1 - s)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ,
      -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
        ≤ (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
            / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨C3, hC3, h3b⟩ := h3
  have hLG : Lam = G :=
    eq_of_agrees_right_local (T := 1 + |(m : ℝ)| / 2) hGan hAn
      (fun s hs => by rw [hagr s hs, hGagr s hs])
  rw [hLG] at h3b ⊢
  refine ⟨C3 + 2, by linarith, fun γ => ?_⟩
  set z : ℂ := (3 : ℂ) + (γ : ℂ) * Complex.I with hz
  set w : ℂ := (-2 : ℂ) + (γ : ℂ) * Complex.I with hw
  have hwz : star (1 - w) = z := by
    rw [hw, hz]
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  have hlogpos : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    refine Real.log_nonneg ?_
    have hd0 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
    nlinarith [hd0, hm0, hg0]
  have hC32 : (0 : ℝ) ≤ C3 + 2 := by linarith
  have hgoal0 : -((C3 + 2) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hC32 hlogpos)
  by_cases hz0 : G z = 0
  · have hw0 : G w = 0 := by
      rw [hGFE w, hwz, hz0, star_zero, mul_zero]
    rw [hw0, div_zero, Complex.zero_re]
    exact hgoal0
  · by_cases hw0 : G w = 0
    · rw [hw0, div_zero, Complex.zero_re]
      exact hgoal0
    · have href := hreflect w hw0 (by rw [hwz]; exact hz0)
      have hre := congrArg Complex.re href
      rw [hwz] at hre
      simp only [Complex.sub_re] at hre
      have hstar : (star (deriv G z / G z)).re = (deriv G z / G z).re := by
        rw [Complex.star_def, Complex.conj_re]
      rw [hstar] at hre
      have hlogB : 0 ≤ (Complex.log (B : ℂ)).re := by
        rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBpos]
        exact Real.log_nonneg hB1
      have h3' := h3b γ
      have hb : -C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) ≤ -(deriv G z / G z).re := by
        linarith [h3']
      have h1 : -C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) ≤ (deriv G w / G w).re := by
        linarith [hre, hlogB, hb]
      have h2 : -((C3 + 2) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ -C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
        nlinarith [hlogpos]
      linarith [h1, h2]


end
end Work.FIArea6Hecke.R
