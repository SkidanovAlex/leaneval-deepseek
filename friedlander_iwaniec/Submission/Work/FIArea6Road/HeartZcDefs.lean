import Mathlib
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea6.S16.HeartIface
import Submission.Work.FIArea6Road.HeartAux
import Submission.Work.FIArea6Road.TsumWindow
import Submission.Work.FIArea6Road.sum_tau_sq_window_le
import Submission.Work.FIArea6Road.ZcontExistsBoundUniform
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FIArea6.TsumMellinRepLocal
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Road.PhifacBoundUniform
import Submission.Work.FIArea6Road.PfacSharpZT

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Submission.Work.FIArea6Road.TsumHeartOfInvBound` — the §16 analytic heart

*FI* §16, the contour-shift bound (16.29)–(16.38) for the Möbius-twisted Hecke sum
`Tsum Pa χ m p = Σ_{(n,Π)=1} λ_m(n)μ(n)γ(n;C)p(n)`, from the Hecke inverse bound (16.23)/(16.24).

The target `Work.FIArea6.S16TsumHeart` is assembled here from three independent pieces, exactly as
in `Submission.Work.FIArea6.S16.HeartIface`:

* the continuation of the Dirichlet series `Zsfun` in the strip, with a constant **uniform** in the
  datum — `heart_ZcHypOfInvBound` below (from `Work.FIArea6Road.ZcontExistsBoundUniform`), in the
  regime where an entire completion of the Hecke `L`-function exists;
* the same conclusion in the one case where the inverse bound is vacuous, namely `ψ_m` trivial on
  the primary units mod `4d` (no entire completion exists, `Work.FIArea6Hecke.R.noCompletionOfPsiTrivial`);
* the contour shift `Work.FIArea6.S16.HeartOfZc`, producing a fresh exponent constant `c` and the
  prefactor `C·C_z`.

This file supplies the first of the three, the elementary side conditions (`heart_threshold`), the
Mellin representation in the shape the shift consumes (`heart_mellin_rep_hyp`), and the assembly.
-/

/-- The contour height `T` of (16.38), `T = 5exp(√log N) + 10`. -/
abbrev heartT (Pa : Work.FITop.Params) : ℝ := Work.FIArea6Hecke.heightT Pa

/-- The right-hand vertical line `σ = 1 + 1/log N` of the Mellin identity (16.29). -/
abbrev heartSigma (Pa : Work.FITop.Params) : ℝ := 1 + 1 / Real.log Pa.N

/-- The shift `δ` of (16.37), `δ = min{c_h/(2d^ε(log T + 1)), 1/log Pz}`. -/
abbrev heartDelta (Pa : Work.FITop.Params) (d : ℕ) (ε c_h : ℝ) : ℝ :=
  Work.FIArea6Hecke.deltaC Pa d ε c_h

/-- The first exponential slot of (16.38), `E1 = exp(-ηc(4d)^{-ε}√log N)`. -/
abbrev heartE1 (Pa : Work.FITop.Params) (c : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  Real.exp (-(Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)))

/-- The second exponential slot of (16.38), `E2 = exp(-η log N / log Pz)`. -/
abbrev heartE2 (Pa : Work.FITop.Params) : ℝ :=
  Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))

/-- The right-hand side of the target, in the local vocabulary. -/
abbrev heartRHS (Pa : Work.FITop.Params) (C : ℝ) (c : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  C * (heartE1 Pa c d ε + heartE2 Pa) * ((4 * d : ℕ) : ℝ) * Pa.N
    * (Real.log Pa.N) ^ (6 : ℕ)

/-- `Pa.θ ≤ 1`: `θ = (log x)^{-A'}` with `log x > 1` and `A' ≥ 2A + 2^{20} > 0`. -/
lemma heart_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hlog1 : 1 < Real.log (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3
    linarith [Real.log_three_gt_d9]
  have hA'pos : 0 < Pa.A' := by
    have h20 : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by positivity
    linarith [Pa.hA, Pa.hA', h20]
  have hpow : 1 ≤ (Real.log (Pa.x : ℝ)) ^ Pa.A' :=
    Real.one_le_rpow (x := Real.log (Pa.x : ℝ)) (z := Pa.A')
      (le_of_lt hlog1) (le_of_lt hA'pos)
  rw [Pa.hθ, Real.rpow_neg (le_of_lt (by linarith : (0 : ℝ) < Real.log (Pa.x : ℝ)))]
  exact inv_le_one_of_one_le₀ hpow

/-- `1 < N` (from `x^{1/4+η} < N`), hence `0 < log N`. -/
lemma heart_one_lt_N (Pa : Work.FITop.Params) : (1 : ℝ) < Pa.N := by
  have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by
    have : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hexp : (1 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.one_lt_rpow hx1 (by linarith [Pa.hη])
  linarith [Pa.hNlo]

/-- `0 < log N`. -/
lemma heart_logN_pos (Pa : Work.FITop.Params) : 0 < Real.log Pa.N :=
  Real.log_pos (heart_one_lt_N Pa)

/-- `1 ≤ log N` when `log x ≥ 4` (which holds once `x ≥ 55`): from
`x^{1/4+η} < N` and `η > 0`. -/
lemma heart_logN_ge_one (Pa : Work.FITop.Params) (hx : 4 ≤ Real.log (Pa.x : ℝ)) :
    1 ≤ Real.log Pa.N := by
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlt : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) < Real.log Pa.N :=
    Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) Pa.hNlo
  rw [Real.log_rpow hxpos] at hlt
  nlinarith [hlt, hx, Pa.hη]

/-- The frequency bound `|m| ≤ 4exp(√log N)` puts `m` below the contour height of (16.38). -/
lemma heart_abs_m_le_T (Pa : Work.FITop.Params) (m : ℤ)
    (hm : |(m : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log Pa.N))) :
    |(m : ℝ)| + 3 ≤ heartT Pa := by
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.sqrt (Real.log Pa.N)) :=
    Real.one_le_exp (Real.sqrt_nonneg _)
  rw [heartT, Work.FIArea6Hecke.heightT]
  nlinarith [abs_nonneg (m : ℝ), hexp1, hm]

/-- `log T + 1 ≥ √log N`: the lower bound on the contour height, which turns (16.37) into the first
slot of (16.38) (this is the step that replaces the paper's implicit `θ^{-1} ≤ e^{√log N}`). -/
lemma heart_logT_ge (Pa : Work.FITop.Params) :
    Real.sqrt (Real.log Pa.N) ≤ Real.log (heartT Pa) + 1 := by
  have hle : 5 * Real.exp (Real.sqrt (Real.log Pa.N)) ≤ heartT Pa := by
    rw [heartT, Work.FIArea6Hecke.heightT]; linarith
  have hlog : Real.log (5 * Real.exp (Real.sqrt (Real.log Pa.N)))
      ≤ Real.log (heartT Pa) := Real.log_le_log (by positivity) hle
  have hsplit : Real.log (5 * Real.exp (Real.sqrt (Real.log Pa.N)))
      = Real.log 5 + Real.sqrt (Real.log Pa.N) := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hsqrt_le : Real.sqrt (Real.log Pa.N) ≤ Real.log Pa.N + 1 := by
    have h1 : Real.sqrt (Real.log Pa.N) ^ 2 = Real.log Pa.N :=
      Real.sq_sqrt (le_of_lt (heart_logN_pos Pa))
    have h0 : 0 ≤ Real.sqrt (Real.log Pa.N) := Real.sqrt_nonneg _
    nlinarith [h1, h0]
  linarith [hlog, hsplit, h5, hsqrt_le]

/-- `log T + 1 ≤ 2√log N` for `log N ≥ 256`: the upper bound on the contour height. -/
lemma heart_logT_le (Pa : Work.FITop.Params) (hlogN : 256 ≤ Real.log Pa.N) :
    Real.log (heartT Pa) + 1 ≤ 2 * Real.sqrt (Real.log Pa.N) := by
  have hlogNpos : 0 < Real.log Pa.N := by linarith
  have hs : 0 < Real.sqrt (Real.log Pa.N) := Real.sqrt_pos.mpr hlogNpos
  have hone : (1 : ℝ) ≤ Real.exp (Real.sqrt (Real.log Pa.N)) :=
    Real.one_le_exp (Real.sqrt_nonneg _)
  have hT15 : heartT Pa ≤ 15 * Real.exp (Real.sqrt (Real.log Pa.N)) := by
    rw [heartT, Work.FIArea6Hecke.heightT]
    nlinarith [hone]
  have hT1 : (1 : ℝ) < heartT Pa := by
    rw [heartT, Work.FIArea6Hecke.heightT]
    nlinarith [Real.exp_pos (Real.sqrt (Real.log Pa.N)),
      Real.one_le_exp (Real.sqrt_nonneg (Real.log Pa.N))]
  have hlog : Real.log (heartT Pa) ≤ Real.log (15 * Real.exp (Real.sqrt (Real.log Pa.N))) :=
    Real.log_le_log (by linarith) hT15
  have hsplit : Real.log (15 * Real.exp (Real.sqrt (Real.log Pa.N)))
      = Real.log 15 + Real.sqrt (Real.log Pa.N) := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have h15 : Real.log 15 + 1 ≤ Real.sqrt (Real.log Pa.N) := by
    have hlog15 : Real.log 15 ≤ 14 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 15)
      linarith
    have h256 : (256 : ℝ) ≤ Real.log Pa.N := hlogN
    have h4 : (16 : ℝ) ≤ Real.sqrt (Real.log Pa.N) := by
      have h := Real.sqrt_le_sqrt h256
      have h16 : Real.sqrt (256 : ℝ) = 16 := by
        rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h16] at h
    linarith
  linarith [hlog, hsplit, h15]

/-- On the rectangle, `log(|m| + |t| + 3) ≤ log T + 1` when `|t| ≤ T` and `|m| + 3 ≤ T`. -/
lemma heart_log_arg_le (Pa : Work.FITop.Params) (m : ℤ) (t : ℝ)
    (hm : |(m : ℝ)| + 3 ≤ heartT Pa) (ht : |t| ≤ heartT Pa)
    (hT1 : (1 : ℝ) ≤ heartT Pa) :
    Real.log (|(m : ℝ)| + |t| + 3) ≤ Real.log (heartT Pa) + 1 := by
  have hle : |(m : ℝ)| + |t| + 3 ≤ 2 * heartT Pa := by linarith [abs_nonneg (m : ℝ), ht, hm]
  have hpos : (0 : ℝ) < |(m : ℝ)| + |t| + 3 := by positivity
  have hlog : Real.log (|(m : ℝ)| + |t| + 3) ≤ Real.log (2 * heartT Pa) :=
    Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) (by linarith)] at hlog
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  linarith

/-- `T' = 2T + 3` dominates `|m| + |t| + 3` on the rectangle: the form in which the `log^6` of the
continuation bound is evaluated at the contour height. -/
lemma heart_arg_le_twoT (Pa : Work.FITop.Params) (m : ℤ) (t : ℝ)
    (hm : |(m : ℝ)| + 3 ≤ heartT Pa) (ht : |t| ≤ heartT Pa) :
    |(m : ℝ)| + |t| + 3 ≤ 2 * heartT Pa + 3 := by
  linarith [abs_nonneg (m : ℝ), ht, hm]

/-- **The trivial bound of `Tsum` on its support window** (16.30): `‖Tsum‖ ≤ 4Σ τ(n)²` over
`N < n ≤ (1+θ)N`, from `‖λ(n)‖ ≤ 4τ(n)`, `|μ| ≤ 1`, `|γ| ≤ τ` and `|p| ≤ 1`. -/
theorem Tsum_trivial_bound (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hp : ∀ u : ℝ, |p u| ≤ 1)
    (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
      ≤ 4 * ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊,
            ((n.divisors.card : ℝ)) ^ 2 :=
  norm_Tsum_le_suppWindow Pa chi m p hchi hp hpsupp

/-- **Case A of the case split.**  If the trivial window bound is already below the target, then
`Tsum` obeys the target: `‖Tsum‖ ≤ heartRHS`. -/
theorem Tsum_le_of_trivial (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (d : ℕ) (c C ε : ℝ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hp : ∀ u : ℝ, |p u| ≤ 1)
    (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hslack : 4 * ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊,
            ((n.divisors.card : ℝ)) ^ 2 ≤ heartRHS Pa C c d ε) :
    ‖Work.FIArea6Hecke.Tsum Pa chi m p‖ ≤ heartRHS Pa C c d ε :=
  (Tsum_trivial_bound Pa chi m p hchi hp hpsupp).trans hslack

/-- **The Mellin identity (16.29) with the target's hypotheses discharged.**  `IsCharMod4dStrict`
supplies `‖χ z‖ ≤ 1`, `Params` supplies `θ ≤ 1`, and the derivative hypothesis at `k = 2` supplies
the `1048576/(θN)²` bound of `S16TsumMellinRep` because `cMoll 2 = 2^{20}`. -/
theorem Tsum_mellin_rep (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (d : ℕ) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hx : 4 ≤ Real.log (Pa.x : ℝ))
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hpd : ∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
      |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ))) :
    Work.FIArea6Hecke.Tsum Pa chi m p
      = (1 / (2 * Real.pi)) * ∫ t : ℝ,
          mellin (fun u : ℝ => (p u : ℂ)) ((heartSigma Pa : ℂ) + (t : ℂ) * Complex.I)
            * Work.FIArea6.TauPieces.Zsfun Pa chi m ((heartSigma Pa : ℂ) + (t : ℂ) * Complex.I) := by
  have hlogN : 0 < Real.log Pa.N := Real.log_pos (heart_one_lt_N Pa)
  have hσ1 : 1 < heartSigma Pa := by
    rw [heartSigma]; linarith [one_div_pos.mpr hlogN]
  have hlogN1 : 1 ≤ Real.log Pa.N := heart_logN_ge_one Pa hx
  have hσ2 : heartSigma Pa ≤ 2 := by
    rw [heartSigma]
    have h : 1 / Real.log Pa.N ≤ 1 := (div_le_one hlogN).mpr hlogN1
    linarith
  have hd2 : ∀ u : ℝ, |iteratedDeriv 2 p u| ≤ 1048576 / (Pa.θ * Pa.N) ^ 2 := by
    intro u
    have hθN : 0 < Pa.θ * Pa.N := mul_pos Pa.hθ0 (by linarith [Pa.hN1])
    have h := hpd 2 (le_refl 2) u
    have hc : Work.FITop4.cMoll 2 = (1048576 : ℝ) := by
      rw [Work.FITop4.cMoll]; norm_num
    rw [hc] at h
    rw [Real.rpow_neg (le_of_lt hθN)] at h
    rw [inv_eq_one_div, Real.rpow_natCast, mul_one_div] at h
    exact h
  exact Work.FIArea6.Trunc.S16TsumMellinRep Pa chi m p hσ1 hσ2 (heart_theta_le_one Pa)
    hchi.1.2.2.1 hpC hp0 hp1 hpsupp hd2

/-! ## 1. The side conditions at the threshold `x0` -/

/-- At `Pa.x ≥ exp (exp 2)` the elementary side conditions used by the assembly hold:
`4 ≤ log Pz`, `θ ≤ 1`, and `1 ≤ log N`, so that `σ = 1 + 1/log N ≤ 2`. -/
lemma heart_threshold :
    ∃ x0 : ℝ, 0 < x0 ∧ ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
      (4 : ℝ) ≤ Real.log (Pa.Pz : ℝ) ∧ Pa.θ ≤ 1 ∧ (1 : ℝ) ≤ Real.log Pa.N ∧
      1 + 1 / Real.log Pa.N ≤ 2 := by
  refine ⟨Real.exp (Real.exp 2), Real.exp_pos _, ?_⟩
  intro Pa hx
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlogx : Real.exp 2 ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 2)) hx
    rwa [Real.log_exp] at h
  have hloglogx : (2 : ℝ) ≤ Real.log (Real.log (Pa.x : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 2) hlogx
    rwa [Real.log_exp] at h
  have hlogPz : (4 : ℝ) ≤ Real.log (Pa.Pz : ℝ) := by
    have h4 : (4 : ℝ) ≤ (Real.log (Real.log (Pa.x : ℝ))) ^ 2 := by nlinarith
    exact le_trans h4 Pa.hPlo
  have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_two
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [h2]
    nlinarith [Real.exp_pos 1]
  have hlogx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  have hθ : Pa.θ ≤ 1 := by
    rw [Pa.hθ]
    refine Real.rpow_le_one_of_one_le_of_nonpos hlogx1 ?_
    have hA0 : (0 : ℝ) ≤ Pa.A' := by
      have h1 := Pa.hA
      have h2 := Pa.hA'
      have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) := by positivity
      linarith
    linarith
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by linarith
  have hη0 : (0 : ℝ) < Pa.η := Pa.hη
  have hq_le : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hxq : Real.exp 1 ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hN : Real.exp 1 < Pa.N := lt_of_le_of_lt (le_trans hxq hq_le) Pa.hNlo
  have hlogN : (1 : ℝ) ≤ Real.log Pa.N := by
    have h := Real.log_le_log (Real.exp_pos 1) hN.le
    rwa [Real.log_exp] at h
  exact ⟨hlogPz, hθ, hlogN, by
    have hpos : (0 : ℝ) < Real.log Pa.N := by linarith
    have : 1 / Real.log Pa.N ≤ 1 := by
      rw [div_le_one hpos]; linarith
    linarith⟩

/-! ## 2. The Mellin representation in the shape the shift consumes -/

open MeasureTheory in
/-- The Mellin representation (16.28) of `Tsum` for an arbitrary `1 < σ ≤ 2`, in the shape consumed
by the contour shift (the `hMellin` hypothesis of `HeartOfZc`). -/
lemma heart_mellin_rep_hyp (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    {ε ν : ℝ} (d : ℕ) (hθ1 : Pa.θ ≤ 1) (hh : Work.FIArea6.S16.HeartHyp Pa ν d m chi p ε) :
    ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      Work.FIArea6Hecke.Tsum Pa chi m p
        = (1 / (2 * Real.pi)) * ∫ t : ℝ, (mellin (fun u : ℝ => (p u : ℂ))
            ((σ : ℂ) + (t : ℂ) * Complex.I)
          * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  intro σ hσ1 hσ2
  obtain ⟨hν0, hν1, hd1, hdN, hm, hchi, hpC, hp0, hp1, hpsupp, hpd⟩ := hh
  have hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := fun z => hchi.1.2.2.1 z
  refine Work.FIArea6.Trunc.S16TsumMellinRep Pa chi m p hσ1 hσ2 hθ1 hchibd hpC hp0 hp1 hpsupp ?_
  intro u
  have h := hpd 2 (by norm_num) u
  have hc : Work.FITop4.cMoll 2 = 1048576 := by unfold Work.FITop4.cMoll; norm_num
  rw [hc] at h
  have hxpos : (0 : ℝ) < Pa.θ * Pa.N := by
    have h1 := Pa.hθ0
    have h2 : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
    positivity
  calc |iteratedDeriv 2 p u| ≤ 1048576 * (Pa.θ * Pa.N) ^ (-(2 : ℝ)) := h
    _ = 1048576 / (Pa.θ * Pa.N) ^ 2 := by
        rw [Real.rpow_neg hxpos.le, Real.rpow_ofNat, div_eq_mul_inv]

/-! ## 3. Two monotonicity lemmas -/

/-- **Region monotonicity of the inverse bound**: a smaller `c_h` gives a smaller region, hence
the same bound. -/
lemma heart_hinv_mono {d : ℕ} {ε : ℝ} (hd : 1 ≤ d) {c_h c_h' : ℝ} (hc : c_h ≤ c_h')
    {C_h : ℝ} {m : ℤ} {Lam : ℂ → ℂ}
    (H : ∀ s : ℂ,
      1 - c_h' / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
      ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
        ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) :
    ∀ s : ℂ,
      1 - c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
      ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
        ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
  intro s hs hs2
  refine H s ?_ hs2
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hde : (0 : ℝ) < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hd0 _
  have hlog : (0 : ℝ) < Real.log (|(m : ℝ)| + |s.im| + 3) := by
    apply Real.log_pos
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hpos : (0 : ℝ) < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := mul_pos hde hlog
  have hdiv : c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ c_h' / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
    div_le_div_of_nonneg_right hc hpos.le
  linarith

/-- The prefactor `S16RH` is monotone in its prefactor constant. -/
lemma heart_S16RH_mono (Pa : Work.FITop.Params) (c : ℝ) (d : ℕ) (ε : ℝ) {C C' : ℝ}
    (h : C ≤ C') :
    Work.FIArea6.S16.S16RH Pa c C d ε ≤ Work.FIArea6.S16.S16RH Pa c C' d ε := by
  unfold Work.FIArea6.S16.S16RH
  have hE : 0 ≤ Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa := by
    have h1 := Real.exp_pos (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
    have h2 := Real.exp_pos (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))
    linarith
  have h4d : (0 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one Pa.hN1
  have hl : (0 : ℝ) ≤ (Real.log Pa.N) ^ (6 : ℕ) :=
    pow_nonneg (Real.log_nonneg Pa.hN1) 6
  have hT : (0 : ℝ) ≤ ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) :=
    mul_nonneg (mul_nonneg h4d hN) hl
  have h1 : C * (Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa)
      ≤ C' * (Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa) :=
    mul_le_mul_of_nonneg_right h hE
  calc C * (Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa) * ((4 * d : ℕ) : ℝ)
        * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
      = (C * (Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa))
          * (((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) := by ring
    _ ≤ (C' * (Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa))
          * (((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) :=
        mul_le_mul_of_nonneg_right h1 hT
    _ = C' * (Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa) * ((4 * d : ℕ) : ℝ)
          * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by ring

/-! ## 4. The corrected continuation interface and its realisation

The interface `Work.FIArea6.S16.ZcHyp` inherited from the shared repository demands the
continuation bound on `1/2 < re s ≤ 2` *with* the factor `C^{1-re s}`.  For `re s > 1` the
continuation agrees with the Dirichlet series `Zsfun`, whose `n = 1` term is `tcoef 1 = 1`; since
`C^{1-re s} → 0` there when `Pa.C` is large, that clause is **false** and no `Pa`-uniform `C_z` can
realise it.  The contour shift only needs the bound up to the right-hand line `re s = 1 + 1/log N`
of (16.36).  The correct interface is therefore

* the bound with the saving factor `C^{1-σ}` on the region `re s ≤ 1` of (16.32), and
* the bound without any `C`-factor on the thin strip `1 < re s ≤ 1 + 1/log N`, where the series is
  absolutely convergent and `Pa.C^{re s - 1} ≤ e`.

Both clauses hold for the candidate continuation `Zcand = Φ·(Λ/arch)^{-1}·P·Q`. -/

/-- **The corrected continuation interface** (compare `Work.FIArea6.S16.ZcHyp`).  `Zc` agrees with
`Zsfun` on `re s > 1`, is analytic on the region (16.24), and satisfies

* `‖Zc s‖ ≤ C_z·d·C^{1-σ}·L(s)^6` for `1/2 < σ ≤ 1` inside the region (16.32) — the bound the
  shifted line consumes, with the saving `C^{1-σ}`;
* `‖Zc s‖ ≤ C_z·d·L(s)^6` for `1 < σ ≤ 1 + 1/log N` — the bound the two horizontal segments
  consume on the part `σ > 1`, where the `C^{1-σ}` saving is unavailable but unnecessary,

with `L(s) = log N + log(|m| + |Im s| + 3) + 2`. -/
def heartZcHyp (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ)
    (ε c_h C_z : ℝ) (Zc : ℂ → ℂ) : Prop :=
  0 < C_z ∧
  (∀ s : ℂ, 1 < s.re → Zc s = Work.FIArea6.TauPieces.Zsfun Pa chi m s) ∧
  AnalyticOn ℂ Zc {s : ℂ | 1 / 2 < s.re ∧
    1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re} ∧
  (∀ s : ℂ, 1 / 2 < s.re →
    1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re →
    1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 1 →
    ‖Zc s‖ ≤ C_z * (d : ℝ) * Pa.C ^ (1 - s.re)
      * (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ)) ∧
  (∀ s : ℂ, 1 < s.re → s.re ≤ 1 + 1 / Real.log Pa.N → s.re ≤ 2 →
    ‖Zc s‖ ≤ C_z * (d : ℝ)
      * (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ))

/-- `log(N + x) ≤ log N + log x + 2` for `x ≥ 1`, `N ≥ 1`. -/
lemma heart_log_add_le {N x : ℝ} (hN : 1 ≤ N) (hx : 1 ≤ x) :
    Real.log (x + N) ≤ Real.log N + Real.log x + 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hle : x + N ≤ 2 * (N * x) := by nlinarith
  have h1 : Real.log (x + N) ≤ Real.log (2 * (N * x)) := Real.log_le_log (by linarith) hle
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_ne_zero (ne_of_gt hNpos) (ne_of_gt hxpos)),
    Real.log_mul (ne_of_gt hNpos) (ne_of_gt hxpos)] at h1
  have h2 : Real.log 2 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  linarith

/-- `L(m,s) := log N + log(|m| + |Im s| + 3) + 2` is nonnegative. -/
lemma heart_L_nonneg (Pa : Work.FITop.Params) (m : ℤ) (s : ℂ) :
    0 ≤ Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 := by
  have h1 : (0 : ℝ) ≤ Real.log (Pa.N) := Real.log_nonneg Pa.hN1
  have h2 : (0 : ℝ) ≤ Real.log (|(m : ℝ)| + |s.im| + 3) :=
    Real.log_nonneg (by
      have ha := abs_nonneg (m : ℝ)
      have hb := abs_nonneg s.im
      linarith)
  linarith

/-- The log-shape conversion `log(|m|+|Im s|+N+3) ≤ L(m,s)`. -/
lemma heart_logN_add_three_le (Pa : Work.FITop.Params) (m : ℤ) (s : ℂ) :
    Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)
      ≤ Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 := by
  have hx1 : (1 : ℝ) ≤ |(m : ℝ)| + |s.im| + 3 := by
    have ha := abs_nonneg (m : ℝ)
    have hb := abs_nonneg s.im
    linarith
  have h := heart_log_add_le Pa.hN1 hx1
  have he : |(m : ℝ)| + |s.im| + 3 + (Pa.N : ℝ)
      = |(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3 := by ring
  rwa [he] at h

end

end Work.FIArea6Road
