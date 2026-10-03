/-
# `Submission.Work.FIArea6Road.HeartZcTrivial`

The corrected continuation interface `heartZcHyp` in the *trivial-`ψ`* regime, i.e. the case where
the Hecke character `ψ_m` is trivial on the primary units modulo `4d`.  There the Hecke eigenvalue
is the principal one (`HeckeLamTrivialPsi`),

  `λ_m(n) = 1_{(n,4d)=1} Σ_{e|n} χ₄(e)`,

so `L(s,ψ) = ζ(s)L(s,χ₄)G_d(s)` with `G_d = axisBadPoly d` the finite bad-prime correction, and the
natural continuation of `Zsfun = M·P·Q` is

  `Zc = Φ · (ζ · L(·,χ₄) · G_d)^{-1} · P · Q`  (with the value at `s = 1` corrected to its limit `0`,
since `ζ` has its pole there).

The two inputs from the analytic theory of `ζ` and `L(·,χ₄)` are the inverse bounds in the
de la Vallée Poussin zero-free region `1 - c/log(|t|+2) ≤ σ ≤ 2`:

* `Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree` — for `ζ` (proved in the workspace);
* `zcT_Chi4Inv` — for `χ₄` (the sharp inverse bound).

Since the depth `c_h/(2d^ε log(|m|+|Im s|+3))` of the analyticity region is *smaller* than
`c/log(|t|+2)` whenever `c_h ≤ 2c`, the region of `heartZcHyp` lies inside both zero-free regions,
which is what makes the trivial regime accessible.

The log-bookkeeping (the `P`-factor's `log³`, the `Q`-factor's `log²` and the inverse bound's
`log²`) is `Work.FIArea6Road.ZcBoundArith_proved`.
-/
import Mathlib
import Submission.Work.FIArea6Road.HeartZcDefs
import Submission.Work.FIArea6Road.HeckeLamTrivialPsi
import Submission.Work.FIArea6Road.QfacBoundRatioGeOne
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.PrimeCounting
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_log_div_le
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_eventually_bounded
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_le_log_log_add
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log
import Submission.Work.FIArea6Road.PhifacIdent
import Submission.Work.FIArea6Road.ZprodRegroup
import Submission.Work.FIArea6Road.ZcontAux
import Submission.Work.FIArea6Road.PhifacBoundUniform
import Submission.Work.FIArea6Road.PfacSharpZT
import Submission.Work.FIArea6Road.ZcontExistsBoundUniform
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_all_t
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_LFunction_chi4_all_t
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_real_zero_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Work.FIArea6Road.Chi4CCommon
import Submission.Work.FIArea6Road.Lchi4InvSharp
import Submission.Work.FIArea6Road.ZcTrivAxisBad

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Road

open Finset Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The two inputs from the analytic theory of `ζ` and `χ₄` -/

/-- **The sharp inverse bound for `L(·,χ₄)`** in the de la Vallée Poussin zero-free region, for all
heights.  Proved in `Submission/Work/FIArea6Road/Lchi4InvSharp.lean`. -/
theorem zcT_Chi4Inv :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ σ t : ℝ,
      1 - c / Real.log (4 * (|t| + 2)) ≤ σ → σ ≤ 2 →
        1 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * Real.log (4 * (|t| + 2)) :=
  Work.FIArea6Road.Lchi4InvSharp

/-- **The `Q`-factor on `1 ≤ σ ≤ 2`**: `‖Q(s)‖ ≤ K(1 + log(C+2)/log Pz)²`.  On `σ ≥ 1` each
summand is dominated by its majorant `∏_{p|c}QfacW Pa p` (`QfacTermNormLe`), and the Euler product
of those majorants is `≪ (1 + log C/log Pz)²` (`QfacSumBound`); since `log C ≤ log(C+2)` the bound
with `log(C+2)` follows. -/
theorem zcT_QfacTwo :
    ∃ K : ℝ, 0 < K ∧ ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ),
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) → 1 ≤ Pa.C → 4 ≤ Real.log (Pa.Pz : ℝ) →
      ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 →
        ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖
          ≤ K * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨K, hKpos, hK⟩ := Work.FIArea6Road.QfacSumBound
  refine ⟨K, hKpos, ?_⟩
  intro Pa chi m hchi1 hchimul hchi hC1 hlogPz s h1 _h2
  have hlogC : Real.log Pa.C ≤ Real.log (Pa.C + 2) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hC1) (by linarith)
  have hlogpos : (0 : ℝ) < Real.log (Pa.Pz : ℝ) := by linarith
  have hbase : (0 : ℝ) ≤ 1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ) := by
    have := div_nonneg (Real.log_nonneg hC1) (le_of_lt hlogpos)
    linarith
  have hstep : 1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)
      ≤ 1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ) := by
    have := div_le_div_of_nonneg_right hlogC (le_of_lt hlogpos)
    linarith
  have hmono := pow_le_pow_left₀ hbase hstep 2
  rw [Work.FIArea6Road.Qfac_eq_sum]
  calc ‖∑ c ∈ Work.FIArea6Road.QfacS Pa, Work.FIArea6Road.QfacTerm chi m s c‖
      ≤ ∑ c ∈ Work.FIArea6Road.QfacS Pa,
          ‖Work.FIArea6Road.QfacTerm chi m s c‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ Work.FIArea6Road.QfacS Pa,
          ∏ p ∈ c.primeFactors, Work.FIArea6Road.QfacW Pa p :=
        Finset.sum_le_sum (fun c hc =>
          Work.FIArea6Road.QfacTermNormLe Pa chi m hchi1 hchimul hchi hlogPz h1 hc)
    _ ≤ K * (1 + Real.log Pa.C / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) := hK Pa hlogPz hC1
    _ ≤ K * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hmono (le_of_lt hKpos)

/-- **The bad-prime correction is bounded below**: `‖G_d(s)⁻¹‖ ≤ K·d` for `Re s ≥ 1/2`.  Proved in
`Submission/Work/FIArea6Road/ZcTrivAxisBad.lean`. -/
theorem zcT_AxisBad :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℕ, 1 ≤ d → ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re →
      ‖(Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖ ≤ K * (d : ℝ) :=
  ZcTrivAxisBad

/-! ## 2. The trivial-regime identities -/

/-- In the trivial-`ψ` regime the Hecke eigenvalue is the principal one. -/
theorem zcT_heckeLam (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → Work.FIArea5.S16Hecke.psi chi m z = 1) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam chi m n
      = Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 n := by
  rw [Work.FIArea6Road.HeckeLamTrivialPsi d hd chi m hchi htriv n]
  exact (Work.FIArea6Road.HeckeLamTrivialPsi d hd (Work.FIArea6Hecke.principalStrict d) 0
    (Work.FIArea6Hecke.isCharMod4dStrict_principalStrict d hd) (by
      intro z _ hu
      rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]
      exact Work.FIArea6Hecke.principalStrict_of_unit hu) n).symm

/-- In the trivial-`ψ` regime the Hecke `L`-series of `χ` is `ζ·L(·,χ₄)·G_d`. -/
theorem zcT_heckeLSeries (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → Work.FIArea5.S16Hecke.psi chi m z = 1)
    {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeLSeries chi m s
      = riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
          * Work.FIArea6Hecke.R.axisBadPoly d s := by
  have h1 : Work.FIArea5.S16Hecke.heckeLSeries chi m s
      = Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s := by
    rw [Work.FIArea5.S16Hecke.heckeLSeries, Work.FIArea5.S16Hecke.heckeLSeries]
    exact LSeries_congr (fun {n} _ => zcT_heckeLam d hd chi m hchi htriv n) s
  rw [h1, Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq d hd hs,
    Work.FIArea6Hecke.R.LSeries_axisChi4_eq_LFunction hs]

/-! ## 3. The candidate continuation -/

/-- The candidate continuation of `Zsfun` in the trivial-`ψ` regime,
`Φ·(ζ·L(·,χ₄)·G_d)^{-1}·P·Q` (the shape of `Zcand`, with the entire completion `Λ` replaced by the
explicit product `ζ·L(·,χ₄)·G_d`). -/
def zcTrivFun (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) : ℂ → ℂ :=
  fun s => Work.FIArea6.TauPieces.Phifac chi m s
    * (riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
        * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹
    * Work.FIArea6.TauPieces.Pfac Pa chi m s * Work.FIArea6.TauPieces.Qfac Pa chi m s

/-- The candidate `Zc` of the trivial-`ψ` regime: `zcTrivFun`, with the value at `s = 1` replaced by
the limit `0` (the simple pole of `ζ` at `1` is a zero of the continuation). -/
def zcTriv (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) : ℂ → ℂ :=
  Function.update (zcTrivFun Pa chi m d) 1 0

lemma zcTriv_apply_of_ne {Pa : Work.FITop.Params} {chi : GaussianInt → ℂ} {m : ℤ} {d : ℕ}
    {s : ℂ} (hs : s ≠ 1) : zcTriv Pa chi m d s = zcTrivFun Pa chi m d s :=
  Function.update_of_ne hs _ _

lemma zcTriv_one (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) :
    zcTriv Pa chi m d 1 = 0 := Function.update_self _ _ _

/-- **Agreement with the Dirichlet series on `Re s > 1`** (*FI* (16.30)–(16.31)). -/
theorem zcT_agree (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ)
    (hd : 1 ≤ d) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → Work.FIArea5.S16Hecke.psi chi m z = 1)
    {s : ℂ} (hs : 1 < s.re) :
    zcTriv Pa chi m d s = Work.FIArea6.TauPieces.Zsfun Pa chi m s := by
  have hchi1 : chi 1 = 1 := hchi.1.1
  have hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hsne : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hL := zcT_heckeLSeries d hd chi m hchi htriv hs
  have hPhi := Work.FIArea6Road.PhifacIdent chi m hchi1 hchimul hchibd hs
  have hLmul := Work.FIArea6Road.zcontLSeries_mul_inv (m := m) hchi1 hchimul hchibd hs
  have hPr := Work.FIArea6Road.ZprodRegroup Pa chi m hchi1 hchimul hchibd hs
  have hstep : (Work.FIArea6.TauPieces.Mfac chi m s
        * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
        * (Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹
      = Work.FIArea6.TauPieces.Mfac chi m s := by
    rw [mul_assoc, hLmul, mul_one]
  rw [zcTriv_apply_of_ne hsne, zcTrivFun, ← hL, hPhi, hstep, hPr]

/-! ## 4. Analyticity of the candidate -/

/-- On the region `Re s > 0` the bad-prime correction does not vanish (its factors `1 - p^{-s}`
and `1 - χ₄(p)p^{-s}` vanish only on the imaginary axis). -/
lemma zcT_axisBadPoly_ne_zero (d : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Work.FIArea6Hecke.R.axisBadPoly d s ≠ 0 := by
  rw [Work.FIArea6Hecke.R.axisBadPoly]
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hpσ : (p : ℝ) ^ (-s.re) < 1 := by
    rw [Real.rpow_neg hp0.le, inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow hp1 (by linarith)
  have hne1 : (p : ℂ) ^ (-s) ≠ 1 := by
    intro h
    have h1 : ‖(p : ℂ) ^ (-s)‖ = 1 := by rw [h]; simp
    rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re] at h1
    linarith
  refine mul_ne_zero (sub_ne_zero.mpr (Ne.symm hne1)) ?_
  intro h
  have h1 : Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s)‖ = 1 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re] at h2
  have h3 : ‖Work.FIArea6Hecke.R.axisChi4 p‖ ≤ 1 := by
    rw [Work.FIArea6Hecke.R.axisChi4_eq_if]
    split_ifs <;> norm_num
  have h4 : (0 : ℝ) < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hp0 _
  have h5 : ‖Work.FIArea6Hecke.R.axisChi4 p‖ * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-s.re) :=
    mul_le_of_le_one_left h4.le h3
  linarith

/-! ## 4. The region comparisons -/

/-- The region of `heartZcHyp` lies in the zero-free region `1 - cζ/log(|t|+2) ≤ σ`. -/
lemma zcT_region_zeta {cζ c₀ : ℝ} (hcζ : 0 < cζ) (hc₀ζ : c₀ ≤ 2 * cζ) {c_h : ℝ}
    (hc_h : 0 < c_h) (hc_h₀ : c_h ≤ c₀) (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (m : ℤ) {s : ℂ}
    (hdeep : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re) :
    1 - cζ / Real.log (|s.im| + 2) ≤ s.re := by
  have hA1 : (1 : ℝ) < |(m : ℝ)| + |s.im| + 3 := by
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hlogA : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) := Real.log_pos hA1
  have hB1 : (1 : ℝ) < |s.im| + 2 := by
    have h2 := abs_nonneg s.im
    linarith
  have hlogB : 0 < Real.log (|s.im| + 2) := Real.log_pos hB1
  have hlogBA : Real.log (|s.im| + 2) ≤ Real.log (|(m : ℝ)| + |s.im| + 3) := by
    refine Real.log_le_log (by linarith) ?_
    have h1 := abs_nonneg (m : ℝ)
    linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdε : (1 : ℝ) ≤ (d : ℝ) ^ ε := Real.one_le_rpow hd1 (le_of_lt hε)
  have hstep1 : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ c_h / (2 * Real.log (|(m : ℝ)| + |s.im| + 3)) := by
    refine div_le_div_of_nonneg_left hc_h.le (by positivity) ?_
    calc (2 : ℝ) * Real.log (|(m : ℝ)| + |s.im| + 3)
        = 2 * 1 * Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
      _ ≤ 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogA.le
          linarith
  have hstep2 : c_h / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3)) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact hc_h₀
  have hstep3 : c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ cζ / Real.log (|(m : ℝ)| + |s.im| + 3) := by
    have h1 : c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
        = (c₀ / 2) / Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
    rw [h1]
    exact div_le_div_of_nonneg_right (by linarith) hlogA.le
  have hstep4 : cζ / Real.log (|(m : ℝ)| + |s.im| + 3)
      ≤ cζ / Real.log (|s.im| + 2) :=
    div_le_div_of_nonneg_left hcζ.le hlogB hlogBA
  linarith [hdeep, hstep1, hstep2, hstep3, hstep4]

/-- The region of `heartZcHyp` lies in the zero-free region `1 - cχ/log(4(|t|+2)) ≤ σ`. -/
lemma zcT_region_chi4 {cχ c₀ : ℝ} (hcχ : 0 < cχ)
    (hc₀χ : c₀ ≤ 2 * cχ * Real.log 2 / (Real.log 4 + Real.log 2)) {c_h : ℝ}
    (hc_h : 0 < c_h) (hc_h₀ : c_h ≤ c₀) (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (m : ℤ) {s : ℂ}
    (hdeep : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re) :
    1 - cχ / Real.log (4 * (|s.im| + 2)) ≤ s.re := by
  have hA1 : (1 : ℝ) < |(m : ℝ)| + |s.im| + 3 := by
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hlogA : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) := Real.log_pos hA1
  have hB1 : (1 : ℝ) < |s.im| + 2 := by
    have h2 := abs_nonneg s.im
    linarith
  have hlogB : 0 < Real.log (|s.im| + 2) := Real.log_pos hB1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogBA : Real.log (|s.im| + 2) ≤ Real.log (|(m : ℝ)| + |s.im| + 3) := by
    refine Real.log_le_log (by linarith) ?_
    have h1 := abs_nonneg (m : ℝ)
    linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdε : (1 : ℝ) ≤ (d : ℝ) ^ ε := Real.one_le_rpow hd1 (le_of_lt hε)
  have hstep1 : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ c_h / (2 * Real.log (|(m : ℝ)| + |s.im| + 3)) := by
    refine div_le_div_of_nonneg_left hc_h.le (by positivity) ?_
    calc (2 : ℝ) * Real.log (|(m : ℝ)| + |s.im| + 3)
        = 2 * 1 * Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
      _ ≤ 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogA.le
          linarith
  have hstep2 : c_h / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3)) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact hc_h₀
  have hstep3 : c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ cχ * Real.log 2 / (Real.log 4 + Real.log 2) / Real.log (|(m : ℝ)| + |s.im| + 3) := by
    have h1 : c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
        = (c₀ / 2) / Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
    rw [h1]
    have hD : Real.log 4 + Real.log 2 ≠ 0 := by linarith
    have h2 : c₀ / 2 ≤ cχ * Real.log 2 / (Real.log 4 + Real.log 2) := by
      have h := div_le_div_of_nonneg_right hc₀χ (by norm_num : (0:ℝ) ≤ 2)
      have he : (2 * cχ * Real.log 2 / (Real.log 4 + Real.log 2)) / 2
          = cχ * Real.log 2 / (Real.log 4 + Real.log 2) := by
        field_simp
      rwa [he] at h
    exact div_le_div_of_nonneg_right h2 hlogA.le
  have hlog2B : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hkey : Real.log 2 * Real.log (4 * (|s.im| + 2))
      ≤ (Real.log 4 + Real.log 2) * Real.log (|(m : ℝ)| + |s.im| + 3) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    nlinarith [hlogB, hlogBA, hlog2, hlog4, hlog2B]
  have hstep4 : cχ * Real.log 2 / (Real.log 4 + Real.log 2)
        / Real.log (|(m : ℝ)| + |s.im| + 3)
      ≤ cχ / Real.log (4 * (|s.im| + 2)) := by
    have hpos4 : 0 < Real.log (4 * (|s.im| + 2)) :=
      Real.log_pos (by linarith [abs_nonneg s.im])
    rw [div_div, div_le_div_iff₀ (by positivity) hpos4]
    nlinarith [mul_le_mul_of_nonneg_left hkey hcχ.le]
  linarith [hdeep, hstep1, hstep2, hstep3, hstep4]


/-- On the analyticity region of `heartZcHyp` the function `ζ` does not vanish. -/
lemma zcT_zeta_ne_zero {c₁ c₂ c₀ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₀₁ : c₀ ≤ 2 * c₁) (hc₀₂ : c₀ ≤ 2 * (Real.log 3) * c₂ / (Real.log 4) ^ 9)
    (hZ1 : ∀ σ t : ℝ, 2 ≤ |t| → 1 - c₁ / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hZ2 : ∀ σ t : ℝ, 1 - c₂ / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    {c_h : ℝ} (hc_h : 0 < c_h) (hc_h₀ : c_h ≤ c₀) (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (m : ℤ) {s : ℂ} (hs1 : (1 / 2 : ℝ) < s.re)
    (hdeep : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re) :
    riemannZeta s ≠ 0 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdε : (1 : ℝ) ≤ (d : ℝ) ^ ε := Real.one_le_rpow hd1 (le_of_lt hε)
  have hlogA1 : (1 : ℝ) < |(m : ℝ)| + |s.im| + 3 := by
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hlogA : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) := Real.log_pos hlogA1
  have hlog3A : Real.log 3 ≤ Real.log (|(m : ℝ)| + |s.im| + 3) := by
    refine Real.log_le_log (by norm_num) ?_
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hdepth : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ c₀ / (2 * Real.log 3) := by
    have h1 : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
        ≤ c_h / (2 * Real.log 3) := by
      have hbc : (2 : ℝ) * Real.log 3 ≤ 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by
        have h2 : (2 : ℝ) * Real.log 3
            ≤ 2 * Real.log (|(m : ℝ)| + |s.im| + 3) := by linarith
        calc (2 : ℝ) * Real.log 3 ≤ 2 * Real.log (|(m : ℝ)| + |s.im| + 3) := h2
          _ = 2 * 1 * Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
          _ ≤ 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) :=
              mul_le_mul_of_nonneg_right (by linarith) hlogA.le
      exact div_le_div_of_nonneg_left hc_h.le (by positivity) hbc
    exact h1.trans (div_le_div_of_nonneg_right hc_h₀ (by positivity))
  rcases le_or_gt 1 s.re with h1 | h1
  · rw [← Complex.re_add_im s]
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using h1)
  · rcases le_or_gt 2 |s.im| with h2 | h2
    · have hregion : 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re :=
        zcT_region_zeta hc₁ hc₀₁ hc_h hc_h₀ d hd ε hε m hdeep
      rw [← Complex.re_add_im s]
      exact hZ1 s.re s.im h2 hregion
    · have hgap : c₀ / (2 * Real.log 3) ≤ c₂ / (Real.log 4) ^ 9 := by
        have hD : 0 < (Real.log 4) ^ 9 := pow_pos hlog4 9
        have h : c₀ ≤ (2 * Real.log 3) * (c₂ / (Real.log 4) ^ 9) := by
          have hh := hc₀₂
          have he : 2 * Real.log 3 * c₂ / (Real.log 4) ^ 9
              = (2 * Real.log 3) * (c₂ / (Real.log 4) ^ 9) := by ring
          rwa [he] at hh
        calc c₀ / (2 * Real.log 3)
            ≤ ((2 * Real.log 3) * (c₂ / (Real.log 4) ^ 9)) / (2 * Real.log 3) :=
              div_le_div_of_nonneg_right h (by positivity)
          _ = c₂ / (Real.log 4) ^ 9 := by field_simp
      have hlogB1 : (1 : ℝ) < |s.im| + 2 := by
        have h2 := abs_nonneg s.im
        linarith
      have hlogB : 0 < Real.log (|s.im| + 2) := Real.log_pos hlogB1
      have hlogle : Real.log (|s.im| + 2) ≤ Real.log 4 :=
        Real.log_le_log (by linarith) (by linarith [abs_nonneg s.im])
      have hpow : (Real.log (|s.im| + 2)) ^ 9 ≤ (Real.log 4) ^ 9 :=
        pow_le_pow_left₀ hlogB.le hlogle 9
      have h1' : c₂ / (Real.log 4) ^ 9 ≤ c₂ / (Real.log (|s.im| + 2)) ^ 9 :=
        div_le_div_of_nonneg_left hc₂.le (pow_pos hlogB 9) hpow
      have hsr : 1 - c₂ / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re := by
        have h2' : (0 : ℝ) < (Real.log 4) ^ 9 := pow_pos hlog4 9
        linarith [hdeep, hdepth, hgap, h1']
      rw [← Complex.re_add_im s]
      exact hZ2 s.re s.im hsr

/-- On the analyticity region of `heartZcHyp` the function `L(·,χ₄)` does not vanish: off the real
axis from the uniform zero-free region of `L(·,χ₄)` (valid for every `t ≠ 0`), and on the real axis
from the (Siegel-type) gap between `1` and the real zeros of `L(·,χ₄)`. -/
lemma zcT_chi4_ne_zero {c₃ c₅ c₀ : ℝ} (hc₃ : 0 < c₃) (hc₅ : 0 < c₅)
    (hc₀₃ : c₀ ≤ 2 * c₃ * Real.log 2 / (Real.log 4 + Real.log 2))
    (hc₀₅ : c₀ ≤ 2 * Real.log 3 * c₅)
    (hC1 : ∀ σ t : ℝ, t ≠ 0 → 1 - c₃ / Real.log (4 * (|t| + 2)) ≤ σ →
      (Work.FIArea6Hecke.R.chi4C).LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hC5 : ∀ β : ℝ, 0 < β → β < 1 →
      (Work.FIArea6Hecke.R.chi4C).LFunction (β : ℂ) = 0 → c₅ ≤ 1 - β)
    {c_h : ℝ} (hc_h : 0 < c_h) (hc_h₀ : c_h ≤ c₀) (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (m : ℤ) {s : ℂ} (hs1 : (1 / 2 : ℝ) < s.re)
    (hdeep : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re) :
    (Work.FIArea6Hecke.R.chi4C).LFunction s ≠ 0 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdε : (1 : ℝ) ≤ (d : ℝ) ^ ε := Real.one_le_rpow hd1 (le_of_lt hε)
  have hlogA1 : (1 : ℝ) < |(m : ℝ)| + |s.im| + 3 := by
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hlogA : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) := Real.log_pos hlogA1
  have hdepth : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ c₀ / (2 * Real.log 3) := by
    have h1 : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
        ≤ c_h / (2 * Real.log 3) := by
      have hbc : (2 : ℝ) * Real.log 3 ≤ 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by
        have hL3 : Real.log 3 ≤ Real.log (|(m : ℝ)| + |s.im| + 3) := by
          refine Real.log_le_log (by norm_num) ?_
          have h1 := abs_nonneg (m : ℝ)
          have h2 := abs_nonneg s.im
          linarith
        calc (2 : ℝ) * Real.log 3 ≤ 2 * Real.log (|(m : ℝ)| + |s.im| + 3) := by linarith
          _ = 2 * 1 * Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
          _ ≤ 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) :=
              mul_le_mul_of_nonneg_right (by linarith) hlogA.le
      exact div_le_div_of_nonneg_left hc_h.le (by positivity) hbc
    exact h1.trans (div_le_div_of_nonneg_right hc_h₀ (by positivity))
  rcases le_or_gt 1 s.re with h1 | h1
  · rw [← Complex.re_add_im s]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re Work.FIArea6Hecke.R.chi4C
      (Or.inl Work.FIArea6Hecke.R.chi4C_ne_one) (by simpa using h1)
  · rcases eq_or_ne s.im 0 with him | him
    · rw [← Complex.re_add_im s, him]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      intro h0
      have hσ0 : 0 < s.re := by linarith
      have h := hC5 s.re hσ0 h1 h0
      have h2 : c₀ / (2 * Real.log 3) ≤ c₅ := by
        have h3 : c₀ ≤ (2 * Real.log 3) * c₅ := by linarith
        calc c₀ / (2 * Real.log 3) ≤ ((2 * Real.log 3) * c₅) / (2 * Real.log 3) :=
              div_le_div_of_nonneg_right h3 (by positivity)
          _ = c₅ := by field_simp
      linarith [hdeep, hdepth, h2, h]
    · rw [← Complex.re_add_im s]
      refine hC1 s.re s.im him ?_
      have hB1 : (1 : ℝ) < |s.im| + 2 := by
        have h := abs_pos.mpr him
        linarith
      have hlogB : 0 < Real.log (|s.im| + 2) := Real.log_pos hB1
      have hlogBA : Real.log (|s.im| + 2) ≤ Real.log (|(m : ℝ)| + |s.im| + 3) := by
        refine Real.log_le_log (by linarith) ?_
        have h1 := abs_nonneg (m : ℝ)
        linarith
      have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2B : Real.log 2 ≤ Real.log (|s.im| + 2) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
      have hstep1 : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
          ≤ c₀ / (2 * Real.log (|s.im| + 2)) := by
        have hA : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
            ≤ c_h / (2 * Real.log (|(m : ℝ)| + |s.im| + 3)) := by
          refine div_le_div_of_nonneg_left hc_h.le (by positivity) ?_
          calc (2 : ℝ) * Real.log (|(m : ℝ)| + |s.im| + 3)
              = 2 * 1 * Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
            _ ≤ 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) :=
                mul_le_mul_of_nonneg_right (by linarith) hlogA.le
        have hB : c_h / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
            ≤ c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
          div_le_div_of_nonneg_right hc_h₀ (by positivity)
        have hC : c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
            ≤ c₀ / (2 * Real.log (|s.im| + 2)) := by
          have h1 : c₀ / (2 * Real.log (|(m : ℝ)| + |s.im| + 3))
              = (c₀ / 2) / Real.log (|(m : ℝ)| + |s.im| + 3) := by ring
          have h2 : c₀ / (2 * Real.log (|s.im| + 2))
              = (c₀ / 2) / Real.log (|s.im| + 2) := by ring
          rw [h1, h2]
          exact div_le_div_of_nonneg_left (by linarith) hlogB hlogBA
        exact hA.trans (hB.trans hC)
      have hmono : Real.log 2 / (Real.log 4 + Real.log 2)
          ≤ Real.log (|s.im| + 2) / (Real.log 4 + Real.log (|s.im| + 2)) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        have h3 : Real.log 2 * Real.log 4 ≤ Real.log (|s.im| + 2) * Real.log 4 :=
          mul_le_mul_of_nonneg_right hlog2B hlog4.le
        nlinarith [h3]
      have hc0 : c₀ ≤ 2 * c₃ * Real.log (|s.im| + 2) / (Real.log 4 + Real.log (|s.im| + 2)) := by
        have h3 : 2 * c₃ * Real.log 2 / (Real.log 4 + Real.log 2)
            ≤ 2 * c₃ * Real.log (|s.im| + 2) / (Real.log 4 + Real.log (|s.im| + 2)) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          have h4 : Real.log 2 * Real.log 4 ≤ Real.log (|s.im| + 2) * Real.log 4 :=
            mul_le_mul_of_nonneg_right hlog2B hlog4.le
          nlinarith [h4]
        exact le_trans hc₀₃ h3
      have hstep2 : c₀ / (2 * Real.log (|s.im| + 2)) ≤ c₃ / Real.log (4 * (|s.im| + 2)) := by
        rw [Real.log_mul (by norm_num) (by linarith [abs_nonneg s.im])]
        rw [div_le_div_iff₀ (by positivity) (by linarith)]
        have h4 : c₀ * (Real.log 4 + Real.log (|s.im| + 2))
            ≤ 2 * c₃ * Real.log (|s.im| + 2) := by
          have h5 : c₀ * (Real.log 4 + Real.log (|s.im| + 2))
              ≤ (2 * c₃ * Real.log (|s.im| + 2) / (Real.log 4 + Real.log (|s.im| + 2)))
                * (Real.log 4 + Real.log (|s.im| + 2)) :=
            mul_le_mul_of_nonneg_right hc0 (by linarith)
          have h6 : (2 * c₃ * Real.log (|s.im| + 2) / (Real.log 4 + Real.log (|s.im| + 2)))
              * (Real.log 4 + Real.log (|s.im| + 2)) = 2 * c₃ * Real.log (|s.im| + 2) := by
            field_simp
          exact h5.trans_eq h6
        linarith [h4]
      linarith [hdeep, hstep1, hstep2]

/-- **Analyticity of the candidate continuation** on the region (16.24) of `heartZcHyp`, in the
trivial-`ψ` regime. -/
theorem zcT_analytic {c₁ c₂ c₃ c₅ c₀ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hc₅ : 0 < c₅) (hc₀₁ : c₀ ≤ 2 * c₁)
    (hc₀₂ : c₀ ≤ 2 * (Real.log 3) * c₂ / (Real.log 4) ^ 9)
    (hc₀₃ : c₀ ≤ 2 * c₃ * Real.log 2 / (Real.log 4 + Real.log 2))
    (hc₀₅ : c₀ ≤ 2 * Real.log 3 * c₅)
    (hZ1 : ∀ σ t : ℝ, 2 ≤ |t| → 1 - c₁ / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hZ2 : ∀ σ t : ℝ, 1 - c₂ / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hC1 : ∀ σ t : ℝ, t ≠ 0 → 1 - c₃ / Real.log (4 * (|t| + 2)) ≤ σ →
      (Work.FIArea6Hecke.R.chi4C).LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hC5 : ∀ β : ℝ, 0 < β → β < 1 →
      (Work.FIArea6Hecke.R.chi4C).LFunction (β : ℂ) = 0 → c₅ ≤ 1 - β)
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (ε c_h : ℝ)
    (hd : 1 ≤ d) (hε : 0 < ε) (hc_h : 0 < c_h) (hc_h₀ : c_h ≤ c₀)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    AnalyticOn ℂ (zcTriv Pa chi m d) {s : ℂ | 1 / 2 < s.re ∧
      1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re} := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧
      1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re} with hU
  have hchi1 : chi 1 = 1 := hchi.1.1
  have hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hhalf : IsOpen {s : ℂ | 1 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hΦan : AnalyticOn ℂ (fun s => Work.FIArea6.TauPieces.Phifac chi m s)
      {s : ℂ | 1 / 2 < s.re} :=
    (Work.FIArea6Road.PhifacAnalyticBound chi m hchi1 hchimul hchibd).1
  have hUopen : IsOpen U := by
    rw [hU]
    have hin : Continuous (fun w : ℂ => |(m : ℝ)| + |w.im| + 3) :=
      (continuous_const.add Complex.continuous_im.abs).add continuous_const
    have hlogc : Continuous (fun w : ℂ => Real.log (|(m : ℝ)| + |w.im| + 3)) :=
      Continuous.log hin (fun w => by
        have h1 := abs_nonneg (m : ℝ)
        have h2 := abs_nonneg w.im
        linarith)
    have hcont : Continuous (fun w : ℂ =>
        1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3))) := by
      refine Continuous.sub continuous_const ?_
      refine Continuous.div continuous_const ?_ ?_
      · exact continuous_const.mul hlogc
      · intro w
        have h1 : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
        have h2 : 0 < Real.log (|(m : ℝ)| + |w.im| + 3) := by
          apply Real.log_pos
          have h3 := abs_nonneg (m : ℝ)
          have h4 := abs_nonneg w.im
          linarith
        positivity
    exact IsOpen.and (isOpen_lt continuous_const Complex.continuous_re)
      (isOpen_lt hcont Complex.continuous_re)
  -- analyticity of the candidate at points different from `1`
  have hF : ∀ z ∈ U, z ≠ 1 → AnalyticAt ℂ (zcTrivFun Pa chi m d) z := by
    intro z hz hzne
    have hzre : 0 < z.re := by linarith [hz.1]
    have hζnz : riemannZeta z ≠ 0 :=
      zcT_zeta_ne_zero hc₁ hc₂ hc₀₁ hc₀₂ hZ1 hZ2 hc_h hc_h₀ d hd ε hε m hz.1 hz.2
    have hLnz : (Work.FIArea6Hecke.R.chi4C).LFunction z ≠ 0 :=
      zcT_chi4_ne_zero hc₃ hc₅ hc₀₃ hc₀₅ hC1 hC5 hc_h hc_h₀ d hd ε hε m hz.1 hz.2
    have hGnz : Work.FIArea6Hecke.R.axisBadPoly d z ≠ 0 := zcT_axisBadPoly_ne_zero d hzre
    have hprod : riemannZeta z * (Work.FIArea6Hecke.R.chi4C).LFunction z
        * Work.FIArea6Hecke.R.axisBadPoly d z ≠ 0 :=
      mul_ne_zero (mul_ne_zero hζnz hLnz) hGnz
    have hζan : AnalyticAt ℂ riemannZeta z :=
      (DifferentiableOn.analyticOn (s := {w : ℂ | w ≠ 1})
        (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) isOpen_ne).analyticAt
        (isOpen_ne.mem_nhds hzne)
    have hLan : AnalyticAt ℂ (fun s => (Work.FIArea6Hecke.R.chi4C).LFunction s) z :=
      (DifferentiableOn.analyticOn (s := Set.univ)
        (fun w _ => (DirichletCharacter.differentiable_LFunction
          Work.FIArea6Hecke.R.chi4C_ne_one).differentiableAt.differentiableWithinAt)
        isOpen_univ).analyticAt Filter.univ_mem
    have hGan : AnalyticAt ℂ (fun s => Work.FIArea6Hecke.R.axisBadPoly d s) z :=
      (DifferentiableOn.analyticOn (s := Set.univ)
        (fun w _ => (Work.FIArea6Hecke.R.differentiableAt_axisBadPoly d w).differentiableWithinAt)
        isOpen_univ).analyticAt Filter.univ_mem
    have hRan : AnalyticAt ℂ (fun s => (riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
        * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹) z :=
      AnalyticAt.inv (AnalyticAt.mul (AnalyticAt.mul hζan hLan) hGan) hprod
    have hΦz : AnalyticAt ℂ (fun s => Work.FIArea6.TauPieces.Phifac chi m s) z :=
      hΦan.analyticAt (hhalf.mem_nhds hz.1)
    have hPan : AnalyticAt ℂ (fun s => Work.FIArea6.TauPieces.Pfac Pa chi m s) z :=
      (Work.FIArea6Road.zcontPfac_diff Pa chi m hchibd).analyticOn hhalf |>.analyticAt
        (hhalf.mem_nhds hz.1)
    have hQan : AnalyticAt ℂ (fun s => Work.FIArea6.TauPieces.Qfac Pa chi m s) z :=
      (Work.FIArea6Road.zcontQfac_diff Pa chi m hchibd).analyticOn hhalf |>.analyticAt
        (hhalf.mem_nhds hz.1)
    exact AnalyticAt.mul (AnalyticAt.mul (AnalyticAt.mul hΦz hRan) hPan) hQan
  -- continuity at `1`
  have hcont1 : ContinuousAt (zcTriv Pa chi m d) 1 := by
    obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ s : ℂ, s ≠ 1 → ‖s - 1‖ < δ →
        1 / ‖riemannZeta s‖ ≤ 2 * ‖s - 1‖ := by
      have h := Metric.tendsto_nhds.mp riemannZeta_residue_one (1 / 2) (by norm_num)
      rw [nhdsWithin, Filter.eventually_inf_principal] at h
      rw [Metric.eventually_nhds_iff] at h
      obtain ⟨ε', hε'pos, hε'⟩ := h
      refine ⟨ε', hε'pos, fun s hsne hslt => ?_⟩
      have h1 : dist ((s - 1) * riemannZeta s) 1 < 1 / 2 :=
        hε' (by rw [dist_eq_norm]; exact hslt) (by simpa using hsne)
      rw [dist_eq_norm] at h1
      have h2 : (1 : ℝ) / 2 ≤ ‖(s - 1) * riemannZeta s‖ := by
        have h3 : ‖(1 : ℂ)‖ - ‖(s - 1) * riemannZeta s‖
            ≤ ‖(1 : ℂ) - (s - 1) * riemannZeta s‖ :=
          norm_sub_norm_le (1 : ℂ) ((s - 1) * riemannZeta s)
        rw [norm_one, norm_sub_rev] at h3
        linarith
      rw [norm_mul] at h2
      have hs0 : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsne)
      have hz0 : 0 < ‖riemannZeta s‖ := by
        by_contra hc
        have h0 : ‖riemannZeta s‖ = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
        rw [h0, mul_zero] at h2
        linarith
      rw [div_le_iff₀ hz0]
      nlinarith [h2, hs0]
    have hL1 : (Work.FIArea6Hecke.R.chi4C).LFunction 1 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re Work.FIArea6Hecke.R.chi4C
        (Or.inl Work.FIArea6Hecke.R.chi4C_ne_one) (by norm_num)
    have hG1 : Work.FIArea6Hecke.R.axisBadPoly d 1 ≠ 0 := zcT_axisBadPoly_ne_zero d (by norm_num)
    have hΦcont : ContinuousAt (fun s => Work.FIArea6.TauPieces.Phifac chi m s) 1 :=
      (hΦan.analyticAt (hhalf.mem_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))).continuousAt
    have hPcont : ContinuousAt (fun s => Work.FIArea6.TauPieces.Pfac Pa chi m s) 1 :=
      ((Work.FIArea6Road.zcontPfac_diff Pa chi m hchibd).analyticOn hhalf).analyticAt
        (hhalf.mem_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)) |>.continuousAt
    have hQcont : ContinuousAt (fun s => Work.FIArea6.TauPieces.Qfac Pa chi m s) 1 :=
      ((Work.FIArea6Road.zcontQfac_diff Pa chi m hchibd).analyticOn hhalf).analyticAt
        (hhalf.mem_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)) |>.continuousAt
    have hLcont : ContinuousAt (fun s => (Work.FIArea6Hecke.R.chi4C).LFunction s) 1 :=
      (DifferentiableOn.analyticOn (s := Set.univ)
        (fun w _ => (DirichletCharacter.differentiable_LFunction
          Work.FIArea6Hecke.R.chi4C_ne_one).differentiableAt.differentiableWithinAt)
        isOpen_univ).analyticAt Filter.univ_mem |>.continuousAt
    have hGcont : ContinuousAt (fun s => Work.FIArea6Hecke.R.axisBadPoly d s) 1 :=
      (DifferentiableOn.analyticOn (s := Set.univ)
        (fun w _ => (Work.FIArea6Hecke.R.differentiableAt_axisBadPoly d w).differentiableWithinAt)
        isOpen_univ).analyticAt Filter.univ_mem |>.continuousAt
    have hΦb : ∀ᶠ s in 𝓝 (1 : ℂ), ‖Work.FIArea6.TauPieces.Phifac chi m s‖
        ≤ ‖Work.FIArea6.TauPieces.Phifac chi m 1‖ + 1 :=
      (hΦcont.norm.eventually (Iio_mem_nhds (by linarith))).mono fun s hs => hs.le
    have hPb : ∀ᶠ s in 𝓝 (1 : ℂ), ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
        ≤ ‖Work.FIArea6.TauPieces.Pfac Pa chi m 1‖ + 1 :=
      (hPcont.norm.eventually (Iio_mem_nhds (by linarith))).mono fun s hs => hs.le
    have hQb : ∀ᶠ s in 𝓝 (1 : ℂ), ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖
        ≤ ‖Work.FIArea6.TauPieces.Qfac Pa chi m 1‖ + 1 :=
      (hQcont.norm.eventually (Iio_mem_nhds (by linarith))).mono fun s hs => hs.le
    have hLb : ∀ᶠ s in 𝓝 (1 : ℂ),
        ‖((Work.FIArea6Hecke.R.chi4C).LFunction s)⁻¹‖
          ≤ 2 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖ := by
      have hpos : 0 < ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖ := norm_pos_iff.mpr hL1
      have hev : ∀ᶠ s in 𝓝 (1 : ℂ),
          ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖ / 2
            < ‖(Work.FIArea6Hecke.R.chi4C).LFunction s‖ :=
        hLcont.norm.eventually (Ioi_mem_nhds (by linarith))
      filter_upwards [hev] with s hs
      have hs0 : 0 < ‖(Work.FIArea6Hecke.R.chi4C).LFunction s‖ := lt_trans (by linarith) hs
      rw [norm_inv]
      have h2 : (2 : ℝ) / ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖
          = (‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖ / 2)⁻¹ := by
        field_simp
      rw [h2, inv_le_inv₀ hs0 (by linarith)]
      exact hs.le
    have hGb : ∀ᶠ s in 𝓝 (1 : ℂ),
        ‖(Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖
          ≤ 2 / ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖ := by
      have hpos : 0 < ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖ := norm_pos_iff.mpr hG1
      have hev : ∀ᶠ s in 𝓝 (1 : ℂ),
          ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖ / 2
            < ‖Work.FIArea6Hecke.R.axisBadPoly d s‖ :=
        hGcont.norm.eventually (Ioi_mem_nhds (by linarith))
      filter_upwards [hev] with s hs
      have hs0 : 0 < ‖Work.FIArea6Hecke.R.axisBadPoly d s‖ := lt_trans (by linarith) hs
      rw [norm_inv]
      have h2 : (2 : ℝ) / ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖
          = (‖Work.FIArea6Hecke.R.axisBadPoly d 1‖ / 2)⁻¹ := by
        field_simp
      rw [h2, inv_le_inv₀ hs0 (by linarith)]
      exact hs.le
    set C : ℝ := (‖Work.FIArea6.TauPieces.Phifac chi m 1‖ + 1)
        * ((2 * 1) * (2 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖)
            * (2 / ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖))
        * (‖Work.FIArea6.TauPieces.Pfac Pa chi m 1‖ + 1)
        * (‖Work.FIArea6.TauPieces.Qfac Pa chi m 1‖ + 1) with hCdef
    have hbound : ∀ᶠ s in 𝓝 (1 : ℂ), ‖zcTriv Pa chi m d s‖ ≤ C * ‖s - 1‖ := by
      filter_upwards [Metric.ball_mem_nhds (1 : ℂ) hδpos, hΦb, hPb, hQb, hLb, hGb]
        with s hsball hΦs hPs hQs hLs hGs
      rcases eq_or_ne s 1 with rfl | hsne
      · rw [zcTriv_one]
        simp
      · rw [zcTriv_apply_of_ne hsne, zcTrivFun]
        have hζs : ‖riemannZeta s‖⁻¹ ≤ 2 * ‖s - 1‖ := by
          rw [← one_div]
          exact hδ s hsne (by simpa [Metric.mem_ball, dist_eq_norm] using hsball)
        have hRs : ‖(riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
            * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖
            ≤ (2 * ‖s - 1‖) * (2 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖)
              * (2 / ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖) := by
          rw [mul_inv, mul_inv, norm_mul, norm_mul, norm_inv, norm_inv, norm_inv]
          exact mul_le_mul (mul_le_mul hζs (by simpa only [norm_inv] using hLs)
            (by positivity) (by positivity)) (by simpa only [norm_inv] using hGs)
            (by positivity) (by positivity)
        have h1 : ‖Work.FIArea6.TauPieces.Phifac chi m s‖
              * ‖(riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
                  * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖
              * ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
              * ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖
            ≤ (‖Work.FIArea6.TauPieces.Phifac chi m 1‖ + 1)
              * ((2 * ‖s - 1‖) * (2 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖)
                  * (2 / ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖))
              * (‖Work.FIArea6.TauPieces.Pfac Pa chi m 1‖ + 1)
              * (‖Work.FIArea6.TauPieces.Qfac Pa chi m 1‖ + 1) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hΦs hRs (by positivity) (by positivity)) hPs
            (by positivity) (by positivity)) hQs (by positivity) (by positivity)
        rw [show ‖Work.FIArea6.TauPieces.Phifac chi m s
              * (riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
                  * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹
              * Work.FIArea6.TauPieces.Pfac Pa chi m s
              * Work.FIArea6.TauPieces.Qfac Pa chi m s‖
            = ‖Work.FIArea6.TauPieces.Phifac chi m s‖
              * ‖(riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
                  * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖
              * ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
              * ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖ from by
            rw [norm_mul, norm_mul, norm_mul]]
        refine h1.trans ?_
        rw [hCdef]
        have h2 : (‖Work.FIArea6.TauPieces.Phifac chi m 1‖ + 1)
              * ((2 * ‖s - 1‖) * (2 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction 1‖)
                  * (2 / ‖Work.FIArea6Hecke.R.axisBadPoly d 1‖))
              * (‖Work.FIArea6.TauPieces.Pfac Pa chi m 1‖ + 1)
              * (‖Work.FIArea6.TauPieces.Qfac Pa chi m 1‖ + 1)
            = C * ‖s - 1‖ := by
          ring
        linarith [h2.le]
    rw [ContinuousAt, zcTriv_one Pa chi m d, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _) hbound ?_
    have h1 : Filter.Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      have hid : Filter.Tendsto (fun s : ℂ => s) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ)) := tendsto_id
      simpa using hid.sub_const (1 : ℂ)
    have h2 : Filter.Tendsto (fun s : ℂ => ‖s - 1‖) (𝓝 (1 : ℂ)) (𝓝 0) := by
      simpa using h1.norm
    have h3 : Filter.Tendsto (fun s : ℂ => C * ‖s - 1‖) (𝓝 (1 : ℂ)) (𝓝 0) := by
      have := (tendsto_const_nhds (x := C) (f := 𝓝 (1 : ℂ))).mul h2
      simpa using this
    exact h3
  intro z hz
  rcases eq_or_ne z 1 with rfl | hzne
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hcont1).analyticWithinAt
    have h1U : (1 : ℂ) ∈ U := by
      refine ⟨by norm_num, ?_⟩
      have hlog : 0 < Real.log (|(m : ℝ)| + |(1 : ℂ).im| + 3) := by
        apply Real.log_pos
        have h1 := abs_nonneg (m : ℝ)
        simp only [Complex.one_im, abs_zero]
        linarith
      have hden : 0 < 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |(1 : ℂ).im| + 3) := by
        have h2 : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
        positivity
      have hpos : 0 < c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |(1 : ℂ).im| + 3)) :=
        div_pos hc_h hden
      simp only [Complex.one_re]
      linarith
    filter_upwards [nhdsWithin_le_nhds (hUopen.mem_nhds h1U), self_mem_nhdsWithin]
      with w hwU hwne
    have hw : AnalyticAt ℂ (zcTriv Pa chi m d) w :=
      (hF w hwU hwne).congr (by
        filter_upwards [isOpen_ne.mem_nhds hwne] with t ht
        exact (zcTriv_apply_of_ne ht).symm)
    exact hw.differentiableAt
  · refine ((hF z hz hzne).congr ?_).analyticWithinAt
    filter_upwards [isOpen_ne.mem_nhds hzne] with w hw
    exact (zcTriv_apply_of_ne hw).symm

/-! ## 5. The bound (16.35) on the region -/

/-- **The inverse bound of the candidate continuation**: on the region of `heartZcHyp` (and
`Re s ≤ 2`), `‖(ζ·L(·,χ₄)·G_d)⁻¹‖ ≤ C_R·d·log²(|m| + |Im s| + 3)`, from the two inverse bounds of
the zero-free region and the bad-prime bound. -/
theorem zcT_Rbound {cζ Cζ cχ Cχ KB c₀ : ℝ} (hcζ : 0 < cζ) (hCζ : 0 < Cζ) (hcχ : 0 < cχ)
    (hCχ : 0 < Cχ) (hKB : 0 < KB) (hc₀ : 0 < c₀) (hc₀ζ : c₀ ≤ 2 * cζ)
    (hc₀χ : c₀ ≤ 2 * cχ * Real.log 2 / (Real.log 4 + Real.log 2))
    (hζ : ∀ σ t : ℝ, 1 - cζ / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Cζ * (Real.log (|t| + 2) + 1))
    (hχ : ∀ σ t : ℝ, 1 - cχ / Real.log (4 * (|t| + 2)) ≤ σ → σ ≤ 2 →
      1 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Cχ * Real.log (4 * (|t| + 2)))
    (hB : ∀ d : ℕ, 1 ≤ d → ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re →
      ‖(Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖ ≤ KB * (d : ℝ))
    (Pa : Work.FITop.Params) (m : ℤ) (d : ℕ) (ε c_h : ℝ) (hd : 1 ≤ d) (hε : 0 < ε)
    (hc_h : 0 < c_h) (hc_h₀ : c_h ≤ c₀) {s : ℂ} (hs2 : s.re ≤ 2) (hs1 : (1 / 2 : ℝ) < s.re)
    (hdeep : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re) :
    ‖(riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
        * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖
      ≤ (2 * Cζ * (1 + Real.log 4) * Cχ * KB) * (d : ℝ)
          * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ 2 := by
  set b : ℝ := Real.log (|(m : ℝ)| + |s.im| + 3) with hbdef
  have hA1 : (1 : ℝ) < |(m : ℝ)| + |s.im| + 3 := by
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hb1 : 1 ≤ b := by
    rw [hbdef]
    have h3 : (3 : ℝ) ≤ |(m : ℝ)| + |s.im| + 3 := by
      have h1 := abs_nonneg (m : ℝ)
      have h2 := abs_nonneg s.im
      linarith
    have h4 : Real.exp 1 ≤ |(m : ℝ)| + |s.im| + 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (|(m : ℝ)| + |s.im| + 3) := Real.log_le_log (Real.exp_pos 1) h4
  have hbpos : 0 < b := by linarith
  have hlogB : Real.log (|s.im| + 2) ≤ b := by
    rw [hbdef]
    refine Real.log_le_log (by linarith [abs_nonneg s.im]) ?_
    have h1 := abs_nonneg (m : ℝ)
    linarith
  have hσζ := zcT_region_zeta hcζ hc₀ζ hc_h hc_h₀ d hd ε hε m hdeep
  have hσχ := zcT_region_chi4 hcχ hc₀χ hc_h hc_h₀ d hd ε hε m hdeep
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have e1 : 1 / ‖riemannZeta s‖ ≤ Cζ * (2 * b) := by
    have h := hζ s.re s.im hσζ hs2
    rw [Complex.re_add_im s] at h
    have h2 : Real.log (|s.im| + 2) + 1 ≤ 2 * b := by linarith
    exact h.trans (mul_le_mul_of_nonneg_left h2 hCζ.le)
  have e2 : 1 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction s‖ ≤ Cχ * ((1 + Real.log 4) * b) := by
    have h := hχ s.re s.im hσχ hs2
    rw [Complex.re_add_im s] at h
    have hlog4eq : Real.log (4 * (|s.im| + 2))
        = Real.log 4 + Real.log (|s.im| + 2) :=
      Real.log_mul (by norm_num) (by linarith [abs_nonneg s.im])
    rw [hlog4eq] at h
    have h2 : Real.log 4 + Real.log (|s.im| + 2) ≤ (1 + Real.log 4) * b := by
      nlinarith [hb1, hlogB, hlog4]
    exact h.trans (mul_le_mul_of_nonneg_left h2 hCχ.le)
  have e3 : 1 / ‖Work.FIArea6Hecke.R.axisBadPoly d s‖ ≤ KB * (d : ℝ) := by
    have h := hB d hd s (le_of_lt hs1)
    simpa only [norm_inv, one_div] using h
  calc ‖(riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
        * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖
      = (1 / ‖riemannZeta s‖) * (1 / ‖(Work.FIArea6Hecke.R.chi4C).LFunction s‖)
          * (1 / ‖Work.FIArea6Hecke.R.axisBadPoly d s‖) := by
        rw [mul_inv, mul_inv, norm_mul, norm_mul, norm_inv, norm_inv, norm_inv,
          one_div, one_div, one_div]
    _ ≤ (Cζ * (2 * b)) * (Cχ * ((1 + Real.log 4) * b)) * (KB * (d : ℝ)) := by
        refine mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3
          (by positivity) (by positivity)
    _ = (2 * Cζ * (1 + Real.log 4) * Cχ * KB) * (d : ℝ) * b ^ 2 := by ring

/-! ## 6. The target -/

theorem HeartZcTrivial (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ K_z c₀ : ℝ, 0 < K_z ∧ 0 < c₀ ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (c_h : ℝ),
        0 < c_h → c_h ≤ c₀ → 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → 4 ≤ Real.log (Pa.Pz : ℝ) →
        (∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d z →
          Work.FIArea5.S16Hecke.psi chi m z = 1) →
        ∃ (C_z : ℝ) (Zc : ℂ → ℂ), C_z ≤ K_z ∧
          Work.FIArea6Road.heartZcHyp Pa chi m d ε c_h C_z Zc := by
  obtain ⟨cζ, Cζ, hcζ, hCζ, hζ⟩ := Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
  obtain ⟨cχ, Cχ, hcχ, hCχ, hχ⟩ := zcT_Chi4Inv
  obtain ⟨KB, hKB, hB⟩ := zcT_AxisBad
  obtain ⟨KΦ, hKΦ, hΦ⟩ := Work.FIArea6Road.PhifacBoundUniform
  obtain ⟨KP, hKP, hP⟩ := Work.FIArea6Road.ZT.PfacBoundSharpZT
  obtain ⟨KQ1, hKQ1, hQ1⟩ := Work.FIArea6Road.zcub_QfacBoundUniformRatio
  obtain ⟨KQ2, hKQ2, hQ2⟩ := zcT_QfacTwo
  obtain ⟨CA, hCA, hA⟩ := Work.FIArea6Road.ZcBoundArith_proved
  obtain ⟨c₁, hc₁, hZ1⟩ := Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_log
  obtain ⟨c₂, hc₂, hZ2⟩ := Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_all_t
  obtain ⟨c₃, hc₃, hC1raw⟩ := Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨c₅, hc₅, K₅, hK₅, hC5raw⟩ := Commons.NumberTheory.DirichletCharacter.LFunction_real_zero_bound
    Work.FIArea6Hecke.R.chi4C Work.FIArea6Road.chi4C_isPrimitive
  have hC1 : ∀ σ t : ℝ, t ≠ 0 → 1 - c₃ / Real.log (4 * (|t| + 2)) ≤ σ →
      (Work.FIArea6Hecke.R.chi4C).LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro σ t ht hreg
    exact hC1raw Work.FIArea6Hecke.R.chi4C Work.FIArea6Road.chi4C_isPrimitive
      Work.FIArea6Hecke.R.chi4C_ne_one σ t ht (by simpa using hreg)
  set c₅' : ℝ := c₅ / (4 : ℝ) ^ K₅ with hc₅'def
  have hc₅' : 0 < c₅' := by
    rw [hc₅'def]
    exact div_pos hc₅ (Real.rpow_pos_of_pos (by norm_num) _)
  have hC5 : ∀ β : ℝ, 0 < β → β < 1 →
      (Work.FIArea6Hecke.R.chi4C).LFunction (β : ℂ) = 0 → c₅' ≤ 1 - β := by
    intro β hβ0 hβ1 hzero
    have h := hC5raw β hβ0 hβ1 hzero
    rwa [hc₅'def]
  set CR : ℝ := 2 * Cζ * (1 + Real.log 4) * Cχ * KB with hCRdef
  set K1 : ℝ := KΦ * CR * KP * KQ1 * CA with hK1def
  set K2 : ℝ := KΦ * CR * KP * KQ2 * CA with hK2def
  set Kz : ℝ := max K1 K2 with hKzdef
  set c₀ : ℝ := min (2 * cζ)
      (min (2 * cχ * Real.log 2 / (Real.log 4 + Real.log 2))
      (min (2 * c₁)
      (min (2 * (Real.log 3) * c₂ / (Real.log 4) ^ 9)
      (min (2 * c₃ * Real.log 2 / (Real.log 4 + Real.log 2))
      (min (2 * (Real.log 3) * c₅') 1))))) with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    positivity
  have hKzpos : 0 < Kz := by
    rw [hKzdef]
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    rw [hK1def, hCRdef]
    positivity
  refine ⟨Kz, c₀, hKzpos, hc₀pos, ?_⟩
  intro Pa chi m d c_h hc_h_pos hc_h_le hd hchi hlogPz htriv
  have hc0ζ : c₀ ≤ 2 * cζ := by
    rw [hc₀def]
    exact min_le_left _ _
  have hc0χ : c₀ ≤ 2 * cχ * Real.log 2 / (Real.log 4 + Real.log 2) := by
    rw [hc₀def]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hc0₁ : c₀ ≤ 2 * c₁ := by
    rw [hc₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc0₂ : c₀ ≤ 2 * (Real.log 3) * c₂ / (Real.log 4) ^ 9 := by
    rw [hc₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hc0₃ : c₀ ≤ 2 * c₃ * Real.log 2 / (Real.log 4 + Real.log 2) := by
    rw [hc₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hc0₅ : c₀ ≤ 2 * (Real.log 3) * c₅' := by
    rw [hc₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hchi1 : chi 1 = 1 := hchi.1.1
  have hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  refine ⟨Kz, zcTriv Pa chi m d, (by linarith : Kz ≤ Kz), ?_,
    (fun s hs => zcT_agree Pa chi m d hd hchi htriv hs),
    zcT_analytic (c₀ := c₀) hc₁ hc₂ hc₃ hc₅' hc0₁ hc0₂ hc0₃ hc0₅ hZ1 hZ2 hC1 hC5 Pa chi m d ε c_h hd hε
      hc_h_pos hc_h_le hchi, ?_, ?_⟩
  · rw [hKzdef]
    have hK1pos : 0 < K1 := by
      rw [hK1def, hCRdef]
      positivity
    exact lt_of_lt_of_le hK1pos (le_max_left K1 K2)
  · -- clause (16.32): `σ ≤ 1` with the saving `C^{1-σ}`
    intro s hs1 hsPz hsdeep hs2
    rcases eq_or_ne s 1 with rfl | hsne
    · rw [zcTriv_one]
      have hLnn : (0 : ℝ) ≤ Real.log (Pa.N) + Real.log (|(m : ℝ)| + |(1 : ℂ).im| + 3) + 2 :=
        heart_L_nonneg Pa m 1
      have hCnn : (0 : ℝ) ≤ Pa.C ^ (1 - (1 : ℂ).re) :=
        Real.rpow_nonneg (by linarith [Pa.hC1]) _
      have hnn : (0 : ℝ) ≤ Kz * (d : ℝ) * Pa.C ^ (1 - (1 : ℂ).re)
          * (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |(1 : ℂ).im| + 3) + 2) ^ 6 :=
        mul_nonneg (mul_nonneg (mul_nonneg hKzpos.le (by positivity)) hCnn) (pow_nonneg hLnn 6)
      simpa using hnn
    · rw [zcTriv_apply_of_ne hsne, zcTrivFun]
      set b : ℝ := Real.log (|(m : ℝ)| + |s.im| + 3) with hbdef
      set L : ℝ := Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 with hLdef
      set L' : ℝ := Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) with hL'def
      have h34 : (3 / 4 : ℝ) ≤ s.re := by
        have hpos : 0 < Real.log (Pa.Pz : ℝ) := by linarith
        have hle : 1 / Real.log (Pa.Pz : ℝ) ≤ 1 / 4 := by
          rw [div_le_iff₀ hpos]; linarith
        linarith
      have hΦs := hΦ chi m hchi1 hchimul hchibd s h34
      have hRs := zcT_Rbound (c₀ := c₀) hcζ hCζ hcχ hCχ hKB hc₀pos hc0ζ hc0χ hζ hχ hB Pa m d ε c_h hd hε
        hc_h_pos hc_h_le (by linarith) hs1 hsdeep
      have hPs := hP Pa chi m hchi1 hchimul hchibd hlogPz s hsPz
      have hQs := hQ1 Pa chi m hchi1 hchimul hchibd Pa.hC1 hlogPz s h34 hsPz hs2
      have hArith := hA Pa m s Pa.hC1 hlogPz
      have hLle : L' ≤ L := heart_logN_add_three_le Pa m s
      have hL'nonneg : (0 : ℝ) ≤ L' := by
        rw [hL'def]
        have h1 : (1 : ℝ) < |(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3 := by
          have h2 := abs_nonneg (m : ℝ)
          have h3 := abs_nonneg s.im
          have h4 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
          linarith
        exact Real.log_nonneg (by linarith)
      have hprod : ‖Work.FIArea6.TauPieces.Phifac chi m s
            * (riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
                * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹
            * Work.FIArea6.TauPieces.Pfac Pa chi m s
            * Work.FIArea6.TauPieces.Qfac Pa chi m s‖
          ≤ KΦ * (CR * (d : ℝ) * b ^ 2)
            * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
            * (KQ1 * Pa.C ^ (1 - s.re)
                * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)) := by
        rw [norm_mul, norm_mul, norm_mul]
        refine mul_le_mul (mul_le_mul (mul_le_mul hΦs hRs (by positivity) (by positivity)) hPs
          (by positivity) (by positivity)) hQs (by positivity) (by positivity)
      have hrearr : KΦ * (CR * (d : ℝ) * b ^ 2)
            * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
            * (KQ1 * Pa.C ^ (1 - s.re)
                * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ))
          = (KΦ * CR * KP * KQ1) * (d : ℝ) * Pa.C ^ (1 - s.re)
            * ((Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
                * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * b ^ 2) := by
        ring
      refine hprod.trans ?_
      rw [hrearr]
      have h2 : (0 : ℝ) ≤ (d : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ Pa.C ^ (1 - s.re) := Real.rpow_nonneg (by linarith [Pa.hC1]) _
      have h4 : (0 : ℝ) ≤ L ^ 6 := by
        rw [hLdef]
        exact pow_nonneg (heart_L_nonneg Pa m s) 6
      have hstep : (KΦ * CR * KP * KQ1) * (d : ℝ) * Pa.C ^ (1 - s.re)
            * ((Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
                * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * b ^ 2)
          ≤ (KΦ * CR * KP * KQ1) * (d : ℝ) * Pa.C ^ (1 - s.re) * (CA * L' ^ 6) := by
        refine mul_le_mul_of_nonneg_left hArith ?_
        have ha : (0 : ℝ) ≤ KΦ * CR * KP * KQ1 := by positivity
        exact mul_nonneg (mul_nonneg ha h2) h3
      refine hstep.trans ?_
      have hpow : L' ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ hL'nonneg hLle 6
      have h5 : (KΦ * CR * KP * KQ1) * (d : ℝ) * Pa.C ^ (1 - s.re) * (CA * L' ^ 6)
          ≤ (KΦ * CR * KP * KQ1 * CA) * (d : ℝ) * Pa.C ^ (1 - s.re) * L ^ 6 := by
        rw [show (KΦ * CR * KP * KQ1) * (d : ℝ) * Pa.C ^ (1 - s.re) * (CA * L' ^ 6)
            = (KΦ * CR * KP * KQ1 * CA) * (d : ℝ) * Pa.C ^ (1 - s.re) * L' ^ 6 from by ring]
        have ha : (0 : ℝ) ≤ KΦ * CR * KP * KQ1 * CA := by positivity
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg ha h2) h3)
      have h6 : (KΦ * CR * KP * KQ1 * CA) * (d : ℝ) * Pa.C ^ (1 - s.re) * L ^ 6
          ≤ Kz * (d : ℝ) * Pa.C ^ (1 - s.re) * L ^ 6 := by
        rw [hKzdef]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left K1 K2) h2) h3) h4
      exact h5.trans h6
  · -- clause (16.35) on the strip `1 < σ ≤ 1 + 1/log N`
    intro s hs1 hsN hs2
    rw [zcTriv_apply_of_ne (by intro h; rw [h] at hs1; norm_num at hs1), zcTrivFun]
    set b : ℝ := Real.log (|(m : ℝ)| + |s.im| + 3) with hbdef
    set L : ℝ := Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 with hLdef
    set L' : ℝ := Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) with hL'def
    have hΦs := hΦ chi m hchi1 hchimul hchibd s (by linarith)
    have hdepth : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re := by
      have hlog : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) := by
        apply Real.log_pos
        have h2 := abs_nonneg (m : ℝ)
        have h3 := abs_nonneg s.im
        linarith
      have hden : 0 < 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by
        have h1 : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
        positivity
      have hp : 0 < c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
        div_pos hc_h_pos hden
      linarith
    have hRs := zcT_Rbound (c₀ := c₀) hcζ hCζ hcχ hCχ hKB hc₀pos hc0ζ hc0χ hζ hχ hB Pa m d ε c_h
      hd hε hc_h_pos hc_h_le hs2 (by linarith) hdepth
    have hPzreg : 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re := by
      have hlogpos : 0 < Real.log (Pa.Pz : ℝ) := by linarith
      have hposinv : 0 < 1 / Real.log (Pa.Pz : ℝ) := by positivity
      have hle : 1 / Real.log (Pa.Pz : ℝ) ≤ 1 / 4 := by
        rw [div_le_iff₀ hlogpos]
        linarith
      linarith
    have hPs := hP Pa chi m hchi1 hchimul hchibd hlogPz s hPzreg
    have hQs := hQ2 Pa chi m hchi1 hchimul hchibd Pa.hC1 hlogPz s (le_of_lt hs1) hs2
    have hArith := hA Pa m s Pa.hC1 hlogPz
    have hLle : L' ≤ L := heart_logN_add_three_le Pa m s
    have hL'nonneg : (0 : ℝ) ≤ L' := by
      rw [hL'def]
      have h1 : (1 : ℝ) < |(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3 := by
        have h2 := abs_nonneg (m : ℝ)
        have h3 := abs_nonneg s.im
        have h4 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
        linarith
      exact Real.log_nonneg (by linarith)
    have hprod : ‖Work.FIArea6.TauPieces.Phifac chi m s
          * (riemannZeta s * (Work.FIArea6Hecke.R.chi4C).LFunction s
              * Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹
          * Work.FIArea6.TauPieces.Pfac Pa chi m s
          * Work.FIArea6.TauPieces.Qfac Pa chi m s‖
        ≤ KΦ * (CR * (d : ℝ) * b ^ 2)
          * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
          * (KQ2 * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)) := by
      rw [norm_mul, norm_mul, norm_mul]
      refine mul_le_mul (mul_le_mul (mul_le_mul hΦs hRs (by positivity) (by positivity)) hPs
        (by positivity) (by positivity)) hQs (by positivity) (by positivity)
    have hrearr : KΦ * (CR * (d : ℝ) * b ^ 2)
          * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
          * (KQ2 * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ))
        = (KΦ * CR * KP * KQ2) * (d : ℝ)
          * (((Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
              * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)) * b ^ 2) := by
      ring
    refine hprod.trans ?_
    rw [hrearr]
    have h2 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ L ^ 6 := by
      rw [hLdef]
      exact pow_nonneg (heart_L_nonneg Pa m s) 6
    have hstep : (KΦ * CR * KP * KQ2) * (d : ℝ)
          * ((Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
              * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * b ^ 2)
        ≤ (KΦ * CR * KP * KQ2) * (d : ℝ) * (CA * L' ^ 6) := by
      refine mul_le_mul_of_nonneg_left hArith ?_
      have ha : (0 : ℝ) ≤ KΦ * CR * KP * KQ2 := by positivity
      exact mul_nonneg ha h2
    refine hstep.trans ?_
    have hpow : L' ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ hL'nonneg hLle 6
    have h5 : (KΦ * CR * KP * KQ2) * (d : ℝ) * (CA * L' ^ 6)
        ≤ (KΦ * CR * KP * KQ2 * CA) * (d : ℝ) * L ^ 6 := by
      rw [show (KΦ * CR * KP * KQ2) * (d : ℝ) * (CA * L' ^ 6)
          = (KΦ * CR * KP * KQ2 * CA) * (d : ℝ) * L' ^ 6 from by ring]
      have ha : (0 : ℝ) ≤ KΦ * CR * KP * KQ2 * CA := by positivity
      exact mul_le_mul_of_nonneg_left hpow (mul_nonneg ha h2)
    have h6 : (KΦ * CR * KP * KQ2 * CA) * (d : ℝ) * L ^ 6
        ≤ Kz * (d : ℝ) * L ^ 6 := by
      rw [hKzdef]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right K1 K2) h2) h4
    exact h5.trans h6

end

end Work.FIArea6Road
