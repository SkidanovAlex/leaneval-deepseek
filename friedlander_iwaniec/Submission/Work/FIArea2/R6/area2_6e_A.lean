/-
# `FIArea2/R6/area2_6e_A.lean` — the (9.10) half of the round-6 area-2 estimate

This module proves `Work.FIArea2.R6.area2_6e_A`: for every `η ∈ (0,3/32)` there are constants
`Cb, x0 > 0` such that for every parameter set `Pa` with `Pa.η = η` and `Pa.x ≥ x0`, every
round-6 majorant `f` and every round-6 coefficient `β`,

  `‖D*(Pa;f,β) − D₀^exact(Pa; majF Pa f hf, β)‖ ≤ Cb·ϑ⁻¹τ²N²(log N)^{bFun η}`,

i.e. *FI* (9.10) with the **exact** main term `D0ex` of (6.13) (the `h = 0` Poisson term with the
exact Fourier integral `Fint F γ 0 0`), where `majF Pa f hf` is the compactly supported `C⁴`
interpolant of `f` produced by `majorant6_trunc`.

The proof is the triangle/pair-sum decomposition of `ExactMain`:
`D* − D₀^exact` is the `Re(β_{z₁}β̄_{z₂})`-weighted sum of the per-pair Poisson errors of (9.1)
(`Dstar_sub_D0ex`, `abs_Dstar_sub_D0ex_le`); each per-pair error is bounded by the general-majorant
(9.1) estimate, and the resulting sum is exactly `sec9ErrSum6` (the §9 corrector sum of
`Area6eDefs`), which `sec9ErrSum6_bound` bounds by `Cb·ϑ⁻¹τ²N²(log N)^{bFun η}`.

The (9.1) estimate for a *general* round-6 majorant rests on Lemma 7.1 of FI with a general
derivative constant `Cder` and support window `[A,B]`, `M/64 ≤ A`, `B ≤ 64M`.  In this workspace
that chain (`lemma_7_1_gen` → `sec9_error_gen` → `sec9_error_of_pair_H_gen`) currently passes
through the `sorry`-ed pointwise Faà-di-Bruno bound `deriv4_pointwise_gen`.  We therefore re-run
the chain here against the clean pointwise bound `deriv4_pointwise_gen_clean` (produced in
parallel), keeping every declaration `sorry`-free:
`lemma_7_1_gen_clean` → `sec9_error_gen_clean` → `sec9_error_pair_clean`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.Inputs6
import Submission.Work.FIArea2.R6.BetaFacts6
import Submission.Work.FIArea2.R6.BetaPrim6
import Submission.Work.FIArea2.R6.Assembly6
import Submission.Work.FIArea2.R6.Pack6
import Submission.Work.FIArea2.R6.ExactMain
import Submission.Work.FIArea2.R6.Sec9Gen
import Submission.Work.FIArea2.R6.sec9Psum_le_of_Lsum_six
import Submission.Work.FIArea2.R6.sec9_Z_bound_six
import Submission.Work.FIArea2.R6.majorant6_trunc
import Submission.Work.FIArea2.R6.Area6eDefs
import Submission.Work.FIArea2.R6.GenRegion
import Submission.Work.FIArea2.R6.deriv4_pointwise_gen_clean
import Submission.Work.FIArea2.R6.sec9ErrSum6_bound
import Submission.Work.FIArea4.GaussMoebiusCore

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open MeasureTheory
open scoped BigOperators
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1.  Elementary helpers -/

/-- `‖(x : ℂ)‖ = |x|`. -/
theorem norm_ofReal_coe_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `|z|²` in coordinates. -/
lemma gnorm_cast_real (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) = ((z.re : ℝ)) ^ 2 + ((z.im : ℝ)) ^ 2 := by
  have h := Work.FIArea4.gnorm_eq_coords z
  have h2 : ((Work.FIPlan.gnorm z : ℤ) : ℝ) = ((z.re : ℝ)) ^ 2 + ((z.im : ℝ)) ^ 2 := by
    rw [h]; push_cast; ring
  have h3 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) = ((Work.FIPlan.gnorm z : ℤ) : ℝ) := by
    push_cast; ring
  rw [h3, h2]

/-- A Gaussian integer of norm `≤ 4M` lies in the outer box `boxM Pa = gBox ⌈√(4M)⌉`. -/
lemma mem_boxM_of_gnorm_le (Pa : Work.FITop.Params) {w : GaussianInt}
    (h : (Work.FIPlan.gnorm w : ℝ) ≤ 4 * Pa.M) : w ∈ Work.FITop.boxM Pa := by
  have hcast := gnorm_cast_real w
  have hM0 : (0 : ℝ) ≤ Pa.M := le_trans zero_le_one Pa.hM1
  have hre : |((w.re : ℝ))| ≤ Real.sqrt (4 * Pa.M) := by
    have h1 : ((w.re : ℝ)) ^ 2 ≤ 4 * Pa.M := by
      have h2 := h; rw [hcast] at h2
      nlinarith [sq_nonneg ((w.im : ℝ))]
    calc |((w.re : ℝ))| = Real.sqrt (((w.re : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (4 * Pa.M) := Real.sqrt_le_sqrt h1
  have him : |((w.im : ℝ))| ≤ Real.sqrt (4 * Pa.M) := by
    have h1 : ((w.im : ℝ)) ^ 2 ≤ 4 * Pa.M := by
      have h2 := h; rw [hcast] at h2
      nlinarith [sq_nonneg ((w.re : ℝ))]
    calc |((w.im : ℝ))| = Real.sqrt (((w.im : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (4 * Pa.M) := Real.sqrt_le_sqrt h1
  have hrad : Real.sqrt (4 * Pa.M) ≤ ((Work.FITop.radM Pa : ℤ) : ℝ) := by
    have h2 : ((Work.FITop.radM Pa : ℤ) : ℝ) = ((⌈Real.sqrt (4 * Pa.M)⌉₊ : ℕ) : ℝ) := by
      unfold Work.FITop.radM; push_cast; ring
    rw [h2]
    exact Nat.le_ceil _
  have hreb : |w.re| ≤ Work.FITop.radM Pa := by
    have h1 : ((|w.re| : ℤ) : ℝ) ≤ ((Work.FITop.radM Pa : ℤ) : ℝ) := by
      have h2 : ((|w.re| : ℤ) : ℝ) = |((w.re : ℝ))| := by rw [Int.cast_abs]
      rw [h2]; exact le_trans hre hrad
    exact_mod_cast h1
  have himb : |w.im| ≤ Work.FITop.radM Pa := by
    have h1 : ((|w.im| : ℤ) : ℝ) ≤ ((Work.FITop.radM Pa : ℤ) : ℝ) := by
      have h2 : ((|w.im| : ℤ) : ℝ) = |((w.im : ℝ))| := by rw [Int.cast_abs]
      rw [h2]; exact le_trans him hrad
    exact_mod_cast h1
  obtain ⟨h1, h2⟩ := abs_le.mp hreb
  obtain ⟨h3, h4⟩ := abs_le.mp himb
  rw [Work.FITop.boxM, Work.FIArea4.mem_gBox]
  exact ⟨h1, h2, h3, h4⟩

/-! ## 2.  The clean (sorry-free) §7/§9 chain for a general round-6 majorant -/

/-- **Lemma 7.1 of FI for the general round-6 majorant.**  A `C⁴` function `f` supported in `[A,B]`
with `M/64 ≤ A`, `B ≤ 64 M`, `|f^{(j)}| ≤ Cder·M^{−j}` (`j ≤ 4`, `Cder ≥ 1`) satisfies

  `‖∫∫ f(t₁⁴−2γt₁²t₂²+t₂⁴)e(u₁t₁+u₂t₂)dt₁dt₂‖`
    `≤ C·Cder·(1+u₁²δ√M)^{−1}(1+u₂²δ√M)^{−1}·√M·log(2+δ^{−2})`, `δ² = 1 − γ²`,

with the absolute constant `C = 10^13`. -/
theorem lemma_7_1_gen_clean (M : ℝ) (hM : 1 ≤ M) (A B Cder : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hB : B ≤ 64 * M) (hCder : 1 ≤ Cder)
    (f : ℝ → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ContDiff ℝ 4 f) (hfsupp : ∀ u : ℝ, f u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ Cder * M ^ (-(j : ℝ)))
    (u₁ u₂ : ℝ) :
    ‖Work.FIArea2.Fint f γ u₁ u₂‖ ≤ 10 ^ 13 * Cder
      * (1 + u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
      * (1 + u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt M)⁻¹
      * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have h1γ : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ]
  have hvolle := vol_regG_le M γ A B hM hγ0 hγ1 hA hAB hB
  have hvol : volume (regG A B γ) < ⊤ := lt_of_le_of_lt hvolle ENNReal.ofReal_lt_top
  have hvolb : (volume (regG A B γ)).toReal
      ≤ 2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
    have hlog : 0 ≤ Real.log (2 + 1 / (1 - γ ^ 2)) := by
      apply Real.log_nonneg
      have h1 : 0 < 1 / (1 - γ ^ 2) := by positivity
      linarith
    calc (volume (regG A B γ)).toReal
        ≤ (ENNReal.ofReal (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hvolle
      _ = 2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
          rw [ENNReal.toReal_ofReal]
          positivity
  have hpt : ∀ t₁ t₂ : ℝ, ‖iteratedDeriv 4 (fun s : ℝ => (f (Work.FIArea2.gq γ s t₂) : ℂ)) t₁‖
      ≤ 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹
        * Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂) :=
    fun t₁ t₂ => deriv4_pointwise_gen_clean M γ A B Cder f hM hγ0 hγ1 hB hCder hf hfsupp hfd t₁ t₂
  exact lemma_7_1_gen_core M hM A B Cder hA hAB hB hCder f γ hγ0 hγ1 hf hfsupp hfd
    hvol hvolb hpt u₁ u₂


/-- **(9.1) for the general round-6 majorant**, in the sharp form used by §9: the error at a pair is
`≤ K·Cder·|z₁z₂|^{−1/4}·τ(Δ)³|Δ|^{−1}√M·log(2+δ^{−2})·H(z₁,z₂)` with an absolute `K = 4·10^13`. -/
theorem sec9_error_gen_clean (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hA : Pa.M / 64 ≤ A) (hB : B ≤ 64 * Pa.M) (hCder1 : 1 ≤ Cder)
    (hF : ContDiff ℝ 4 F) (hcs : HasCompactSupport F)
    (hcop : IsCoprime z1 z2) (hp1 : IsCoprime z1 (star z1)) (hp2 : IsCoprime z2 (star z2))
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hbox : ∀ w : GaussianInt, F (Work.FIPlan.gnorm w) ≠ 0 → w ∈ Work.FITop.boxM Pa)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ Cder * Pa.M ^ (-(j : ℝ)))
    (hM : 1 ≤ Pa.M) (hγ0 : 0 ≤ Work.FIArea2.gamOf z1 z2) :
    ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
        - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
            * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                * Work.FIArea2.Gsum z1 z2 0 0)‖
      ≤ 4 * 10 ^ 13 * Cder * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
          * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
              * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
              * Work.FIArea2.Haver Pa z1 z2) := by
  by_cases hAB : A ≤ B
  · have hA0 : 0 < A := by
      have : (0 : ℝ) < Pa.M / 64 := by linarith
      linarith
    set γ : ℝ := Work.FIArea2.gamOf z1 z2 with hγdef
    have hγ0' : 0 ≤ γ := by rw [hγdef]; exact hγ0
    have hγ1 : γ < 1 := by rw [hγdef]; exact Work.FIArea2.gamOf_lt_one_of_Delta_ne_zero hΔ
    have hCder0 : 0 ≤ Cder := le_trans zero_le_one hCder1
    have hG : ∀ h1 h2 : ℤ, ‖Work.FIArea2.Gsum z1 z2 h1 h2‖
        ≤ 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
            * (Work.FIArea2.gcdDelta z1 z2 h1 h2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) :=
      fun h1 h2 => Work.FIArea2.Gsum_bound z1 z2 hcop hp1 hp2
        (Work.FIArea2.absDelta_ne_zero_of_Delta_ne_zero hΔ) h1 h2
    have h71 : ∀ u₁ u₂ : ℝ, ‖Work.FIArea2.Fint F γ u₁ u₂‖ ≤ 10 ^ 13 * Cder
        * (1 + u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)) :=
      fun u₁ u₂ => lemma_7_1_gen_clean Pa.M hM A B Cder hA0 hAB hB hCder1 F γ hγ0' hγ1 hF hfsupp hfd u₁ u₂
    have hsumm := sec9_frequency_summable_gen Pa F z1 z2 γ (10 ^ 13) Cder
      (by norm_num) hCder0 hM hγ0' hγ1 hΔ hG h71
    have htail := sec9_frequency_sum_bound_gen Pa F z1 z2 γ (10 ^ 13) Cder
      (by norm_num) hCder0 hM hγ0' hγ1 hΔ hG h71
    have hpoisson : ((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
        = ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
          * ∑' h : ℤ × ℤ, Work.FIArea2.Fint F γ
              (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
              (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))))
            * Work.FIArea2.Gsum z1 z2 h.1 h.2 := by
      rw [show ((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
          = ((∑ w ∈ Work.FITop.boxM Pa, F (Work.FIPlan.gnorm w)
            * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re : ℝ) : ℂ) from rfl]
      exact Work.FIArea2.Ccount_smooth_eq_poisson Pa F z1 z2 hF hcs hΔ hbox
    have hTsum : (∑' h : ℤ × ℤ, Work.FIArea2.Fint F γ
              (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
              (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))))
            * Work.FIArea2.Gsum z1 z2 h.1 h.2)
        = (∑' h : ℤ × ℤ, Work.FIArea2.Fint F γ
              (-(Work.FIArea2.secFreq₁ z1 z2 h.1)) (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
            * Work.FIArea2.Gsum z1 z2 h.1 h.2) := by
      apply tsum_congr
      intro h
      simp only [Work.FIArea2.secFreq₁, Work.FIArea2.secFreq₂, neg_div]
    have hc : 0 ≤ ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsplit0 := Work.FIArea2.tsum_sub_single (fun h : ℤ × ℤ => Work.FIArea2.Fint F γ
          (-(Work.FIArea2.secFreq₁ z1 z2 h.1)) (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
          * Work.FIArea2.Gsum z1 z2 h.1 h.2) hsumm (0, 0)
    have hsplit : (∑' h : ℤ × ℤ, Work.FIArea2.Fint F γ
            (-(Work.FIArea2.secFreq₁ z1 z2 h.1)) (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
            * Work.FIArea2.Gsum z1 z2 h.1 h.2)
          - (Work.FIArea2.Fint F γ 0 0 * Work.FIArea2.Gsum z1 z2 0 0)
        = ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
            Work.FIArea2.Fint F γ
              (-(Work.FIArea2.secFreq₁ z1 z2 h.1)) (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
            * Work.FIArea2.Gsum z1 z2 h.1 h.2) := by
      simpa [Work.FIArea2.secFreq₁, Work.FIArea2.secFreq₂] using hsplit0
    have hnorm : ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖
        = ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) := by
      rw [show ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖
          = |(((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))| from by simp]
      exact abs_of_nonneg hc
    have hHaver : HaverG Pa γ z1 z2 = Work.FIArea2.Haver Pa z1 z2 := by
      rw [hγdef]; exact HaverG_gamOf Pa z1 z2
    calc ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
          - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
              * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                  * Work.FIArea2.Gsum z1 z2 0 0)‖
        = ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
            * (∑' h : ℤ × ℤ, Work.FIArea2.Fint F γ
                (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
                (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))))
              * Work.FIArea2.Gsum z1 z2 h.1 h.2)
            - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
                * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                    * Work.FIArea2.Gsum z1 z2 0 0)‖ := by rw [hpoisson]
      _ = ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
            * ((∑' h : ℤ × ℤ, Work.FIArea2.Fint F γ
                (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
                (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))))
              * Work.FIArea2.Gsum z1 z2 h.1 h.2)
            - (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                * Work.FIArea2.Gsum z1 z2 0 0))‖ := by rw [mul_sub]
      _ = ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖
            * ‖(∑' h : ℤ × ℤ, Work.FIArea2.Fint F γ
                (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
                (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))))
              * Work.FIArea2.Gsum z1 z2 h.1 h.2)
            - (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                * Work.FIArea2.Gsum z1 z2 0 0)‖ := by rw [norm_mul]
      _ = ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)
            * ‖∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
                Work.FIArea2.Fint F γ
                  (-(Work.FIArea2.secFreq₁ z1 z2 h.1)) (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
                * Work.FIArea2.Gsum z1 z2 h.1 h.2)‖ := by
          rw [hnorm, hTsum, hsplit]
      _ ≤ (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
            * (10 ^ 13 * Cder * 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
                * Real.log (2 + 1 / (1 - γ ^ 2))
                * HaverG Pa γ z1 z2) :=
          mul_le_mul_of_nonneg_left htail hc
      _ = 4 * 10 ^ 13 * Cder * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
            * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
                * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
                * Work.FIArea2.Haver Pa z1 z2) := by
          rw [hHaver]; ring
  · have hF0 : ∀ u : ℝ, F u = 0 := fun u => by
      by_contra h
      exact hAB (le_trans (hfsupp u h).1 (hfsupp u h).2)
    have hC : Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 = 0 := by
      unfold Work.FIArea2.Ccount
      refine Finset.sum_eq_zero fun w _ => ?_
      simp [hF0]
    have hFi : Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0 = 0 := by
      rw [Work.FIArea2.Fint]
      simp [hF0, integral_zero]
    have hLHS : ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
          - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
              * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                  * Work.FIArea2.Gsum z1 z2 0 0)‖ = 0 := by
      rw [hC, hFi]
      simp [Complex.ofReal_zero]
    rw [hLHS]
    exact sec9_gen_rhs_nonneg Pa Cder z1 z2 (le_trans zero_le_one hCder1) hγ0
      (Work.FIArea2.gamOf_lt_one_of_Delta_ne_zero hΔ)


theorem sec9_error_pair_clean :
    ∃ K : ℝ, 0 < K ∧ ∀ (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ)
      (z1 z2 : GaussianInt),
      Pa.M / 64 ≤ A → B ≤ 64 * Pa.M → 1 ≤ Cder →
      ContDiff ℝ 4 F → HasCompactSupport F →
      IsCoprime z1 z2 → IsCoprime z1 (star z1) → IsCoprime z2 (star z2) →
      Work.FIPlan.Delta z1 z2 ≠ 0 →
      (∀ w : GaussianInt, F (Work.FIPlan.gnorm w) ≠ 0 → w ∈ Work.FITop.boxM Pa) →
      (∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B) →
      (∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ Cder * Pa.M ^ (-(j : ℝ))) →
      1 ≤ Pa.M → 0 ≤ Work.FIArea2.gamOf z1 z2 →
      ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
          - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
              * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                  * Work.FIArea2.Gsum z1 z2 0 0)‖
        ≤ K * Cder * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
            * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
                * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
                * Work.FIArea2.Haver Pa z1 z2) :=
  ⟨4 * 10 ^ 13, by norm_num, fun Pa A B Cder F z1 z2 hA hB hC hF hcs hcop hp1 hp2 hΔ hbox
      hfsupp hfd hM hγ0 =>
    sec9_error_gen_clean Pa A B Cder F z1 z2 hA hB hC hF hcs hcop hp1 hp2 hΔ hbox hfsupp hfd hM hγ0⟩

/-! ## 3.  `D* − D₀^exact` as the pair sum of (9.1) -/

/-- **The pair sum of (9.1), bounded by `sec9ErrSum6`.**  `|D* − D₀^exact|` is at most the
per-pair (9.1) right-hand side summed over the coprime pairs, i.e. `(4·10^13·Cder6)·sec9ErrSum6`
(no `4·10^6` and no `Cder^4` here: the sharper `K·Cder` form of the general-majorant (9.1) is
used, `Cder = Cder6`). -/
theorem abs_Dstar_sub_D0ex_le_errSum :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ)
      (hf : Work.FITop4.IsMajorant6 Pa f) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      |Work.FITop3.Dstar Pa f β
          - Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β|
        ≤ C * Work.FIArea2.R6.sec9ErrSum6 Pa β := by
  obtain ⟨K, hKpos, hK⟩ := sec9_error_pair_clean
  refine ⟨K * Cder6, mul_pos hKpos Cder6_pos, fun Pa f hf φ z0 β hβ => ?_⟩
  set F : ℝ → ℝ := Work.FIArea2.R6.majF Pa f hf with hFdef
  obtain ⟨hFcd, hFcs, hFeq, hFsupp, hFder⟩ := Work.FIArea2.R6.majF_spec Pa f hf
  have hFint : ∀ n : ℤ, F n = f n := hFeq
  have hmajbox : ∀ w : GaussianInt, F (Work.FIPlan.gnorm w) ≠ 0 → w ∈ Work.FITop.boxM Pa := by
    intro w hw
    have hFF : F ((Work.FIPlan.gnorm w : ℕ) : ℝ) = f ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by
      simpa using hFeq ((Work.FIPlan.gnorm w : ℕ) : ℤ)
    have hfw : f ((Work.FIPlan.gnorm w : ℕ) : ℤ) ≠ 0 := by
      intro h0; exact hw (by rw [hFF, h0])
    obtain ⟨-, hb2⟩ := hf.2.2.2.2 ((Work.FIPlan.gnorm w : ℕ) : ℤ) hfw
    exact mem_boxM_of_gnorm_le Pa (by simpa using hb2)
  have hterm : ∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa,
      (if Work.FIPlan.GaussCoprime z1 z2 then
        ‖β z1‖ * ‖β z2‖ *
          ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
            - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
                * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                    * Work.FIArea2.Gsum z1 z2 0 0)‖
      else 0)
      ≤ (K * Cder6) * (Real.sqrt Pa.M *
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
              * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                  / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
                  * Work.FIArea2.Haver Pa z1 z2)
          else 0)) := by
    intro z1 _ z2 _
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc, if_pos hc]
      by_cases hb1 : β z1 = 0
      · rw [hb1]; norm_num
      by_cases hb2 : β z2 = 0
      · rw [hb2]; norm_num
      have hΔ : Work.FIPlan.Delta z1 z2 ≠ 0 :=
        Work.FIArea2.R6.IsBetaCoeff6.delta_ne_zero6 hβ hc hb1 hb2
      have hγ0 : 0 ≤ Work.FIArea2.gamOf z1 z2 :=
        (Work.FIArea2.R6.IsBetaCoeff6.gamOf_bounds6 hβ hc hb1 hb2).1
      have hA := hK Pa (Pa.M / 64) (64 * Pa.M) Cder6 F z1 z2 (le_refl _) (le_refl _)
        one_le_Cder6 hFcd hFcs hc (Work.FIArea2.R6.IsBetaCoeff6.isCoprime_star6 hβ hb1)
        (Work.FIArea2.R6.IsBetaCoeff6.isCoprime_star6 hβ hb2) hΔ hmajbox hFsupp hFder Pa.hM1 hγ0
      calc ‖β z1‖ * ‖β z2‖ *
            ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
              - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
                  * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                      * Work.FIArea2.Gsum z1 z2 0 0)‖
          ≤ ‖β z1‖ * ‖β z2‖ *
              (K * Cder6 * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
                * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                    / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
                    * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
                    * Work.FIArea2.Haver Pa z1 z2)) :=
            mul_le_mul_of_nonneg_left hA (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = (K * Cder6) * (Real.sqrt Pa.M *
              (‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
                * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                    / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
                    * Work.FIArea2.Haver Pa z1 z2))) := by
            ring
    · rw [if_neg hc, if_neg hc]; simp
  have hmain := abs_Dstar_sub_D0ex_le Pa f F β hFint
  refine le_trans hmain ?_
  calc (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          ‖β z1‖ * ‖β z2‖ *
            ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
              - ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
                  * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                      * Work.FIArea2.Gsum z1 z2 0 0)‖
        else 0))
      ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (K * Cder6) * (Real.sqrt Pa.M *
            (if Work.FIPlan.GaussCoprime z1 z2 then
              ‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
                * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                    / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                    * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
                    * Work.FIArea2.Haver Pa z1 z2)
            else 0)) :=
        Finset.sum_le_sum fun z1 h1 => Finset.sum_le_sum fun z2 h2 => hterm z1 h1 z2 h2
    _ = (K * Cder6) * Work.FIArea2.R6.sec9ErrSum6 Pa β := by
        rw [Work.FIArea2.R6.sec9ErrSum6]
        simp only [Finset.mul_sum]

/-! ## 4.  The target -/

theorem area2_6e_A (hL : Work.FIArea2.R6.LacProp) :
    ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ Cb x0 : ℝ, 0 < Cb ∧ 0 < x0 ∧
      ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
      ∀ (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) (φ : ℝ) (z0 : GaussianInt)
        (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
            - ((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β : ℝ) : ℂ)‖
          ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  obtain ⟨C, hCpos, hC⟩ := abs_Dstar_sub_D0ex_le_errSum
  intro η hη0 hη32
  obtain ⟨Cb, x0, hCbpos, hx0pos, hCb⟩ := Work.FIArea2.R6.sec9ErrSum6_bound hL η hη0 hη32
  refine ⟨C * Cb, x0, by positivity, hx0pos, fun Pa hx hη f hf φ z0 β hβ => ?_⟩
  have h1 : ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
        - ((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β : ℝ) : ℂ)‖
      = |Work.FITop3.Dstar Pa f β
          - Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  calc |Work.FITop3.Dstar Pa f β
          - Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β|
      ≤ C * Work.FIArea2.R6.sec9ErrSum6 Pa β := hC Pa f hf φ z0 β hβ
    _ ≤ C * (Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) :=
        mul_le_mul_of_nonneg_left (hCb Pa hx hη φ z0 β hβ) hCpos.le
    _ = C * Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by ring

end

end Work.FIArea2.R6
