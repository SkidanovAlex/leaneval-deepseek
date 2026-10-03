import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivBoundAux
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Work.FIArea6Hecke.R.badPolyAlt
import Submission.Work.FIArea6Hecke.R.heckeLam_chiTriv_localFactor_coprime
import Submission.Work.FIArea6Hecke.R.heckeLam_chiTriv_localFactor_dvd
import Submission.Work.FIArea6Hecke.R.heckeLSeries_chiTriv_eq_decomp
import Submission.Work.FIArea6Hecke.R.zeta_logDeriv_re_le_logsq
import Submission.Work.FIArea6Hecke.R.chi4_LSeries_logDeriv_re_le_logsq
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_polyGrowth
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Port.LogDerivCompat

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

/-!
# `Work.FIArea6Hecke.R.logDerivPrincipalCharAlt`

A **self-contained variant of `R/heckeLSeries_logDeriv_principalChar`**: the logarithmic-derivative
bound `Re (L'/L)(s) <= K*d*log^2(|im s|+3)` for the `L`-series of the *principal* strict character
`chiTriv d` on `1 < re s <= 2`.

The reason this file exists is that the original chain reaches
`R/zeta_logDeriv_re_le_logsq`, whose small-height input `R/zeta_logDeriv_re_smallIm_bound` is a
placeholder stub.  Here

* the small-height bound `Re (zeta'/zeta)(sigma+it) <= B` for `1 < sigma <= 2`, `|t| <= 60` is
  **proved** from the polynomial growth of `zeta1'/zeta1`
  (`Commons.NumberTheory.Zeta.zeta1_logDeriv_polyGrowth`) via
  `zeta'/zeta = zeta1'/zeta1 - (s-1)^-1`, whose second term has real part `<= 0` on `re s >= 1`;
* the large-height bound is the *already proved* `zeta_logDeriv_norm_le_logsq_largeIm` (only
  that theorem is used, not the placeholder-carrying combination in the same module);
* the resulting `Re (zeta'/zeta) <= C log^2` is fed into the factorization argument
  `L(s) = zeta(s)*L(s,chi4)*G_d(s)` exactly as in `R/heckeLSeries_logDeriv_principalChar`.
-/

/-- **Small-height bound for `Re (zeta'/zeta)`.**  For `1 < sigma <= 2` and `|t| <= 60` the function
`zeta'/zeta` is bounded above by a constant: `zeta'/zeta(s) = zeta1'/zeta1(s) - (s-1)^-1` with
`Re (s-1)^-1 = (sigma-1)/|s-1|^2 >= 0`, and `zeta1'/zeta1` grows only polynomially on `re s >= 1`. -/
theorem zetaLogDerivReSmallImBound :
    ∃ B : ℝ, ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → |t| ≤ 60 →
      (deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤ B := by
  obtain ⟨C, hC, hb⟩ := Commons.NumberTheory.Zeta.zeta1_logDeriv_polyGrowth
  refine ⟨C * 63 ^ (4 : ℕ), fun σ t hσ1 hσ2 ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    rw [hsre] at h'
    simp at h'
    linarith
  have hnorm : ‖s‖ ≤ 62 := by
    have h1 : ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := by
      rw [hs]; exact norm_add_le _ _
    have h2 : ‖(σ : ℂ)‖ = σ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h3 : ‖(t : ℂ) * Complex.I‖ = |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h2, h3] at h1
    linarith
  have hζne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (le_of_lt (by rw [hsre]; exact hσ1))
  have h1eq : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    have h := riemannZeta_eq_inv_sub_mul (s := s) hs1
    rw [h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  have h1ne : riemannZeta₁ s ≠ 0 := by
    rw [h1eq]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hζne
  have hident : deriv riemannZeta s / riemannZeta s
      = deriv riemannZeta₁ s / riemannZeta₁ s - (s - 1)⁻¹ := by
    rw [riemannZeta_eq_inv_sub_mul (s := s) hs1,
      deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add (s := s) hs1]
    field_simp
    ring
  rw [hident, Complex.sub_re]
  have hpos : 0 ≤ ((s - 1)⁻¹).re := by
    have hre1 : (s - 1).re = σ - 1 := by simp [hs]
    have hpos1 : 0 < (s - 1).re := by rw [hre1]; linarith
    have h1 : ((s - 1)⁻¹).re = (s - 1).re / Complex.normSq (s - 1) := Complex.inv_re _
    rw [h1]
    have h2 : 0 < Complex.normSq (s - 1) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hs1)
    exact div_nonneg hpos1.le h2.le
  have hb' := hb s (by rw [hsre]; exact le_of_lt hσ1)
  have hpow : (1 + ‖s‖) ^ (4 : ℕ) ≤ 63 ^ (4 : ℕ) := by
    have h0 : (0 : ℝ) ≤ 1 + ‖s‖ := by positivity
    have h1 : 1 + ‖s‖ ≤ 63 := by linarith
    exact pow_le_pow_left₀ h0 h1 4
  calc (deriv riemannZeta₁ s / riemannZeta₁ s).re - ((s - 1)⁻¹).re
      ≤ (deriv riemannZeta₁ s / riemannZeta₁ s).re := by linarith
    _ ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ := Complex.re_le_norm _
    _ ≤ C * (1 + ‖s‖) ^ (4 : ℕ) := hb'
    _ ≤ C * 63 ^ (4 : ℕ) := mul_le_mul_of_nonneg_left hpow hC.le

/-- **The uniform bound `Re (zeta'/zeta) <= C log^2` on the strip `1 < re s <= 2`.**  Combination of
the proved large-height norm bound `zeta_logDeriv_norm_le_logsq_largeIm` with
`zetaLogDerivReSmallImBound`. -/
theorem zetaLogDerivReLeLogsq :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
      (deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re
        ≤ C * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
  obtain ⟨Cl, hCl0, hlarge⟩ := zeta_logDeriv_norm_le_logsq_largeIm
  obtain ⟨B, hsmall⟩ := zetaLogDerivReSmallImBound
  refine ⟨max Cl B + 1, by positivity, ?_⟩
  intro σ t hσ1 hσ2
  have hlog1 : (1 : ℝ) ≤ Real.log (|t| + 3) := by
    have hx : Real.exp 1 ≤ |t| + 3 := by
      have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (|t| + 3) := Real.log_le_log (Real.exp_pos 1) hx
  have hsq1 : (1 : ℝ) ≤ (Real.log (|t| + 3)) ^ (2 : ℕ) := one_le_pow₀ hlog1
  have hCpos : 0 < max Cl B + 1 := by positivity
  have hCle : max Cl B + 1 ≤ (max Cl B + 1) * (Real.log (|t| + 3)) ^ (2 : ℕ) :=
    le_mul_of_one_le_right (le_of_lt hCpos) hsq1
  by_cases ht : 60 ≤ |t|
  · have h := hlarge σ t hσ1 hσ2 ht
    have h2 : (deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re
        ≤ ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))‖ := Complex.re_le_norm _
    have h3 : Cl ≤ max Cl B + 1 := by
      have := le_max_left Cl B; linarith
    calc (deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re
        ≤ ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))‖ := h2
      _ ≤ Cl * (Real.log (|t| + 3)) ^ (2 : ℕ) := h
      _ ≤ (max Cl B + 1) * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
          apply mul_le_mul_of_nonneg_right h3 (by positivity)
  · have ht' : |t| ≤ 60 := le_of_lt (lt_of_not_ge ht)
    have h := hsmall σ t hσ1 hσ2 ht'
    have h3 : B ≤ max Cl B + 1 := by
      have := le_max_right Cl B; linarith
    calc (deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re
        ≤ B := h
      _ ≤ max Cl B + 1 := h3
      _ ≤ (max Cl B + 1) * (Real.log (|t| + 3)) ^ (2 : ℕ) := hCle

/-- **The logarithmic-derivative bound for the principal (trivial) strict character modulo `4d`.**

For the Hecke `L`-series of weight `0` attached to `chiTriv d` (`1` on the units of
`Z[i]/(4d)`, `0` off them),

  `Re (L'(s)/L(s)) <= K * d * log^2(|im s| + 3)`  for  `1 < re s <= 2`,

uniformly in `d >= 1`.  Same proof as `R/heckeLSeries_logDeriv_principalChar`, but resting on the
axiom-clean `zetaLogDerivReLeLogsq` above instead of `R/zeta_logDeriv_re_le_logsq`. -/
theorem heckeLSeries_logDeriv_principalCharAux : ∃ K : ℝ, 0 < K ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      (deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.R.chiTriv d) 0) s /
        Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.R.chiTriv d) 0 s).re
        ≤ K * (d : ℝ) * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := by
  obtain ⟨C1, hC1, hZ⟩ := zetaLogDerivReLeLogsq
  obtain ⟨C2, hC2, hL4⟩ := chi4_LSeries_logDeriv_re_le_logsq
  refine ⟨C1 + C2 + (2 * Real.log 4 + 2), by positivity, ?_⟩
  intro d hd s hs1 hs2
  have hloc : ∀ (p : ℕ), p.Prime → ∀ s : ℂ, 1 < s.re →
      (∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 (p ^ e)
          * (((p : ℂ) ^ (-s)) ^ e))
        = (if p ∣ 4 * d then 1 else
            ((1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.chi4fun p * (p : ℂ) ^ (-s)))⁻¹) := by
    intro p hp s' hs'
    by_cases hpd : p ∣ 4 * d
    · rw [if_pos hpd]; exact heckeLam_chiTriv_localFactor_dvd hd hp hpd s' hs'
    · rw [if_neg hpd]; exact heckeLam_chiTriv_localFactor_coprime hd hp hpd s' hs'
  have hdec := heckeLSeries_chiTriv_eq_decomp hd hloc
  set F : ℂ → ℂ := fun w => riemannZeta w * LSeries chi4fun w * badPoly d w with hF
  have hEq : Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0 =ᶠ[𝓝 s] F := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs1] with w hw
    rw [hF]; exact hdec w hw
  have hder : deriv (Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0) s = deriv F s := hEq.deriv_eq
  have hval : Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0 s = F s := hEq.self_of_nhds
  have hMnn : 0 ≤ Real.log (|s.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hM2 : (0 : ℝ) ≤ (Real.log (|s.im| + 3)) ^ (2 : ℕ) := pow_nonneg hMnn 2
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [hder, hval]
  by_cases hL4z : LSeries chi4fun s = 0
  · have hFs : F s = 0 := by
      show riemannZeta s * LSeries chi4fun s * badPoly d s = 0
      rw [hL4z]; ring
    rw [hFs, div_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg d)) hM2
  · have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs1)
    have hGne : badPoly d s ≠ 0 := badPoly_ne_zeroAlt hd hs1
    have hζd : DifferentiableAt ℂ riemannZeta s :=
      differentiableAt_riemannZeta (by rintro rfl; simp at hs1)
    have hL4d : DifferentiableAt ℂ (LSeries chi4fun) s := LSeries_chi4fun_differentiableAtAlt hs1
    have hGd : DifferentiableAt ℂ (badPoly d) s := differentiableAt_badPolyAlt d s
    have hlog1 : logDeriv (fun w : ℂ => riemannZeta w * LSeries chi4fun w * badPoly d w) s
        = logDeriv (fun w : ℂ => riemannZeta w * LSeries chi4fun w) s + logDeriv (badPoly d) s :=
      Submission.Port.logDeriv_mul_fun (f := fun w : ℂ => riemannZeta w * LSeries chi4fun w) (g := badPoly d) s
        (mul_ne_zero hζne hL4z) hGne (hζd.mul hL4d) hGd
    have hlog2 : logDeriv (fun w : ℂ => riemannZeta w * LSeries chi4fun w) s
        = logDeriv riemannZeta s + logDeriv (LSeries chi4fun) s :=
      Submission.Port.logDeriv_mul_fun (f := riemannZeta) (g := fun w : ℂ => LSeries chi4fun w) s
        hζne hL4z hζd hL4d
    have hlog : deriv F s / F s
        = logDeriv riemannZeta s + logDeriv (LSeries chi4fun) s + logDeriv (badPoly d) s := by
      rw [hF]
      rw [show deriv (fun w => riemannZeta w * LSeries chi4fun w * badPoly d w) s
            / (riemannZeta s * LSeries chi4fun s * badPoly d s)
            = logDeriv (fun w => riemannZeta w * LSeries chi4fun w * badPoly d w) s from rfl]
      rw [hlog1, hlog2]
    rw [hlog, Complex.add_re, Complex.add_re]
    have hb1 : (logDeriv riemannZeta s).re ≤ C1 * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := by
      have := hZ s.re s.im hs1 hs2
      rwa [Complex.re_add_im] at this
    have hb2 : (logDeriv (LSeries chi4fun) s).re ≤ C2 * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := by
      have := hL4 s.re s.im hs1 hs2
      rwa [Complex.re_add_im] at this
    have hb3 : (logDeriv (badPoly d) s).re ≤ 2 * Real.log (4 * d) := badPoly_logDeriv_re_leAlt hd hs1
    have harith := two_log_four_mul_d_leAlt hd (t := s.im)
    have step : C1 * (Real.log (|s.im| + 3)) ^ (2 : ℕ) + C2 * (Real.log (|s.im| + 3)) ^ (2 : ℕ)
        ≤ (C1 + C2) * (d : ℝ) * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := by
      have hsum : C1 + C2 ≤ (C1 + C2) * (d : ℝ) := by nlinarith [hC1.le, hC2.le, hd1]
      calc C1 * (Real.log (|s.im| + 3)) ^ (2 : ℕ) + C2 * (Real.log (|s.im| + 3)) ^ (2 : ℕ)
          = (C1 + C2) * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := by ring
        _ ≤ ((C1 + C2) * (d : ℝ)) * (Real.log (|s.im| + 3)) ^ (2 : ℕ) :=
              mul_le_mul_of_nonneg_right hsum hM2
        _ = (C1 + C2) * (d : ℝ) * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := by ring
    linarith [hb1, hb2, hb3, harith, step]

end

end Work.FIArea6Hecke.R
