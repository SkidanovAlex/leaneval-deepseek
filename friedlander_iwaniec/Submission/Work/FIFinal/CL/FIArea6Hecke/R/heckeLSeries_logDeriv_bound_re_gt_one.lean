import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivBoundAux
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea6Hecke.R.stripCoreClean
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.logDerivPrincipalCharAlt
import Submission.Work.FIArea6Hecke.R.conductorFECleanNoDep
import Submission.Work.FIArea6Hecke.R.zfrOffAxisSdClean
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.zfrRealAxisSdClean
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- Case B identification: if `ψ` is trivial on the primary units, then `heckeLam χ m = heckeLam (chiTriv d) 0`. -/
private lemma heckeLam_eq_chiTriv (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hB : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea5.S16Hecke.psi chi m z = 1) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam chi m n = Work.FIArea5.S16Hecke.heckeLam (chiTriv d) 0 n := by
  classical
  rw [Work.FIArea5.S16Hecke.heckeLam, Work.FIArea5.S16Hecke.heckeLam]
  refine Finset.sum_congr rfl ?_
  intro z hz
  rw [Finset.mem_filter] at hz
  obtain ⟨-, hzp, -⟩ := hz
  by_cases hunit : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · have hp : Work.FIArea5.S16Hecke.psi chi m z = 1 := hB z hzp hunit
    have hq : Work.FIArea5.S16Hecke.psi (chiTriv d) 0 z = 1 := by
      simp only [Work.FIArea5.S16Hecke.psi, chiTriv]
      rw [if_pos hunit]
      simp
    rw [hp, hq]
  · have hz0 : chi z = 0 := hchi.2 z hunit
    have hp : Work.FIArea5.S16Hecke.psi chi m z = 0 := by
      rw [Work.FIArea5.S16Hecke.psi, hz0]
      simp
    have hq : Work.FIArea5.S16Hecke.psi (chiTriv d) 0 z = 0 := by
      simp only [Work.FIArea5.S16Hecke.psi, chiTriv]
      rw [if_neg hunit]
      simp
    rw [hp, hq]

private lemma heckeLSeries_eq_chiTriv (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hB : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea5.S16Hecke.psi chi m z = 1) :
    Work.FIArea5.S16Hecke.heckeLSeries chi m = Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0 := by
  unfold Work.FIArea5.S16Hecke.heckeLSeries
  refine funext (fun s => ?_)
  exact LSeries_congr (fun {n} _ => heckeLam_eq_chiTriv d chi m hchi hB n) s


/-- ***FI* §16, the logarithmic-derivative bound on the half-plane of absolute convergence.**
For the Hecke `L`-series of `ℚ(i)` attached to the Größencharacter `ψ_m(z) = χ(z)(z/|z|)^m`
(`heckeLSeries chi m = LSeries (heckeLam chi m)`), with `χ` a strict character mod `4d`:

  `Re (L'(s,ψ_m)/L(s,ψ_m)) ≤ K · d · log²(|m| + |s.im| + 3)`  for  `1 < s.re ≤ 2`,

uniformly in `d ≥ 1`, in the strict character `χ` mod `4d`, in the weight `m : ℤ` and in the
point `s`; the constant `K = K(ε)` may depend on `ε` only.

This is the classical input that *FI* (16.23) is obtained from: bound `Re(L'/L)` in the region
(16.24), integrate it along the horizontal segment towards `σ = 1 + c/(d^ε log(…))`, and
exponentiate (the integration is carried out in
`Submission/Work/FIArea6Hecke/R/heckeLSeries_inv_bound_re_gt_one.lean`, which turns this statement
into the inverse bound `‖L(s,ψ)⁻¹‖ ≤ c·d·log²(|m|+|s.im|+3)`).

## The proof in this file

Write `L := heckeLSeries χ m` and put `M := |m| + |s.im| + 3 ≥ 3`.

* **The generic case** — `ψ_m` is *not* trivial on the primary units mod `4d`.  Then `ψ_m` is a
  nontrivial Größencharacter, the completed function `Λ(s) = heckeArch d m s · L(s)` is entire
  (`R/heckeCompletionStrict`: the imprimitive `χ` is handled by factoring out the finite part, the
  trivial character being the only case without an entire completion), and the strip
  logarithmic-derivative bound `R/heckeStripLogDeriv` applies — its region
  `1 - c/(d^ε·log M) ≤ σ ≤ 2` contains the target region `1 < σ ≤ 2`.  The identity theorem
  (`R/heckeStripNearOne.Lam_eq_heckeArch_mul_of_one_lt_re`) identifies `Lval d m Lam` with `L` on
  `σ > 1`, hence also the logarithmic derivatives at `s`; taking real parts of the norm bound gives
  `Re (L'/L)(s) ≤ K (log(4dM) + d^ε)`.
* **The exceptional case** — `ψ_m ≡ 1` on the primary units mod `4d` (so that
  `L(s) = ∏_{𝔭 ∤ 4d}(1 - N𝔭^{-s})^{-1} = ζ_K(s)·∏_{𝔭 | 4d}(1 - N𝔭^{-s})`).  Then `heckeLam χ m`
  agrees with `heckeLam (chiTriv d) 0` (`heckeLam_eq_chiTriv`: the hypothesis evaluates to `1` on
  the primary units and strictness kills the remaining primaries), so `L` is the `L`-series of the
  trivial strict character; its completed function has a *pole* at `s = 1` and there is no entire
  completion, so the strip bound is vacuous and the case is covered by the companion
  `R/heckeStripLogDeriv_trivialChar` (proved from the zero-free region of `ζ` and `L(·, χ₄)`).

Each bound is finally dominated by `C·d·(log M)²` through the arithmetic comparison
`log (4dM) + d^ε ≤ 6·d·(log M)²` proved in `R/logDerivBoundAux.log_four_d_mul_add_rpow_le`
(using `log (4d) ≤ 4d`, `log M ≤ (log M)²` as `log M ≥ 1`, and `d^ε ≤ d`). -/
theorem heckeLSeries_logDeriv_bound_re_gt_one : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ (m : ℤ) (s : ℂ),
        1 < s.re → s.re ≤ 2 →
        (deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s /
          Work.FIArea5.S16Hecke.heckeLSeries chi m s).re
          ≤ K * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
  intro ε hε hε4
  obtain ⟨c, K, hc, hK, hstrip⟩ := heckeStripLogDerivOfInputs ε hε hε4
    (logDerivReLower_of_conductorFESd ε hε hε4 Work.FIArea6Hecke.RC.conductorFECleanNoDep zfrOffAxisSdClean
      (zfrRealAxisSdClean ε hε hε4))
    zfrOffAxisSdClean (zfrRealAxisSdClean ε hε hε4)
  obtain ⟨Kp, hKp, hp⟩ := heckeLSeries_logDeriv_principalCharAux
  obtain ⟨Ca, hCa, hCa1, harith⟩ := log_four_d_mul_add_rpow_le ε (le_of_lt hε) (by linarith)
  refine ⟨max (K * Ca) (Kp * Ca), lt_max_of_lt_left (mul_pos hK hCa), ?_⟩
  intro d chi hd hchi m s hs1 hs2
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hM3 : (3 : ℝ) ≤ |(m : ℝ)| + |s.im| + 3 := by
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im; linarith
  have harith' := harith d (|(m : ℝ)| + |s.im| + 3) hd hM3
  by_cases hB : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea5.S16Hecke.psi chi m z = 1
  · -- Case B: `ψ_m` is trivial on the primary units, so `L` is the principal character's
    have hL := heckeLSeries_eq_chiTriv d chi m hchi hB
    have hb := hp d hd s hs1 hs2
    have hL' : deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s /
          Work.FIArea5.S16Hecke.heckeLSeries chi m s
        = deriv (Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0) s /
          Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0 s := by rw [hL]
    rw [hL']
    have hlogmono2 : (Real.log (|s.im| + 3)) ^ (2 : ℕ)
        ≤ (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
      have h0 : 0 ≤ Real.log (|s.im| + 3) :=
        Real.log_nonneg (by have h := abs_nonneg s.im; linarith)
      have h1 : Real.log (|s.im| + 3) ≤ Real.log (|(m : ℝ)| + |s.im| + 3) :=
        Real.log_le_log (by have h := abs_nonneg s.im; linarith)
          (by have h := abs_nonneg (m : ℝ); linarith)
      have h2 : (1 : ℝ) ≤ |(m : ℝ)| + |s.im| + 3 := by
        have h := abs_nonneg (m : ℝ); have h3 := abs_nonneg s.im; linarith
      nlinarith [h0, h1, Real.log_nonneg h2]
    calc (deriv (Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0) s /
          Work.FIArea5.S16Hecke.heckeLSeries (chiTriv d) 0 s).re
        ≤ Kp * (d : ℝ) * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := hb
      _ ≤ Kp * (Ca * (d : ℝ) * (Real.log (|s.im| + 3)) ^ (2 : ℕ)) := by
          have h2 : (0 : ℝ) ≤ (d : ℝ) * (Real.log (|s.im| + 3)) ^ (2 : ℕ) := by positivity
          have h3 := mul_le_mul_of_nonneg_left hCa1 (le_of_lt hKp)
          nlinarith [h2, h3, mul_le_mul_of_nonneg_right h3 h2]
      _ ≤ Kp * (Ca * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hKp)
          exact mul_le_mul_of_nonneg_left hlogmono2 (by positivity)
      _ ≤ max (K * Ca) (Kp * Ca) * (d : ℝ)
            * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
          have h1 : Kp * Ca ≤ max (K * Ca) (Kp * Ca) := le_max_right _ _
          have h2 : 0 ≤ (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by positivity
          nlinarith [h1, h2, mul_le_mul_of_nonneg_right h1 h2]
  · -- Case A
    push Not at hB
    obtain ⟨z0, hz0p, hz0u, hz0ne⟩ := hB
    obtain ⟨Lam, hAn, hagr⟩ := heckeCompletionImprimitive d chi m hd hchi ⟨z0, hz0p, hz0u, hz0ne⟩
    obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
    have hLval : ∀ w : ℂ, 1 < w.re → Lval d m Lam w = Work.FIArea5.S16Hecke.heckeLSeries chi m w := by
      intro w hw
      rw [Lval, Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hw]
      exact mul_div_cancel_left₀ _ (heckeArch_ne_zero_of_one_lt_re hd m hw)
    have hderiv : deriv (Lval d m Lam) s = deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with w hw
      exact hLval w hw
    have hDpos : 0 < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by
      have h1 : (0 : ℝ) < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hdpos ε
      have h2 : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) :=
        Real.log_pos (by have h := abs_nonneg (m : ℝ); linarith)
      exact mul_pos h1 h2
    have hreg : 1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re := by
      have h3 : 0 < c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) := div_pos hc hDpos
      linarith
    have hsb := hstrip d chi m Lam hd hchi hAn hagr s hreg hs2
    have hconv : (deriv (Lval d m Lam) s / Lval d m Lam s).re
        = (deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s /
            Work.FIArea5.S16Hecke.heckeLSeries chi m s).re := by
      rw [hderiv, hLval s hs1]
    calc (deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s /
          Work.FIArea5.S16Hecke.heckeLSeries chi m s).re
        = (deriv (Lval d m Lam) s / Lval d m Lam s).re := hconv.symm
      _ ≤ ‖deriv (Lval d m Lam) s / Lval d m Lam s‖ := Complex.re_le_norm _
      _ ≤ K * (Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) + (d : ℝ) ^ ε) := hsb
      _ ≤ K * (Ca * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2:ℕ)) := by
          exact mul_le_mul_of_nonneg_left harith' (le_of_lt hK)
      _ ≤ max (K * Ca) (Kp * Ca) * (d : ℝ)
            * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2:ℕ) := by
          have h1 : K * Ca ≤ max (K * Ca) (Kp * Ca) := le_max_left _ _
          have h2 : 0 ≤ (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2:ℕ) := by positivity
          nlinarith [h1, h2, mul_le_mul_of_nonneg_right h1 h2]
end

end Work.FIArea6Hecke.R
