import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound

namespace Work.LinnikAreas.OtherCharRepel

open Complex Filter
open scoped Topology

/-!
# `zetaLogDerivRegularSharp`

Uniform upper bound for the real part of `−ζ′/ζ` in the strip `1 < σ ≤ 5/4`:

    Re(−ζ′/ζ)(σ + i t) ≤ (σ−1)/((σ−1)² + t²) + (1/2)·log(2 + |t|) + C.

The proof splits at a height `H ≥ 2` (supplied by the classical "regular" bound
`Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound`, itself reduced to the
Hadamard partial fraction of the completed zeta):

* for `|t| ≥ H` the regular bound gives `Re(−ζ′/ζ)(σ+it) ≤ C + (1/2)·Re ψ(1 + s/2)`,
  and the digamma estimate `digamma_vertical_bound` bounds the last term by
  `(1/2)·log(2+|t|) + O(1)`;
* for `|t| ≤ H` we use the completion `ζ₁ = (s−1)ζ`, which is entire and zero-free on
  `Re s ≥ 1`; there `Re(−ζ′/ζ)(σ+it) − (σ−1)/((σ−1)²+t²) = −Re(ζ₁′/ζ₁)(σ+it)` is bounded
  on the compact rectangle `[1, 5/4] × [−H, H]`.
-/

/-- The logarithmic derivative of the completion `ζ₁ = (s−1)·ζ` differs from that of `ζ`
by the explicit pole term: for `s ≠ 1` with `ζ s ≠ 0`,

    ζ₁′/ζ₁(s) = ζ′/ζ(s) + 1/(s − 1). -/
lemma logDeriv_riemannZeta₁_eq (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
  have hEq : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hzne
    have hz := riemannZeta_eq_inv_sub_mul hzne
    calc
      riemannZeta₁ z = (z - 1) * ((z - 1)⁻¹ * riemannZeta₁ z) := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hzne), one_mul]
      _ = (z - 1) * riemannZeta z := by rw [hz]
  have hval : logDeriv riemannZeta₁ s = logDeriv (fun z => (z - 1) * riemannZeta z) s :=
    (logDeriv_congr_nhds hEq).self_of_nhds
  rw [hval]
  have hmul := logDeriv_mul (x := s) (f := fun z => z - 1) (g := riemannZeta)
      (sub_ne_zero.mpr hs1) hζs (by fun_prop) (differentiableAt_riemannZeta hs1)
  erw [hmul]
  have hld_id : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ => z - 1) s = 1 := by simp
    rw [hd]
  rw [hld_id, logDeriv_apply]
  ring

/-- Real-part identity for the "regular part": for `σ > 1`,

    Re(−ζ′/ζ)(σ+it) = (σ−1)/((σ−1)²+t²) − Re(ζ₁′/ζ₁)(σ+it). -/
lemma re_deriv_div_riemannZeta (σ t : ℝ) (hσ : 1 < σ) :
    (-deriv riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) /
        riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))).re =
      (σ - 1) / ((σ - 1) ^ 2 + t ^ 2)
        - (logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))).re := by
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ) with hs
  have hsre : s.re = σ := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h]; simp
    rw [hsre] at hre
    linarith
  have hζs : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; linarith)
  have hid := logDeriv_riemannZeta₁_eq s hs1 hζs
  have h1 : (-deriv riemannZeta s / riemannZeta s).re =
      -(deriv riemannZeta s / riemannZeta s).re := by
    rw [neg_div]; simp
  rw [h1]
  have h2 : -(deriv riemannZeta s / riemannZeta s).re =
      (1 / (s - 1)).re - (logDeriv riemannZeta₁ s).re := by
    have h := congrArg Complex.re hid
    rw [Complex.add_re] at h
    linarith
  rw [h2]
  have h3 : (1 / (s - 1)).re = (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    have hsub : s - 1 = (((σ - 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [hsub, Complex.div_re]
    simp [Complex.normSq]
    ring
  rw [h3]

/-- The digamma contribution is bounded by `(1/2)·log(2+|t|) + 4`. -/
lemma digamma_half_bound (σ t : ℝ) (hσ1 : 1 < σ) (hσ54 : σ ≤ 5 / 4) :
    (1 / 2) * (Complex.digamma (1 + (((σ : ℂ) + Complex.I * (t : ℂ)) / 2))).re
      ≤ (1 / 2) * Real.log (2 + |t|) + 4 := by
  have hx1 : (1 : ℝ) / 4 ≤ 1 + σ / 2 := by linarith
  have hx2 : 1 + σ / 2 ≤ 8 := by linarith
  have hdig :=
    Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound (1 + σ / 2) (t / 2) hx1 hx2
  have harg : 1 + (((σ : ℂ) + Complex.I * (t : ℂ)) / 2)
      = (((1 + σ / 2 : ℝ)) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  have hre : (Complex.digamma ((((1 + σ / 2 : ℝ)) : ℂ)
        + ((t / 2 : ℝ) : ℂ) * Complex.I)).re
      ≤ Real.log (2 + |t|) + 8 := by
    calc
      (Complex.digamma ((((1 + σ / 2 : ℝ)) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)).re
          ≤ ‖Complex.digamma ((((1 + σ / 2 : ℝ)) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)‖ :=
            Complex.re_le_norm _
      _ ≤ Real.log (2 + |t / 2|) + 8 := hdig
      _ ≤ Real.log (2 + |t|) + 8 := by
        have h2 : |t / 2| ≤ |t| := by
          have hpos : (0 : ℝ) ≤ |t| := abs_nonneg t
          calc |t / 2| = |t| / 2 := by rw [abs_div]; simp
            _ ≤ |t| := by linarith
        have h3 : Real.log (2 + |t / 2|) ≤ Real.log (2 + |t|) :=
          Real.log_le_log (by positivity) (by linarith)
        linarith
  linarith

/-- Compactness bound: on the rectangle `1 ≤ σ ≤ 5/4`, `|t| ≤ H`, the real part of
`ζ₁′/ζ₁(σ+it)` is bounded above. -/
lemma logDeriv_riemannZeta₁_compact_re_le (H : ℝ) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 5 / 4 → |t| ≤ H →
      -(logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤ C := by
  let F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)
  have hFcont : Continuous F := by fun_prop
  let P : Set (ℝ × ℝ) := Set.prod (Set.Icc (1 : ℝ) (5 / 4)) (Set.Icc (-H) H)
  have hPcompact : IsCompact P := isCompact_Icc.prod isCompact_Icc
  have hne : ∀ p ∈ P, riemannZeta₁ (F p) ≠ 0 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p.1 := hp.1.1
    have hre : (F p).re = p.1 := by simp [F]
    have hle : (1 : ℝ) ≤ (F p).re := by rw [hre]; exact hp1
    by_cases h1 : F p = 1
    · rw [h1, riemannZeta₁_one]; exact one_ne_zero
    · have hz : riemannZeta (F p) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hle
      have hmul : riemannZeta₁ (F p) = (F p - 1) * riemannZeta (F p) := by
        have h := riemannZeta_eq_inv_sub_mul h1
        rw [h]
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h1), one_mul]
      rw [hmul]
      exact mul_ne_zero (sub_ne_zero.mpr h1) hz
  have hcont : ContinuousOn (fun p : ℝ × ℝ => logDeriv riemannZeta₁ (F p)) P := by
    have hnum : ContinuousOn (fun p : ℝ × ℝ => deriv riemannZeta₁ (F p)) P :=
      (differentiable_riemannZeta₁.deriv.continuous.comp hFcont).continuousOn
    have hden : ContinuousOn (fun p : ℝ × ℝ => riemannZeta₁ (F p)) P :=
      (differentiable_riemannZeta₁.continuous.comp hFcont).continuousOn
    have hdiv : ContinuousOn (fun p : ℝ × ℝ => deriv riemannZeta₁ (F p) / riemannZeta₁ (F p)) P :=
      hnum.div hden (fun p hp => hne p hp)
    simpa only [logDeriv_apply] using hdiv
  obtain ⟨C, hC⟩ := hPcompact.exists_bound_of_continuousOn hcont
  refine ⟨C, ?_⟩
  intro σ t hσ1 hσ2 ht
  have hp : (σ, t) ∈ P := ⟨⟨hσ1, hσ2⟩, abs_le.mp ht⟩
  have hb := hC (σ, t) hp
  have hval : F (σ, t) = (σ : ℂ) + Complex.I * (t : ℂ) := by simp [F]
  rw [hval] at hb
  calc -(logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))).re
      ≤ ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
        have := Complex.re_le_norm (-(logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))))
        rwa [Complex.neg_re, norm_neg] at this
    _ ≤ C := hb

theorem zetaLogDerivRegularSharp : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 5 / 4 →
    (-deriv riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) /
      riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
      (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) + (1 / 2) * Real.log (2 + |t|) + C := by
  obtain ⟨Creg, hCregpos, H, hH2, hreg⟩ :=
    Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound
  obtain ⟨Csm, hsm⟩ := logDeriv_riemannZeta₁_compact_re_le H
  refine ⟨max (Creg + 4) Csm + 1, by positivity, ?_⟩
  intro σ t hσ1 hσ54
  have hσ2 : σ ≤ 2 := by linarith
  have hlog2 : 0 ≤ (1 / 2) * Real.log (2 + |t|) := by
    have := Real.log_nonneg (by linarith [abs_nonneg t] : (1 : ℝ) ≤ 2 + |t|)
    linarith
  have hfrac : 0 ≤ (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    apply div_nonneg (by linarith); positivity
  by_cases ht : H ≤ |t|
  · have hbound := hreg t ht σ hσ1 hσ2
    have harg : (((σ : ℂ) + (t : ℂ) * Complex.I)) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by ring
    rw [harg] at hbound
    have hdig := digamma_half_bound σ t hσ1 hσ54
    have hC : Creg + 4 ≤ max (Creg + 4) Csm + 1 := by
      have := le_max_left (Creg + 4) Csm; linarith
    linarith
  · rw [not_le] at ht
    have hid := re_deriv_div_riemannZeta σ t hσ1
    have hb := hsm σ t (le_of_lt hσ1) hσ54 (le_of_lt ht)
    have hC : Csm ≤ max (Creg + 4) Csm + 1 := by
      have := le_max_right (Creg + 4) Csm; linarith
    have hreg' : (-deriv riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) /
        riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))).re
        ≤ (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) + Csm := by
      rw [hid]; linarith
    linarith

end Work.LinnikAreas.OtherCharRepel
