import Mathlib
import Submission.Work.GM.Trace.Defs
import Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay

/-!
# GM Lemma 4.3(2) at `ξ = 0`: decay of `ĥ_t(0)`

`ĥ_t(0) = ∫ w(u)² u^{it} du`.  Substituting `u = e^x` turns this into the Fourier transform
of the smooth compactly supported function `F(x) = w(e^x)² e^x` at frequency `-t/(2π)`:

`ĥ_t(0) = 𝓕 F (-t/(2π))`.

Since `F` is `C^∞` with compact support, `Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay`
gives `‖𝓕 F ξ‖ ≤ C_j / |ξ|^j`, and `|ξ| = |t|/(2π)` is comparable to `|t|`.  This yields the
stated bound with a constant independent of `t`.
-/

namespace Work.GM.Trace

open Submission.GM Submission.LargeValues
open MeasureTheory

/-- The function whose Fourier transform is `ĥ_t(0)`: `F(x) = w(e^x)² e^x`. -/
noncomputable def Ffun (x : ℝ) : ℂ := ((w2 (Real.exp x) * Real.exp x : ℝ) : ℂ)

/-- `F` is smooth (composition of the smooth `w²` with `exp`, times `exp`). -/
theorem Ffun_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ffun := by
  unfold Ffun
  exact Complex.ofRealCLM.contDiff.comp ((w2_contDiff.comp Real.contDiff_exp).mul Real.contDiff_exp)

/-- `F` is compactly supported: it vanishes unless `x ∈ [0, log 2]`. -/
theorem Ffun_hasCompactSupport : HasCompactSupport Ffun := by
  refine HasCompactSupport.intro (K := Set.Icc (0 : ℝ) (Real.log 2)) isCompact_Icc
    (fun x hx => ?_)
  have hmem : Real.exp x ∉ Set.Icc (1 : ℝ) 2 := by
    intro h
    rw [Set.mem_Icc] at h
    have hx' : ¬ (0 ≤ x ∧ x ≤ Real.log 2) := hx
    by_cases h0 : (0 : ℝ) ≤ x
    · have h2 : Real.log 2 < x := not_le.mp (fun hle => hx' ⟨h0, hle⟩)
      have hgt : 2 < Real.exp x := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ < Real.exp x := Real.exp_lt_exp.mpr h2
      linarith [h.2]
    · have hneg : x < 0 := lt_of_not_ge h0
      have hlt : Real.exp x < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr hneg
      linarith [h.1]
  rw [Ffun, w2_eq_zero_of_notMem hmem]; simp

/-- Pointwise form of the substitution `u = e^x` in `ĥ_t(0)`. -/
theorem Ffun_mul_exp (t x : ℝ) : Real.exp x • hfun t (Real.exp x)
    = Ffun x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
  rw [hfun_eq_hfunLog, hfunLog, Ffun]
  rw [Complex.real_smul, Real.log_exp, w2, Complex.ofReal_mul]
  ring

/-- The substitution `u = e^x`: `ĥ_t(0)` is the Fourier transform of `F` at frequency
`-t/(2π)`. -/
theorem hhat_eq_fourier (t : ℝ) :
    hhat t 0 = FourierTransform.fourier Ffun (-(t / (2 * Real.pi))) := by
  -- `ĥ_t(0) = ∫ h_t`.
  have hA : hhat t 0 = ∫ v : ℝ, hfun t v := by
    rw [hhat, Real.fourier_eq]
    simp
  -- Restrict to `(1/2, ∞)`, where the support `[1,2]` lives.
  have h1 : (∫ v : ℝ, hfun t v) = ∫ v in Set.Ioi (1/2 : ℝ), hfun t v := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (1/2 : ℝ))
      (f := hfun t) ?_).symm
    intro v hv
    have hv1 : v < 1 := by
      simp only [Set.mem_Ioi, not_lt] at hv
      linarith
    have hmem : v ∉ Set.Icc (1 : ℝ) 2 := by
      intro h; exact absurd h.1 (not_le.mpr hv1)
    rw [hfun, bumpW_eq_zero_of_notMem hmem]; simp
  -- Substitute `u = e^x` on `(1/2, ∞)`.
  have h2 : (∫ v in Set.Ioi (1/2 : ℝ), hfun t v)
      = ∫ x in Set.Ioi (Real.log (1/2)), Real.exp x • hfun t (Real.exp x) := by
    have h := integral_comp_exp_Ioi (hfun t) (Real.log (1/2))
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 1/2)] at h
    exact h.symm
  -- Extend the `x`-integral back to all of `ℝ`: the integrand vanishes for `x ≤ log(1/2)`.
  have h3 : (∫ x in Set.Ioi (Real.log (1/2)), Real.exp x • hfun t (Real.exp x))
      = ∫ x : ℝ, Real.exp x • hfun t (Real.exp x) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (Real.log (1/2)))
      (f := fun x => Real.exp x • hfun t (Real.exp x)) ?_
    intro x hx
    have hx' : x ≤ Real.log (1/2) := by
      simp only [Set.mem_Ioi, not_lt] at hx; exact hx
    have hexp : Real.exp x ≤ (1/2 : ℝ) := by
      calc Real.exp x ≤ Real.exp (Real.log (1/2)) := Real.exp_le_exp.mpr hx'
        _ = 1/2 := Real.exp_log (by norm_num)
    have hmem : Real.exp x ∉ Set.Icc (1 : ℝ) 2 := by
      intro h; linarith [h.1]
    rw [hfun, bumpW_eq_zero_of_notMem hmem]; simp
  -- Rewrite the integrand.
  have h4 : (∫ x : ℝ, Real.exp x • hfun t (Real.exp x))
      = ∫ x : ℝ, Ffun x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => Ffun_mul_exp t x))
  -- Identify the result with `𝓕 F (-t/(2π))`.
  have h5 : (∫ x : ℝ, Ffun x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
      = FourierTransform.fourier Ffun (-(t / (2 * Real.pi))) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    show Ffun v * Complex.exp (Complex.I * (t : ℂ) * (v : ℂ))
        = Complex.exp (↑((-2 : ℝ) * Real.pi * v * (-(t / (2 * Real.pi)))) * Complex.I) • Ffun v
    have hexp2 : Complex.exp
          (↑((-2 : ℝ) * Real.pi * v * (-(t / (2 * Real.pi)))) * Complex.I)
        = Complex.exp (Complex.I * (t : ℂ) * (v : ℂ)) := by
      congr 1
      rw [show (-2 : ℝ) * Real.pi * v * (-(t / (2 * Real.pi))) = v * t from by field_simp]
      push_cast
      ring
    rw [smul_eq_mul, hexp2]
    exact mul_comm _ _
  rw [hA, h1, h2, h3, h4, h5]

/-- GM Lemma 4.3(2) at `ξ = 0`: `‖ĥ_t(0)‖ ≤ C_j / |t|^j` for `|t| ≥ 1`.

Suggested route: `ĥ_t(0) = ∫ w(u)² e^{i t log u} du`, an integral over `[1,2]`; integrating by parts
`j` times against `e^{i t log u}` (or, equivalently, substituting `u = e^x`: it is the Fourier
transform at frequency `t/2π` of the smooth compactly supported function
`x ↦ w(e^x)² e^x` — so `Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` applies
directly, giving the statement with no `t`-dependent constant). -/
theorem hhat_zero_decay :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Submission.GM.hhat t 0‖ ≤ C / |t| ^ j := by
  intro j
  obtain ⟨C, hC, hbound⟩ :=
    Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay j Ffun_contDiff
      Ffun_hasCompactSupport
  refine ⟨C * (2 * Real.pi) ^ j, mul_nonneg hC (pow_nonneg (by positivity) j), ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := abs_pos.mp (lt_of_lt_of_le zero_lt_one ht)
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2πne : (2 * Real.pi) ≠ 0 := ne_of_gt h2π
  have hξ : -(t / (2 * Real.pi)) ≠ 0 := by
    simp [div_eq_zero_iff, ht0, h2πne]
  have hb := hbound (-(t / (2 * Real.pi))) hξ
  rw [abs_neg, abs_div, abs_of_pos h2π] at hb
  have hcalc : C / (|t| / (2 * Real.pi)) ^ j = C * (2 * Real.pi) ^ j / |t| ^ j := by
    rw [div_pow]
    field_simp
  rw [hhat_eq_fourier t]
  rw [hcalc] at hb
  exact hb

end Work.GM.Trace
