/-
# `Submission.Work.FIArea5.HeckeZFR.LamBaseBound`

The bound at the **base point of the Hadamard rebasing**:

  `Re (Λ'/Λ)(2 + iγ) ≤ C · (log(4d) + log(m + |γ| + 3))`,

with `C` absolute (in particular independent of `m` and `γ`).

Since the functional equation gives `Λ'/Λ(-1+iγ) = - conj (Λ'/Λ(2+iγ))`
(`FELogDeriv.logDeriv_FE_at_neg_one`), this is exactly the bound at `s₁ = -1+iγ` that the rebasing
lemma `re_logDeriv_rebase_of_pf` consumes.

The decomposition at `s = 2+iγ` (valid because `re s = 2 > 1`, where the identity theorem gives
`Lam = LambdaHecke` locally) is

  `Λ'/Λ = log(4d/π) + ψ(s + m/2) + L'/L(s,ψ)`,

and the three terms are bounded by `log(4d)`, `DigammaShift.digamma_re_le_of_half_le`
(`log(2+|γ|) + 2log(4(2+m/2)) + 6`) and `LSeriesBound.heckeLSeries_logDeriv_norm_le`
(`‖L'/L(2+iγ,ψ)‖ ≤ C₂`), respectively.
-/
import Mathlib
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound
import Submission.Work.FIArea5.HeckeZFR.DigammaShift
import Submission.Work.FIArea5.HeckeZFR.FELogDeriv
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea5.S16Hecke

open Complex Filter
open scoped Real Topology

noncomputable section

/-- The logarithmic derivative of `z ↦ X^z` is the constant `log X`. -/
lemma logDeriv_const_cpow (X : ℂ) (hX : X ≠ 0) (z : ℂ) :
    logDeriv (fun w : ℂ => X ^ w) z = Complex.log X := by
  have hXz : X ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hX)
  rw [logDeriv_apply, (hasStrictDerivAt_const_cpow (Or.inl hX)).hasDerivAt.deriv]
  field_simp

/-- The logarithmic derivative of `z ↦ Γ(z + c)` is `ψ(z + c)`. -/
lemma logDeriv_Gamma_add_const (c z : ℂ) (hzm : ∀ m : ℕ, z + c ≠ -m) :
    logDeriv (fun w : ℂ => Complex.Gamma (w + c)) z = Complex.digamma (z + c) := by
  have hg : DifferentiableAt ℂ (fun w : ℂ => w + c) z := differentiableAt_id.add_const c
  have hf : DifferentiableAt ℂ Complex.Gamma (z + c) := Complex.differentiableAt_Gamma _ hzm
  rw [show (fun w : ℂ => Complex.Gamma (w + c)) = Complex.Gamma ∘ (fun w : ℂ => w + c) from rfl,
    logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ => w + c) (x := z) hf hg]
  rw [show deriv (fun w : ℂ => w + c) z = 1 from by
    simpa using (hasDerivAt_id (x := z)).add_const c |>.deriv]
  rw [mul_one, Complex.digamma_def]

/-- **The bound at the rebasing base point.** -/
theorem Lam_logDeriv_re_at_two_le (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (Lam : ℂ → ℂ) (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagree : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ,
      (deriv Lam ((2 : ℂ) + (γ : ℂ) * I) / Lam ((2 : ℂ) + (γ : ℂ) * I)).re
        ≤ C * (Real.log (4 * (d : ℝ)) + Real.log ((m : ℝ) + |γ| + 3)) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := heckeLSeries_logDeriv_norm_le chi (m : ℤ) h1 hmul hb
  refine ⟨C₂ + 20, by linarith, ?_⟩
  intro γ
  set s : ℂ := (2 : ℂ) + (γ : ℂ) * I with hsdef
  have hsre : s.re = 2 := by simp [hsdef]
  have hs1 : (1 : ℝ) < s.re := by rw [hsre]; norm_num
  have hsmsre : (s + (m : ℂ) / 2).re = 2 + (m : ℝ) / 2 := by
    rw [Complex.add_re]
    have : ((m : ℂ) / 2).re = (m : ℝ) / 2 := by
      rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re]
      simp [Complex.normSq_apply]; ring
    rw [this, hsre]
  have hsms : s + (m : ℂ) / 2 = ((2 + (m : ℝ) / 2 : ℝ) : ℂ) + (γ : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  -- local agreement with the model function
  have hev : Lam =ᶠ[𝓝 s] fun z => (stripX d) ^ z * Complex.Gamma (z + (m : ℂ) / 2)
      * heckeLSeries chi (m : ℤ) z := by
    have hmem : {z : ℂ | (1 : ℝ) < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1
    filter_upwards [hmem] with z hz
    rw [Lam_eq_LambdaHecke_of_one_lt_re hd hAn hb hagree hz]
    rfl
  have hXne : stripX d ≠ 0 := stripX_ne_zero hd
  have hGne : Complex.Gamma (s + (m : ℂ) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hsmsre]; positivity)
  have hLne : heckeLSeries chi (m : ℤ) s ≠ 0 :=
    heckeLSeries_ne_zero_of_one_lt_re chi (m : ℤ) h1 hmul hb hs1
  have hzc : ((m : ℂ) / 2) ≠ 0 ∨ True := Or.inr trivial
  have hA : (fun z : ℂ => (stripX d) ^ z * Complex.Gamma (z + (m : ℂ) / 2)) s ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hXne)) hGne
  have hB : (fun z : ℂ => heckeLSeries chi (m : ℤ) z) s ≠ 0 := hLne
  have hC : (fun z : ℂ => (stripX d) ^ z) s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hXne)
  have hD : (fun z : ℂ => Complex.Gamma (z + (m : ℂ) / 2)) s ≠ 0 := hGne
  have hneGamma : ∀ k : ℕ, s + (m : ℂ) / 2 ≠ - (k : ℂ) := by
    intro k hk
    have hre : (s + (m : ℂ) / 2).re = -(k : ℝ) := by
      have := congrArg Complex.re hk; simpa using this
    rw [hsmsre] at hre
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hdiffX : DifferentiableAt ℂ (fun z : ℂ => (stripX d) ^ z) s :=
    (hasStrictDerivAt_const_cpow (Or.inl hXne)).hasDerivAt.differentiableAt
  have hdiffG : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + (m : ℂ) / 2)) s :=
    (Complex.differentiableAt_Gamma _ hneGamma).comp s (differentiableAt_id.add_const _)
  have hdiffL : DifferentiableAt ℂ (fun z : ℂ => heckeLSeries chi (m : ℤ) z) s := by
    have habs : LSeries.abscissaOfAbsConv (heckeLam chi (m : ℤ)) < (s.re : EReal) :=
      lt_of_le_of_lt (heckeLSeries_absc_le_one chi (m : ℤ) hb)
        (EReal.coe_lt_coe_iff.mpr (by rw [hsre]; norm_num))
    exact (LSeries_hasDerivAt (f := heckeLam chi (m : ℤ)) (s := s) habs).differentiableAt
  have hdecomp : logDeriv Lam s
      = Complex.log (stripX d) + Complex.digamma (s + (m : ℂ) / 2)
        + logDeriv (fun z => heckeLSeries chi (m : ℤ) z) s := by
    rw [(logDeriv_congr_nhds hev).eq_of_nhds]
    rw [Submission.Port.logDeriv_mul_fun (f := fun z : ℂ => (stripX d) ^ z * Complex.Gamma (z + (m : ℂ) / 2))
        (g := fun z : ℂ => heckeLSeries chi (m : ℤ) z) s hA hB (hdiffX.mul hdiffG) hdiffL]
    rw [Submission.Port.logDeriv_mul_fun (f := fun z : ℂ => (stripX d) ^ z)
        (g := fun z : ℂ => Complex.Gamma (z + (m : ℂ) / 2)) s hC hD hdiffX hdiffG]
    rw [logDeriv_const_cpow (stripX d) hXne s,
      logDeriv_Gamma_add_const ((m : ℂ) / 2) s hneGamma]
  rw [logDeriv_apply] at hdecomp
  -- the three bounds
  have hlogX : (Complex.log (stripX d)).re ≤ Real.log (4 * (d : ℝ)) := by
    rw [Complex.log_re]
    have hnorm : ‖stripX d‖ ≤ 4 * (d : ℝ) := by
      have h2 : stripX d = (((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ) := by simp [stripX]
      rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 4 * (d:ℝ) / Real.pi),
        div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) d]
    exact Real.log_le_log (by positivity) hnorm
  have hdig : (Complex.digamma (s + (m : ℂ) / 2)).re
      ≤ Real.log (2 + |γ|) + 2 * Real.log (4 * (2 + (m : ℝ) / 2)) + 6 := by
    have h := digamma_re_le_of_half_le (2 + (m : ℝ) / 2) γ
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
    rwa [hsms]
  have hLderiv : ((logDeriv (fun z => heckeLSeries chi (m : ℤ) z) s)).re ≤ C₂ := by
    rw [logDeriv_apply]
    exact le_trans (Complex.re_le_norm _) (hC₂ s hsre)
  have hfinal : (deriv Lam s / Lam s).re
      ≤ Real.log (4 * (d : ℝ)) + (Real.log (2 + |γ|) + 2 * Real.log (4 * (2 + (m : ℝ) / 2)) + 6)
        + C₂ := by
    rw [hdecomp, Complex.add_re, Complex.add_re]
    linarith [hlogX, hdig, hLderiv]
  have hlogd : (1 : ℝ) ≤ Real.log (4 * (d : ℝ)) := by
    have h4 : (4 : ℝ) ≤ 4 * (d : ℝ) := by
      have h1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have h1'' : Real.log 4 ≤ Real.log (4 * (d : ℝ)) := Real.log_le_log (by norm_num) h4
    have h2'' : (1 : ℝ) ≤ Real.log 4 := by
      have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [h]; linarith
    linarith
  have hlogm0 : (0 : ℝ) ≤ Real.log ((m : ℝ) + |γ| + 3) := by
    refine Real.log_nonneg ?_
    have h1' : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h2' : (0 : ℝ) ≤ |γ| := abs_nonneg γ
    linarith
  have hlogγ : Real.log (2 + |γ|) ≤ Real.log ((m : ℝ) + |γ| + 3) := by
    refine Real.log_le_log (by positivity) ?_
    have h1' : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hlog8m : Real.log (4 * (2 + (m : ℝ) / 2)) ≤ 3 + Real.log ((m : ℝ) + |γ| + 3) := by
    have h2 : 4 * (2 + (m : ℝ) / 2) ≤ 8 * ((m : ℝ) + |γ| + 3) := by
      have h1' : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h2' : (0 : ℝ) ≤ |γ| := abs_nonneg γ
      linarith
    have hlog := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by norm_num : (8:ℝ) ≠ 0) (by positivity)] at hlog
    have hlog8 : Real.log 8 ≤ 3 := by
      have h : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have h9 : Real.log 2 < 1 := by
        have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num : (2:ℝ) ≠ 1)
        linarith
      rw [h]; linarith
    linarith
  have hmain : Real.log (4 * (d : ℝ))
        + (Real.log (2 + |γ|) + 2 * Real.log (4 * (2 + (m : ℝ) / 2)) + 6) + C₂
      ≤ (C₂ + 20) * (Real.log (4 * (d : ℝ)) + Real.log ((m : ℝ) + |γ| + 3)) := by
    nlinarith [hlogγ, hlog8m, hlogd, hlogm0, hC₂pos]
  linarith [hfinal, hmain]

end

end Work.FIArea5.S16Hecke
