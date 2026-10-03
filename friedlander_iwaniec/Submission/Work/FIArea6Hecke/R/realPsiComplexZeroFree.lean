import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea6Hecke.R.lamGrowth
import Submission.Work.FIArea6Hecke.R.lamPartialFraction
import Submission.Work.FIArea6Hecke.R.zerosInStrip
import Submission.Work.FIArea6Hecke.R.baseLowerTwoUniform
import Submission.Work.FIArea6Hecke.R.baseLowerNegTwoUniform
import Submission.Work.FIArea6Hecke.R.HeckeAxisLogDerivBound
import Submission.Work.FIArea6Hecke.R.HeckeLDerivRe341
import Submission.Work.FIArea6Hecke.R.HeckeZFRCoreAsm
import Submission.Work.FIArea6Hecke.R.HeckeZFRCoreMain
import Submission.Work.FIArea6Hecke.R.heckeLSeries_conj_int
import Submission.Work.FIArea6Hecke.R.conductorFECleanNoDep
import Submission.Work.FIArea6Hecke.R.pfacBaseLowerUniform
import Submission.Work.FIArea6Hecke.R.HeckeSquareEqPrincipalOfPsiReal
import Submission.Work.FIArea6Hecke.R.HeckePrincipalLogDerivOffAxisSharp
import Submission.Work.FIArea6Hecke.R.Chi4LSeriesOffAxisLogDerivReBound
import Submission.Work.FIArea6Hecke.R.AxisBadPolyOffAxisLogDerivReBound
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-! ## 1. A crude off-axis bound for the principal Hecke `L`-function

`-Re (L'/L)(σ+iτ) ≤ 1/(σ-1) + C·log(4d(2+|τ|))` for `1 < σ ≤ 2` and *all* `τ`. -/

theorem principalOffAxisCrude :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 →
        (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)
          / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0
            ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
          ≤ 1 / (σ - 1) + C * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
  obtain ⟨C₂, δ₂, hC₂pos, hδ₂pos, hnear⟩ :=
    Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
  obtain ⟨Cζ, hCζpos, hζ⟩ := Commons.NumberTheory.DirichletCharacter.zeta_logDeriv_re_uniform
  obtain ⟨hχdiff, hχne, Cχ, hCχ0, hχ⟩ := axisChi4_LSeries_facts
  obtain ⟨Cχ', hCχ'pos, hχ'⟩ := Chi4LSeriesOffAxisLogDerivReBound
  obtain ⟨CG, hCGpos, hG⟩ := AxisBadPolyOffAxisLogDerivReBound
  refine ⟨C₂ + Cχ' + Cχ + Cζ + CG, by positivity, ?_⟩
  intro d hd σ τ hσ1 hσ2
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : 1 < s.re := by rw [hsdef]; simp; exact hσ1
  have hs' : s = (σ : ℂ) + Complex.I * (τ : ℂ) := by rw [hsdef]; ring
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hσpos : 0 < σ - 1 := by linarith
  have hLpos : 0 < Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    refine Real.log_pos ?_; nlinarith [abs_nonneg τ, hd1]
  have hL1 : 1 ≤ Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h8 : (8 : ℝ) ≤ 4 * (d : ℝ) * (2 + |τ|) := by nlinarith [abs_nonneg τ, hd1]
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith [Real.exp_le_exp.mpr (by norm_num : (1:ℝ) ≤ 2), he]
  have hlog2 : Real.log (2 + |τ|) ≤ Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    refine Real.log_le_log (by positivity) ?_; nlinarith [abs_nonneg τ, hd1]
  have hlog4 : Real.log (4 * (d : ℝ)) ≤ Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    refine Real.log_le_log (by positivity) ?_; nlinarith [abs_nonneg τ]
  have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hsre
  have hL4ne : LSeries axisChi4 s ≠ 0 := hχne s hsre
  have hGne : axisBadPoly d s ≠ 0 := axisBadPoly_ne_zero d hsre
  have hζd : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (by
      intro h; have h1 : s.re = 1 := by rw [h]; simp
      rw [hsdef] at h1; simp at h1; linarith)
  have hL4d : DifferentiableAt ℂ (LSeries axisChi4) s := hχdiff s hsre
  have hGd : DifferentiableAt ℂ (axisBadPoly d) s := differentiableAt_axisBadPoly d s
  have hL : Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0 =ᶠ[𝓝 s]
      (fun z => riemannZeta z * LSeries axisChi4 z * axisBadPoly d z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsre] with z hz
    exact heckeLSeries_principalStrict_eq d hd hz
  have hld : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) s
      = logDeriv riemannZeta s + logDeriv (LSeries axisChi4) s + logDeriv (axisBadPoly d) s := by
    rw [show logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) s
        = logDeriv (fun z => riemannZeta z * LSeries axisChi4 z * axisBadPoly d z) s
        from (logDeriv_congr_nhds hL).eq_of_nhds]
    rw [Submission.Port.logDeriv_mul_fun (f := fun z => riemannZeta z * LSeries axisChi4 z) (g := axisBadPoly d) s
        (mul_ne_zero hζne hL4ne) hGne (hζd.mul hL4d) hGd,
      Submission.Port.logDeriv_mul_fun (f := riemannZeta) (g := fun z => LSeries axisChi4 z) s
        hζne hL4ne hζd hL4d]
  have hdec : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) s
        / Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0 s).re
      = (-deriv riemannZeta s / riemannZeta s).re
        + (-deriv (LSeries axisChi4) s / LSeries axisChi4 s).re
        + (-deriv (axisBadPoly d) s / axisBadPoly d s).re := by
    have e0 : -deriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) s
        / Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0 s
        = -(logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) s) := by
      rw [logDeriv_apply, neg_div]
    have e1 : -deriv riemannZeta s / riemannZeta s = -(logDeriv riemannZeta s) := by
      rw [logDeriv_apply, neg_div]
    have e2 : -deriv (LSeries axisChi4) s / LSeries axisChi4 s
        = -(logDeriv (LSeries axisChi4) s) := by rw [logDeriv_apply, neg_div]
    have e3 : -deriv (axisBadPoly d) s / axisBadPoly d s
        = -(logDeriv (axisBadPoly d) s) := by rw [logDeriv_apply, neg_div]
    rw [e0, e1, e2, e3, hld]
    simp only [Complex.neg_re, Complex.add_re]
    ring
  rw [hdec]
  have hlog4d : 1 ≤ Real.log (4 * (d : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_three
    nlinarith [hd1]
  have hlogN : Real.log (2 + |τ|) + 1
      ≤ Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    linarith
  have hbζ : (-deriv riemannZeta s / riemannZeta s).re
      ≤ 1 / (σ - 1) + (Cζ + C₂) * (Real.log (2 + |τ|) + 1) := by
    have hsP : s = (σ : ℂ) + Complex.I * (τ : ℂ) := hs'
    rw [hsP]
    have hζ' := hζ σ τ hσ1 hσ2
    by_cases hτ : |τ| ≤ 1 / 2
    · have hδne : (1 : ℝ) - δ₂ ≤ σ := by
        have := hδ₂pos; linarith
      have hn := hnear τ σ (by linarith) (by linarith) hδne hσ2
      have hle : (-deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
            / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re
          ≤ ‖deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
              / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))‖ := by
        have h1 : -((deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
            / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re)
            ≤ |(deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
              / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re| := neg_le_abs _
        have h2 : |(deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
              / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re|
            ≤ ‖deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
              / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))‖ := Complex.abs_re_le_norm _
        have h3 : (-deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
            / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re
            = -((deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
              / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re) := by
          rw [neg_div, Complex.neg_re]
        rw [h3]; linarith
      have hrele : σ - 1 ≤ ‖(↑σ + Complex.I * ↑τ - 1 : ℂ)‖ := by
        have h1 := Complex.abs_re_le_norm ((↑σ + Complex.I * ↑τ - 1 : ℂ))
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
          Complex.one_re] at h1
        rw [show σ + 0 * τ - 1 = σ - 1 by ring, abs_of_pos hσpos] at h1
        exact h1
      have hinv : 1 / ‖(↑σ + Complex.I * ↑τ - 1 : ℂ)‖ ≤ 1 / (σ - 1) :=
        one_div_le_one_div_of_le hσpos hrele
      have hb : (-deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))
            / riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re
          ≤ C₂ + 1 / ‖(↑σ + Complex.I * ↑τ - 1 : ℂ)‖ :=
        le_trans hle (le_trans hn (by gcongr))
      have hlog2nn : 0 ≤ Real.log (2 + |τ|) :=
        Real.log_nonneg (by linarith [abs_nonneg τ])
      have hC₂b : C₂ ≤ (Cζ + C₂) * (Real.log (2 + |τ|) + 1) := by
        have h3 : (1 : ℝ) ≤ Real.log (2 + |τ|) + 1 := by linarith
        calc C₂ ≤ (Cζ + C₂) * 1 := by
              have h4 : C₂ ≤ Cζ + C₂ := by linarith
              simpa using h4
          _ ≤ (Cζ + C₂) * (Real.log (2 + |τ|) + 1) :=
              mul_le_mul_of_nonneg_left h3 (by linarith)
      linarith [hb, hinv, hC₂b]
    · push Not at hτ
      have hfar := hζ' (le_of_lt hτ)
      have hC₂b : C₂ ≤ (Cζ + C₂) * (Real.log (2 + |τ|) + 1) := by
        have h3 : (1 : ℝ) ≤ Real.log (2 + |τ|) + 1 := by
          have hnn : 0 ≤ Real.log (2 + |τ|) :=
            Real.log_nonneg (by linarith [abs_nonneg τ])
          linarith
        calc C₂ ≤ (Cζ + C₂) * 1 := by
              have h4 : C₂ ≤ Cζ + C₂ := by linarith
              simpa using h4
          _ ≤ (Cζ + C₂) * (Real.log (2 + |τ|) + 1) :=
              mul_le_mul_of_nonneg_left h3 (by linarith)
      have hlogτ : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
      have hx : 0 < 1 / (σ - 1) := one_div_pos.mpr hσpos
      nlinarith [hfar, hC₂b, hlogτ, hx, hCζpos, hC₂pos]
  have hbχ : (-deriv (LSeries axisChi4) s / LSeries axisChi4 s).re
      ≤ Cχ' * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    have h := hχ' σ τ hσ1 hσ2
    have : Cχ' * (Real.log (2 + |τ|) + 1) ≤ Cχ' * Real.log (4 * (d : ℝ) * (2 + |τ|)) :=
      mul_le_mul_of_nonneg_left hlogN hCχ'pos.le
    linarith
  have hbG : (-deriv (axisBadPoly d) s / axisBadPoly d s).re
      ≤ CG * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    have h := hG d hd σ τ hσ1 hσ2
    have : CG * Real.log (4 * (d : ℝ)) ≤ CG * Real.log (4 * (d : ℝ) * (2 + |τ|)) :=
      mul_le_mul_of_nonneg_left hlog4 hCGpos.le
    linarith
  have hfinal : (-deriv riemannZeta s / riemannZeta s).re
      + (-deriv (LSeries axisChi4) s / LSeries axisChi4 s).re
      + (-deriv (axisBadPoly d) s / axisBadPoly d s).re
      ≤ 1 / (σ - 1) + (C₂ + Cχ' + Cχ + Cζ + CG) * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
    have hbζ' : (-deriv riemannZeta s / riemannZeta s).re
        ≤ 1 / (σ - 1) + (Cζ + C₂) * Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
      have : (Cζ + C₂) * (Real.log (2 + |τ|) + 1) ≤ (Cζ + C₂) * Real.log (4 * (d : ℝ) * (2 + |τ|)) :=
        mul_le_mul_of_nonneg_left hlogN (by linarith)
      linarith [hbζ, this]
    nlinarith [hbζ', hbχ, hbG, hCχ0, hCGpos, hCχ'pos, hLpos]
  exact hfinal


/-! ## 2. The near-zero logarithmic-derivative bound with the two conjugate zeros

For an admissible completion `Λ` with a zero `ρ = β + iγ` (`0 < β ≤ 1`, `γ ≠ 0`) and its conjugate
`ρ̄ = β - iγ`, the Hadamard partial fraction rebased at `-2 + iγ` gives
`Re(Λ'/Λ)(σ+iγ) ≥ 1/(σ-β) + (σ-β)/((σ-β)²+4γ²) - C·log(4d(|γ|+3))`. -/

private lemma re_finsum_of_finiteSupport_rp (g : ℂ → ℂ) (hfs : Function.HasFiniteSupport g) :
    (∑ᶠ u, g u).re = ∑ᶠ u, (g u).re := by
  have h := AddMonoidHom.map_finsum (Complex.reCLM : ℂ →+ ℝ) hfs
  simpa using h

private lemma re_inv_coord_rp (z u : ℂ) :
    (1 / (z - u)).re
      = (z.re - u.re) / ((z.re - u.re) ^ 2 + (z.im - u.im) ^ 2) := by
  have h : z - u = ((z.re - u.re : ℝ) : ℂ) + ((z.im - u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  rw [h, one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
    sub_zero, mul_one, zero_mul, add_zero]
  ring

/-- Two-point lower bound for a finitely supported nonnegative real function. -/
private lemma hasFiniteSupport_ite (f : ℂ → ℝ) (a : ℂ)
    (hf : Function.HasFiniteSupport f) :
    Function.HasFiniteSupport (fun i : ℂ => if i = a then f a else 0) := by
  refine (Set.finite_singleton a).subset (fun i hi => ?_)
  rw [Function.mem_support] at hi
  simp only [Set.mem_singleton_iff]
  by_contra hia
  exact hi (if_neg hia)

/-- Two-point lower bound for a finitely supported nonnegative real function. -/
private lemma two_le_finsum_rp {f : ℂ → ℝ} {a b : ℂ} (hab : a ≠ b)
    (hf : Function.HasFiniteSupport f) (hnn : ∀ i, 0 ≤ f i) :
    f a + f b ≤ ∑ᶠ i, f i := by
  have hia := hasFiniteSupport_ite f a hf
  have hib := hasFiniteSupport_ite f b hf
  have hsum := finsum_add_distrib hia hib
  have ea : (∑ᶠ i : ℂ, (if i = a then f a else 0)) = f a := by
    rw [finsum_eq_single (fun i : ℂ => if i = a then f a else 0) a (fun x hx => by rw [if_neg hx])]
    rw [if_pos rfl]
  have eb : (∑ᶠ i : ℂ, (if i = b then f b else 0)) = f b := by
    rw [finsum_eq_single (fun i : ℂ => if i = b then f b else 0) b (fun x hx => by rw [if_neg hx])]
    rw [if_pos rfl]
  rw [ea, eb] at hsum
  rw [← hsum]
  refine finsum_le_finsum' (hia.add hib) hf (fun i => ?_)
  by_cases h : i = a
  · rw [if_pos h, if_neg (fun hh => hab (h.symm.trans hh)), add_zero, h]
  · by_cases h2 : i = b
    · rw [if_neg h, if_pos h2, zero_add, h2]
    · rw [if_neg h, if_neg h2, zero_add]
      exact hnn i

/-- The real part of `1/(a + b·i)` for real `a, b`. -/
private lemma re_inv_add_I (a b : ℝ) :
    (1 / (((a : ℂ) + (b : ℂ) * Complex.I))).re = a / (a ^ 2 + b ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  ring

/-- The rebasing kernel of the conjugate zero `β - iγ` (base point `-2 + iγ`). -/
private lemma kernel_conj_negTwo {σ β γ : ℝ} (hβσ : β < σ) (hβ : -1 ≤ β) (hγ : γ ≠ 0) :
    (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
      ≤ ((1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) - (γ : ℂ) * Complex.I))
          - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I)
              - ((β : ℂ) - (γ : ℂ) * Complex.I)))).re := by
  have hsp : ((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) - (γ : ℂ) * Complex.I)
      = (((σ - β : ℝ)) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  have hs2p : ((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) - (γ : ℂ) * Complex.I)
      = (((-2 - β : ℝ)) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [hsp, hs2p, Complex.sub_re, re_inv_add_I, re_inv_add_I]
  have hB : (-2 - β) / ((-2 - β) ^ 2 + (2 * γ) ^ 2) ≤ 0 := by
    have : (-2 - β) ≤ 0 := by linarith
    apply div_nonpos_of_nonpos_of_nonneg this
    nlinarith [sq_nonneg γ]
  have hA : (σ - β) / ((σ - β) ^ 2 + (2 * γ) ^ 2) = (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) := by
    ring_nf
  rw [hA]
  linarith

/-- The rebasing kernel at the zero `β + iγ` itself (base point `-2 + iγ`). -/
private lemma kernel_same_height_negTwo {σ β γ : ℝ} (hβσ : β < σ) (hβ : -1 ≤ β) :
    1 / (σ - β) ≤ ((1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)))
        - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re := by
  have hsp : ((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
      = (((σ - β : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp
  have hs2p : ((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
      = (((-2 - β : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hsp, hs2p, Complex.sub_re,
    show (1 / (((σ - β : ℝ)) : ℂ)).re = 1 / (σ - β) from by
      rw [one_div, one_div, ← Complex.ofReal_inv, Complex.ofReal_re],
    show (1 / (((-2 - β : ℝ)) : ℂ)).re = 1 / (-2 - β) from by
      rw [one_div, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]]
  have h1 : (0 : ℝ) < σ - β := by linarith
  have h2 : -2 - β < 0 := by linarith
  have h3 : (1 : ℝ) / (-2 - β) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_lt h2)
  linarith

theorem nearZeroBoundTwoPoles :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (Lam : ℂ → ℂ),
        Work.FIArea6Hecke.R.IsCompleted d chi 0 Lam →
        ∀ (σ β γ : ℝ), 1 < σ → σ ≤ 2 → 0 < β → β ≤ 1 → β < σ → γ ≠ 0 →
          Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
          Lam ((β : ℂ) - (γ : ℂ) * Complex.I) = 0 →
            1 / (σ - β) + (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
              - C * Real.log (4 * (d : ℝ) * (|γ| + 3))
            ≤ (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
                / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨Cm2, hCm2pos, hbase⟩ := pfacBaseLowerUniform (fun d chi m (hd : 1 ≤ d) hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt)
  refine ⟨Cm2 + 1, by linarith, ?_⟩
  intro d chi Lam hadm σ β γ hσ1 hσ2 hβ0 hβ1 hβσ hγ hρ hρc
  have hzeros : ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1 :=
    zerosInStrip_of_conductorFE (fun d chi m (hd : 1 ≤ d) hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt) d chi 0 Lam hadm
  have hgr := lamGrowth d chi 0 Lam hadm
  have hpf := lamPartialFraction d chi 0 Lam hadm hgr
  have hd : 1 ≤ d := hadm.1
  have hchi := hadm.2.1
  have hAn := hadm.2.2.1
  have hDiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hsdef
  set s₂ : ℂ := (-2 : ℂ) + (γ : ℂ) * Complex.I with hs₂def
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hs : Lam s ≠ 0 :=
    lam_ne_zero_of_one_lt_re_zz hd hAn h1 hmul hb hadm.2.2.2 (by rw [hsre]; linarith)
  have hs₂ : Lam s₂ ≠ 0 := by
    intro h0
    have h := (hzeros s₂ h0).1
    simp only [hs₂def, Complex.add_re, Complex.ofReal_re, Complex.ofReal_neg,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
      Complex.neg_re] at h
    norm_num at h
  set ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I with hρdef
  set ρc : ℂ := (β : ℂ) - (γ : ℂ) * Complex.I with hρcdef
  have hLamne : Lam ≠ 0 := fun hcon => hs (by rw [hcon]; rfl)
  have hpoint : ∀ (R : ℝ) (u : ℂ),
      0 ≤ ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₂ - u))).re := by
    intro R u
    by_cases hD : (MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u = 0
    · rw [hD]; simp
    · have hAnR : AnalyticOnNhd ℂ Lam (Metric.closedBall 0 R) :=
        Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hDiff _
      have hzero : Lam u = 0 := Commons.Analysis.Complex.zero_of_divisor_ne_zero hAnR hD
      have hzu := hzeros u hzero
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)).im
          = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      refine mul_nonneg (Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAnR u) ?_
      have h1 : (1 / (s - u)).re = (σ - u.re) / ((σ - u.re) ^ 2 + (γ - u.im) ^ 2) := by
        rw [hsdef, re_inv_coord_rp]; simp
      have h2 : (1 / (s₂ - u)).re = (-2 - u.re) / ((-2 - u.re) ^ 2 + (γ - u.im) ^ 2) := by
        rw [hs₂def, re_inv_coord_rp]; simp
      rw [Complex.sub_re, h1, h2]
      have hA : 0 ≤ (σ - u.re) / ((σ - u.re) ^ 2 + (γ - u.im) ^ 2) :=
        div_nonneg (by linarith [hzu.2]) (by nlinarith [sq_nonneg (σ - u.re)])
      have hB : (-2 - u.re) / ((-2 - u.re) ^ 2 + (γ - u.im) ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [hzu.1])
          (by nlinarith [sq_nonneg (γ - u.im)])
      linarith
  have hbig : ∀ᶠ R : ℝ in Filter.atTop,
      1 / (σ - β) + (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
        ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u) - 1 / (s₂ - u))).re := by
    rw [Filter.eventually_atTop]
    refine ⟨max (max ‖ρ‖ ‖ρc‖) 0, fun R hR => ?_⟩
    have hρball : ρ ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
    have hρcball : ρc ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
    have hDρ : (MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρ ≠ 0 :=
      Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hDiff hLamne hρball hρ
    have hDρc : (MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρc ≠ 0 :=
      Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hDiff hLamne hρcball hρc
    have hAnR : AnalyticOnNhd ℂ Lam (Metric.closedBall 0 R) :=
      Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hDiff _
    have hmult : ∀ u : ℂ, (MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u ≠ 0 →
        (1 : ℝ) ≤ (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by
      intro u hu
      have hnn : (0 : ℝ) ≤ (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℝ) :=
        Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAnR u
      have hne : (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℝ) ≠ 0 := by
        intro h0; exact hu (by exact_mod_cast h0)
      have hpos : (0 : ℝ) < (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℝ) :=
        lt_of_le_of_ne hnn (Ne.symm hne)
      exact_mod_cast (show (1 : ℤ) ≤ _ by exact_mod_cast hpos)
    have hρterm : 1 / (σ - β) ≤ ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρ : ℤ) : ℂ)
          * (1 / (s - ρ) - 1 / (s₂ - ρ))).re := by
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρ : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρ : ℤ) : ℂ)).im = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      have hK : 1 / (σ - β) ≤ (1 / (s - ρ) - 1 / (s₂ - ρ)).re := by
        rw [hsdef, hs₂def, hρdef]
        exact kernel_same_height_negTwo hβσ (by linarith)
      have hpos : 0 ≤ (1 / (s - ρ) - 1 / (s₂ - ρ)).re :=
        le_trans (by positivity : 0 ≤ 1 / (σ - β)) hK
      calc 1 / (σ - β) ≤ 1 * (1 / (s - ρ) - 1 / (s₂ - ρ)).re := by
            rw [one_mul]; exact hK
        _ ≤ _ := mul_le_mul_of_nonneg_right (hmult ρ hDρ) hpos
    have hρcterm : (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
        ≤ ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρc : ℤ) : ℂ)
          * (1 / (s - ρc) - 1 / (s₂ - ρc))).re := by
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρc : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρc : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) ρc : ℤ) : ℂ)).im = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      have hK : (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
          ≤ (1 / (s - ρc) - 1 / (s₂ - ρc)).re := by
        rw [hsdef, hs₂def, hρcdef]
        exact kernel_conj_negTwo hβσ (by linarith) hγ
      have hpos : 0 ≤ (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) :=
        div_nonneg (by linarith) (by nlinarith [sq_nonneg (σ - β), sq_nonneg γ])
      calc (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
            ≤ 1 * (1 / (s - ρc) - 1 / (s₂ - ρc)).re := by
              rw [one_mul]; exact hK
        _ ≤ _ := mul_le_mul_of_nonneg_right (hmult ρc hDρc) (le_trans hpos hK)
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₂ - u))) :=
      ((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset
        (fun u hu => by rw [Function.mem_support] at hu ⊢; intro hdd; exact hu (by simp [hdd]))
    have hfs' : Function.HasFiniteSupport (fun u : ℂ =>
        ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₂ - u))).re) :=
      hfs.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢; intro h0; exact hu (by rw [h0]; simp))
    have hρne : ρ ≠ ρc := by
      intro heq
      have := congrArg Complex.im heq
      rw [hρdef, hρcdef] at this; simp at this; exact hγ (by linarith)
    have hle := two_le_finsum_rp hρne hfs' (fun j => hpoint R j)
    rw [← re_finsum_of_finiteSupport_rp _ hfs] at hle
    simp only [hρdef, hρcdef] at hle
    linarith [hle, hρterm, hρcterm]
  have hlim : Filter.Tendsto (fun R : ℝ => (∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₂ - u))).re) Filter.atTop
      (nhds ((deriv Lam s / Lam s - deriv Lam s₂ / Lam s₂).re)) :=
    (Complex.continuous_re.tendsto _).comp (hpf s s₂ hs hs₂)
  have hge : 1 / (σ - β) + (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
      ≤ (deriv Lam s / Lam s - deriv Lam s₂ / Lam s₂).re :=
    ge_of_tendsto hlim hbig
  rw [Complex.sub_re] at hge
  have hbase' := hbase d chi 0 Lam hadm γ
  rw [← hs₂def] at hbase'
  simp only [Int.cast_zero, abs_zero, zero_add] at hbase'
  have hlogpos : 0 ≤ Real.log (4 * (d : ℝ) * (|γ| + 3)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith [abs_nonneg γ]
  linarith [hge, hbase', hlogpos]


/-! ## 3. Conjugation symmetry of the completion -/

private lemma lam_star_symm {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hreal : ∀ z : GaussianInt, chi z = star (chi z)) {Lam : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) :
    ∀ s : ℂ, Lam (star s) = star (Lam s) := by
  have hGan : AnalyticOn ℂ (fun s : ℂ => star (Lam (star s))) Set.univ := by
    refine DifferentiableOn.analyticOn ?_ isOpen_univ
    intro z _
    have h1 : DifferentiableAt ℂ Lam (star z) := (hAn.analyticAt Filter.univ_mem).differentiableAt
    have h3 := DifferentiableAt.conj_conj (f := Lam) (x := star z) h1
    have h3' : DifferentiableAt ℂ (fun s : ℂ => star (Lam (star s))) (star (star z)) := h3
    rw [star_star] at h3'
    exact h3'.differentiableWithinAt
  have hagree : ∀ s : ℂ, 1 < s.re → Lam s = star (Lam (star s)) := by
    intro s hs
    rw [hagr s hs, hagr (star s) (by simpa using hs), star_mul', star_heckeArch d 0 s hd]
    congr 1
    have hconj := heckeLSeries_conj_int chi 0 s
    rw [show (-(0:ℤ)) = 0 from rfl,
      show (fun z : GaussianInt => star (chi z)) = chi from funext (fun z => (hreal z).symm)] at hconj
    exact hconj
  have hEq : Lam = fun s : ℂ => star (Lam (star s)) :=
    eq_of_agrees_right (G := fun s : ℂ => star (Lam (star s))) (Lam := Lam) hGan hAn hagree
  intro s
  have h := congrArg star (congrFun hEq s)
  simp only [star_star] at h
  exact h.symm

/-! ## 4. The real-`ψ` complex zero-free region -/

theorem realPsiComplexZeroFree :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, chi z = star (chi z)) →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ s : ℂ, s.im ≠ 0 →
          1 - c / Real.log (4 * (d : ℝ) + |s.im|) < s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d 0 Lam s ≠ 0 := by
  obtain ⟨Csh, hCshpos, hSharp⟩ := HeckePrincipalLogDerivOffAxisSharp
  obtain ⟨C1, hC1nn, hAxis⟩ := HeckeAxisLogDerivBound
  obtain ⟨Ccrude, hCrudepos, hCrude⟩ := principalOffAxisCrude
  obtain ⟨Cnear, hNearpos, hNear⟩ := nearZeroBoundTwoPoles
  set A : ℝ := 100 * (3 * C1 + Ccrude + 4 * Cnear + 160 + 2 * Csh + 1) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hA100 : 100 ≤ A := by
    rw [hAdef]
    have h : 0 ≤ 3 * C1 + Ccrude + 4 * Cnear + 160 + 2 * Csh := by
      nlinarith [hC1nn, hCrudepos, hNearpos, hCshpos]
    linarith
  refine ⟨1 / (1024 * A), by positivity, ?_⟩
  intro d chi Lam hd hchi hreal hAn hagr s hsim hreg hs2
  by_contra hzero
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hagr' : ∀ t : ℂ, 1 + |(((0 : ℤ)) : ℝ)| / 2 < t.re →
      Lam t = Work.FITop4.Bridge.heckeArch d 0 t *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 t := by
    intro t ht
    refine hagr t ?_
    simpa using ht
  have hAdm : IsCompleted d chi 0 Lam := ⟨hd, hchi, hAn, hagr'⟩
  have hlog_s : 0 < Real.log (4 * (d : ℝ) + |s.im|) := by
    refine Real.log_pos ?_; nlinarith [hd1, abs_nonneg s.im]
  have hlog_s1 : 1 < Real.log (4 * (d : ℝ) + |s.im|) := by
    rw [Real.lt_log_iff_exp_lt (by nlinarith [hd1, abs_nonneg s.im])]
    have := Real.exp_one_lt_three
    nlinarith [hd1, abs_nonneg s.im]
  have hc_s : 1 / (1024 * A) / Real.log (4 * (d : ℝ) + |s.im|) < 1 := by
    rw [div_lt_one hlog_s]
    have h1c : 1 / (1024 * A) ≤ 1 / 64 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith [hA100]
    linarith [hlog_s1]
  have hsre_pos : 0 < s.re := by linarith [hreg, hc_s]
  have harch_ne : Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 :=
    heckeArch_ne_zero_of_pos_re d hd 0 hsre_pos
  have hLs : Lam s = 0 := (div_eq_zero_iff.mp hzero).resolve_right harch_ne
  set γ : ℝ := s.im with hγdef
  set β : ℝ := s.re with hβdef
  have hs_eq : s = (β : ℂ) + (γ : ℂ) * Complex.I := by
    rw [hβdef, hγdef]; apply Complex.ext <;> simp
  have hγne : γ ≠ 0 := by rw [hγdef]; exact hsim
  have hβmem : -1 ≤ β ∧ β ≤ 1 := by
    rw [hβdef]; exact zerosInStrip_of_conductorFE (fun d chi m (hd : 1 ≤ d) hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt) d chi 0 Lam hAdm s hLs
  have hρ : Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := by rw [← hs_eq]; exact hLs
  have hsym := lam_star_symm hd hreal hAn hagr
  have hρc : Lam ((β : ℂ) - (γ : ℂ) * Complex.I) = 0 := by
    have h := hsym ((β : ℂ) + (γ : ℂ) * Complex.I)
    rw [hρ, star_zero] at h
    have h2 : star ((β : ℂ) + (γ : ℂ) * Complex.I) = (β : ℂ) - (γ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.star_def] <;> ring
    rwa [h2] at h
  -- logarithms and region constants
  set ℓ : ℝ := Real.log (4 * (d : ℝ) * (|γ| + 3)) with hℓdef
  set Lγ : ℝ := Real.log (4 * (d : ℝ) + |γ|) with hLγdef
  set ℓ' : ℝ := Real.log (4 * (d : ℝ) * (2 + |(2 : ℝ) * γ|)) with hℓ'def
  have hγabs : 0 ≤ |γ| := abs_nonneg _
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, Real.le_log_iff_exp_le (by nlinarith [hd1, hγabs])]
    have := Real.exp_one_lt_three
    nlinarith [hd1, hγabs]
  have hLγ1 : 1 ≤ Lγ := by
    rw [hLγdef, Real.le_log_iff_exp_le (by nlinarith [hd1, hγabs])]
    have := Real.exp_one_lt_three
    nlinarith [hd1, hγabs]
  have hℓpos : 0 < ℓ := by linarith [hℓ1]
  have hℓ_le : ℓ ≤ 4 * Lγ := by
    have hsq : 4 * (d : ℝ) * (|γ| + 3) ≤ (4 * (d : ℝ) + |γ|) ^ 2 := by
      nlinarith [hd1, hγabs, sq_nonneg γ]
    calc ℓ ≤ Real.log ((4 * (d : ℝ) + |γ|) ^ 2) := Real.log_le_log (by positivity) hsq
      _ = 2 * Lγ := by rw [hLγdef, Real.log_pow]; ring
      _ ≤ 4 * Lγ := by linarith [hLγ1]
  have hℓ'le : ℓ' ≤ 2 * ℓ := by
    rw [hℓ'def, hℓdef]
    have hle : 4 * (d : ℝ) * (2 + |(2 : ℝ) * γ|) ≤ 2 * (4 * (d : ℝ) * (|γ| + 3)) := by
      have h2 : |(2 : ℝ) * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
      rw [h2]; nlinarith [hd1, hγabs]
    have h1 : Real.log (4 * (d : ℝ) * (2 + |(2 : ℝ) * γ|))
        ≤ Real.log (2 * (4 * (d : ℝ) * (|γ| + 3))) := Real.log_le_log (by positivity) hle
    have h2 : Real.log (2 * (4 * (d : ℝ) * (|γ| + 3)))
        = Real.log 2 + Real.log (4 * (d : ℝ) * (|γ| + 3)) :=
      Real.log_mul (by norm_num) (ne_of_gt (by positivity))
    have hc2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith [h1, h2.le, h2.ge, hc2, hℓ1]
  set x : ℝ := 1 / (A * ℓ) with hxdef
  have hAℓ1 : 1 ≤ A * ℓ := by
    have : (1:ℝ) ≤ A := by linarith [hA100]
    nlinarith [hℓ1]
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one (by positivity)]; exact hAℓ1
  have hσ1 : 1 < 1 + x := by linarith
  have hσ2 : 1 + x ≤ 2 := by linarith
  have hreg' : 1 - (1 / (1024 * A)) / Lγ < β := hreg
  -- (3,4,1)
  have hpsi : PsiReal chi 0 := (psiReal_zero_iff).mpr (fun z => (hreal z).symm)
  have hsq0 : Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => chi z * chi z) 0
      = Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0 := by
    simpa using HeckeSquareEqPrincipalOfPsiReal d chi 0 hd hchi hpsi
  have h1 : chi 1 = 1 := hchi.1.1
  have hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have h341 := HeckeLDerivRe341 d chi 0 hd hchi (σ := 1 + x) (t := γ) (by linarith)
  rw [show (2 : ℤ) * 0 = 0 by norm_num, hsq0] at h341
  have hA1bd : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0)
        ((((1 + x : ℝ)) : ℂ))
      / Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0 ((((1 + x : ℝ)) : ℂ))).re
      ≤ 1 / x + C1 := by
    have h := hAxis d hd (1 + x) hσ1 hσ2
    have hx' : (1 + x) - 1 = x := by ring
    simpa [hx'] using h
  have hB1bd : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries chi 0)
        ((((1 + x : ℝ)) : ℂ) + (γ : ℂ) * Complex.I)
      / Work.FIArea5.S16Hecke.heckeLSeries chi 0
        ((((1 + x : ℝ)) : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ -(1 / ((1 + x) - β)) - ((1 + x) - β) / (((1 + x) - β) ^ 2 + 4 * γ ^ 2)
        + Cnear * ℓ + 40 * ℓ := by
    have hne := neg_re_L_eq d hd (m := (0:ℤ)) hAn h1 hmul hb hagr'
      (s := ((((1 + x : ℝ)) : ℂ) + (γ : ℂ) * Complex.I)) (by simp; linarith)
    rw [hne]
    have hnear := hNear d chi Lam hAdm (1 + x) β γ hσ1 hσ2 (by linarith [hβmem.1])
      hβmem.2 (by linarith) hγne hρ hρc
    have harch' : (logDeriv (Work.FITop4.Bridge.heckeArch d 0)
        ((((1 + x : ℝ)) : ℂ) + (γ : ℂ) * Complex.I)).re ≤ 40 * ℓ := by
      have h := archLogDeriv_re_le d hd 0
        (s := ((((1 + x : ℝ)) : ℂ) + (γ : ℂ) * Complex.I)) (by simp; linarith) (by simp; linarith)
      have him : ((((1 + x : ℝ)) : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
      rw [him] at h
      simp only [Int.cast_zero, abs_zero, zero_add] at h
      rw [hℓdef]
      exact h
    rw [← hℓdef] at hnear
    linarith [hnear, harch']
  have hT3far : x ≤ |(2 : ℝ) * γ| →
      (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0)
        ((((1 + x : ℝ)) : ℂ) + (((2 : ℝ) * γ : ℝ)) * Complex.I)
      / Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0
        ((((1 + x : ℝ)) : ℂ) + (((2 : ℝ) * γ : ℝ)) * Complex.I)).re
      ≤ (1 / 2) * (1 / x) + Csh * ℓ' := by
    intro hxx
    have h := hSharp d hd (1 + x) (2 * γ) hσ1 hσ2 (by
      have hx' : (1 + x) - 1 = x := by ring
      rw [hx']; exact hxx)
    have hx' : (1 + x) - 1 = x := by ring
    rw [hx', show 1 / (2 * x) = (1 / 2) * (1 / x) by ring] at h
    simpa [hℓ'def] using h
  have hT3near : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0)
        ((((1 + x : ℝ)) : ℂ) + (((2 : ℝ) * γ : ℝ)) * Complex.I)
      / Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0
        ((((1 + x : ℝ)) : ℂ) + (((2 : ℝ) * γ : ℝ)) * Complex.I)).re
      ≤ 1 / x + Ccrude * ℓ' := by
    have h := hCrude d hd (1 + x) (2 * γ) hσ1 hσ2
    have hx' : (1 + x) - 1 = x := by ring
    rw [hx'] at h
    simpa [hℓ'def] using h
  -- arithmetic budgets
  have hC1bud : 3 * C1 ≤ (1 / 16) / x := by
    rw [le_div_iff₀ hxpos, hxdef]
    rw [show 3 * C1 * (1 / (A * ℓ)) = 3 * C1 / (A * ℓ) by ring,
      div_le_iff₀ (by positivity : 0 < A * ℓ)]
    have h : (100 : ℝ) * (3 * C1 + 1) ≤ A := by
      rw [hAdef]; nlinarith [hC1nn, hCrudepos, hNearpos, hCshpos]
    nlinarith [hℓ1, hC1nn, h]
  have hCshbud : Csh * ℓ' ≤ (1 / 16) / x := by
    rw [le_div_iff₀ hxpos, hxdef]
    have h : (100 : ℝ) * (2 * Csh + 1) ≤ A := by
      rw [hAdef]; nlinarith [hC1nn, hCrudepos, hNearpos, hCshpos]
    have h2 : 2 * Csh / A ≤ (1 / 16) := by
      rw [div_le_iff₀ hApos]; nlinarith [hCshpos, h]
    have he : Csh * ℓ' * (1 / (A * ℓ)) ≤ Csh * (2 * ℓ) * (1 / (A * ℓ)) := by
      have := mul_le_mul_of_nonneg_left hℓ'le hCshpos.le
      have hxx : 0 ≤ 1 / (A * ℓ) := by positivity
      nlinarith [this, hxx]
    have h3 : Csh * (2 * ℓ) * (1 / (A * ℓ)) = 2 * Csh / A := by field_simp
    linarith [he, h3.le, h3.ge, h2]
  have hCcrudebud : Ccrude * ℓ' ≤ (1 / 16) / x := by
    rw [le_div_iff₀ hxpos, hxdef]
    have h : (100 : ℝ) * (Ccrude + 1) ≤ A := by
      rw [hAdef]; nlinarith [hC1nn, hCrudepos, hNearpos, hCshpos]
    have h2 : 2 * Ccrude / A ≤ (1 / 16) := by
      rw [div_le_iff₀ hApos]; nlinarith [hCrudepos, h]
    have he : Ccrude * ℓ' * (1 / (A * ℓ)) ≤ Ccrude * (2 * ℓ) * (1 / (A * ℓ)) := by
      have := mul_le_mul_of_nonneg_left hℓ'le hCrudepos.le
      have hxx : 0 ≤ 1 / (A * ℓ) := by positivity
      nlinarith [this, hxx]
    have h3 : Ccrude * (2 * ℓ) * (1 / (A * ℓ)) = 2 * Ccrude / A := by field_simp
    linarith [he, h3.le, h3.ge, h2]
  have hCnbud : Cnear * ℓ + 40 * ℓ ≤ (1 / 16) / x := by
    rw [show Cnear * ℓ + 40 * ℓ = (Cnear + 40) * ℓ by ring]
    rw [le_div_iff₀ hxpos, hxdef]
    rw [show (Cnear + 40) * ℓ * (1 / (A * ℓ)) = (Cnear + 40) / A by field_simp]
    rw [div_le_iff₀ hApos]
    have h : (100 : ℝ) * (4 * Cnear + 160) ≤ A := by
      rw [hAdef]; nlinarith [hC1nn, hCrudepos, hNearpos, hCshpos]
    nlinarith [hNearpos, h]
  have hδx : x / 64 ≤ 1 - β := by
    have hYpos : 0 < (1 + x) - β := by have := hβmem.2; linarith
    rcases lt_or_ge |(2 : ℝ) * γ| x with hnear | hfar
    · -- near the axis: the conjugate zero contributes a doubled pole
      have hT3 := hT3near
      have hTge : 2 * (1 / ((1 + x) - β))
          ≤ 4 * (((1 + x) - β) / (((1 + x) - β) ^ 2 + 4 * γ ^ 2)) := by
        have h2g : 4 * γ ^ 2 ≤ ((1 + x) - β) ^ 2 := by
          have hb2 : |(2 : ℝ) * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
          rw [hb2] at hnear
          have := hβmem.2
          nlinarith [hnear, abs_nonneg γ, sq_abs γ]
        have hden : 0 < ((1 + x) - β) ^ 2 + 4 * γ ^ 2 := by
          nlinarith [sq_nonneg ((1 + x) - β), sq_nonneg γ]
        rw [show 2 * (1 / ((1 + x) - β)) = 2 / ((1 + x) - β) by ring,
          show 4 * (((1 + x) - β) / (((1 + x) - β) ^ 2 + 4 * γ ^ 2))
            = 4 * ((1 + x) - β) / (((1 + x) - β) ^ 2 + 4 * γ ^ 2) by ring]
        rw [div_le_div_iff₀ hYpos hden]
        nlinarith [h2g]
      have hkey : 6 * (1 / ((1 + x) - β))
          ≤ 4 * (1 / x) + 3 * C1 + Ccrude * ℓ' + 4 * (Cnear * ℓ) + 160 * ℓ := by
        linarith [h341, hA1bd, hB1bd, hT3, hTge]
      have hCn' : 4 * (Cnear * ℓ) + 160 * ℓ ≤ 4 * ((1 / 16) / x) := by linarith [hCnbud]
      have hb : 4 * (1 / x) + 3 * C1 + Ccrude * ℓ' + 4 * (Cnear * ℓ) + 160 * ℓ
          ≤ 4 * (1 / x) + (1 / 16) * (1 / x) + (1 / 16) * (1 / x)
            + 4 * ((1 / 16) * (1 / x)) := by
        have e : (1 / 16) / x = (1 / 16) * (1 / x) := by ring
        linarith [hC1bud, hCcrudebud, hCn']
      have hs : 4 * (1 / x) + (1 / 16) * (1 / x) + (1 / 16) * (1 / x)
          + 4 * ((1 / 16) * (1 / x)) = (35 / 8) * (1 / x) := by ring
      have hmain : 6 * (1 / ((1 + x) - β)) ≤ (35 / 8) * (1 / x) := by
        linarith [hkey, hb, hs.le]
      have h1 : 6 * (1 / ((1 + x) - β)) * (x * ((1 + x) - β))
          ≤ (35 / 8) * (1 / x) * (x * ((1 + x) - β)) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
      have e1 : 6 * (1 / ((1 + x) - β)) * (x * ((1 + x) - β)) = 6 * x := by field_simp
      have e2 : (35 / 8) * (1 / x) * (x * ((1 + x) - β)) = (35 / 8) * ((1 + x) - β) := by
        field_simp
      nlinarith [h1, e1.le, e1.ge, e2.le, e2.ge, hxpos, hYpos]
    · -- far from the axis
      have hT3 := hT3far hfar
      have hTpos : 0 ≤ ((1 + x) - β) / (((1 + x) - β) ^ 2 + 4 * γ ^ 2) := by
        apply div_nonneg
        · have := hβmem.2; linarith
        · nlinarith [sq_nonneg ((1 + x) - β), sq_nonneg γ]
      have hkey : 4 * (1 / ((1 + x) - β))
          ≤ (7 / 2) * (1 / x) + 3 * C1 + Csh * ℓ' + 4 * (Cnear * ℓ) + 160 * ℓ := by
        linarith [h341, hA1bd, hB1bd, hT3, hTpos]
      have hCn' : 4 * (Cnear * ℓ) + 160 * ℓ ≤ 4 * ((1 / 16) / x) := by linarith [hCnbud]
      have hb : (7 / 2) * (1 / x) + 3 * C1 + Csh * ℓ' + 4 * (Cnear * ℓ) + 160 * ℓ
          ≤ (7 / 2) * (1 / x) + (1 / 16) * (1 / x) + (1 / 16) * (1 / x)
            + 4 * ((1 / 16) * (1 / x)) := by
        have e : (1 / 16) / x = (1 / 16) * (1 / x) := by ring
        linarith [hC1bud, hCshbud, hCn']
      have hs : (7 / 2) * (1 / x) + (1 / 16) * (1 / x) + (1 / 16) * (1 / x)
          + 4 * ((1 / 16) * (1 / x)) = (31 / 8) * (1 / x) := by ring
      have hmain : 4 * (1 / ((1 + x) - β)) ≤ (31 / 8) * (1 / x) := by
        linarith [hkey, hb, hs.le]
      have h1 : 4 * (1 / ((1 + x) - β)) * (x * ((1 + x) - β))
          ≤ (31 / 8) * (1 / x) * (x * ((1 + x) - β)) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
      have e1 : 4 * (1 / ((1 + x) - β)) * (x * ((1 + x) - β)) = 4 * x := by field_simp
      have e2 : (31 / 8) * (1 / x) * (x * ((1 + x) - β)) = (31 / 8) * ((1 + x) - β) := by
        field_simp
      nlinarith [h1, e1.le, e1.ge, e2.le, e2.ge, hxpos, hYpos]
  -- contradiction with the region hypothesis
  have hc_le : (1 / (1024 * A)) / Lγ ≤ x / 64 := by
    rw [hxdef]
    have h1 : (1 / (1024 * A)) / Lγ ≤ (1 / (1024 * A)) / (ℓ / 16) := by
      apply div_le_div_of_nonneg_left (by positivity)
      · linarith [hℓpos]
      · linarith [hℓ_le]
    have h2 : (1 / (1024 * A)) / (ℓ / 16) = (1 / (A * ℓ)) / 64 := by field_simp; ring
    rw [h2] at h1
    linarith [h1]
  have hδ_lt : 1 - β < (1 / (1024 * A)) / Lγ := by
    have := hreg'
    linarith [this]
  linarith [hδx, hc_le, hδ_lt]

end

end Work.FIArea6Hecke.R
