import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Zeta.dirichletPoly_meanValue_integral_corrected
import Submission.Work.ZeroDensity.Ingham.MKIntervalMeanSquare

/-!
# The mean square of the truncated Möbius polynomial on the *symmetric* interval `[-T, T]`

The one-sided Montgomery mean value bound for
`M_K(s) = Σ_{n ≤ K} μ(n) n^{-s}`, namely
`∫_0^T ‖M_K(1/2 + it)‖² dt ≤ C (T + K log(K+2)) log(K+2)`
(`Submission.Work.ZeroDensity.Ingham.MKIntervalMeanSquare`), is turned here into the estimate over
the symmetric interval `[-T, T]` requested by the zero detector:

`∫_{-T}^{T} ‖M_K(1/2 + it)‖² dt ≤ C (T + K) (log(K+2))²`  for `K, T ≥ 1`.

The two ingredients are

* the critical-line integrand `t ↦ ‖M_K(1/2 + it)‖²` is **even**: `M_K` has real coefficients and
  `conj (M_K s) = M_K (conj s)`, so `‖M_K(1/2 - it)‖ = ‖conj (M_K(1/2 + it))‖ = ‖M_K(1/2 + it)‖`;
* hence the symmetric integral is twice the one-sided integral,

`∫_{-T}^{T} f = ∫_{-T}^{0} f + ∫_0^T f = 2 ∫_0^T f`.

Since `log(K+2) ≥ 1` for `K ≥ 1`, the bound `T + K log(K+2) ≤ (T + K) log(K+2)` upgrades the
one-sided constant to the required shape (with `C` replaced by `2C`).
-/

open scoped BigOperators
open MeasureTheory

namespace Work.ZeroDensity.Ingham.zetaDetectorBig

/-- **Termwise conjugation.**  For `n ≥ 1` and any `s`,
`μ(n) n^{-conj s} = conj (μ(n) n^{-s})`: the coefficient `μ(n)` is real and the base `n` is a
positive real, so `Complex.conj_cpow` applies (`(n : ℂ).arg = 0 ≠ π`). -/
private lemma mk_term_conj (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(starRingEnd ℂ s))
      = (starRingEnd ℂ) ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) := by
  rw [map_mul]
  have hμ : (starRingEnd ℂ) (ArithmeticFunction.moebius n : ℂ)
      = (ArithmeticFunction.moebius n : ℂ) := by simp
  rw [hμ]
  congr 1
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    have h2 : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [h2, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact fun h => Real.pi_ne_zero h.symm
  have h := Complex.conj_cpow (n : ℂ) (-(starRingEnd ℂ s)) harg
  rw [Complex.conj_natCast] at h
  have h2 : (starRingEnd ℂ) (-(starRingEnd ℂ s)) = -s := by simp
  rw [h2] at h
  exact h

/-- **The truncated Möbius polynomial commutes with complex conjugation**,
`M_K(conj s) = conj (M_K s)`, because all its coefficients `μ(n)` are real. -/
private lemma MK_conj (K : ℕ) (s : ℂ) :
    Work.ZeroDensity.Ingham.MK K (starRingEnd ℂ s)
      = (starRingEnd ℂ) (Work.ZeroDensity.Ingham.MK K s) := by
  simp only [Work.ZeroDensity.Ingham.MK]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  exact mk_term_conj n (Finset.mem_Icc.mp hn).1 s

/-- **The critical-line integrand is even**: `‖M_K(1/2 - it)‖ = ‖M_K(1/2 + it)‖`. -/
private lemma mkLine_norm_even (K : ℕ) (t : ℝ) :
    ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖
      = ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have h : ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [Complex.conj_ofReal]
  calc ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖
      = ‖Work.ZeroDensity.Ingham.MK K
          ((starRingEnd ℂ) ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖ := by rw [h]
    _ = ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [MK_conj, Complex.norm_conj]

/-- The squared critical-line integrand is even. -/
private lemma mkLine_even (K : ℕ) (t : ℝ) :
    ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ^ 2
      = ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  rw [mkLine_norm_even K t]

/-- `M_K` is continuous on the critical line, being a finite sum of the continuous functions
`s ↦ (n : ℂ)^{-s}` (`n ≥ 1`). -/
private lemma continuous_MK_line (K : ℕ) :
    Continuous fun t : ℝ => Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  change Continuous (fun t : ℝ => ∑ n ∈ Finset.Icc 1 K,
      (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)))
  refine continuous_finsetSum _ (fun n hn => ?_)
  refine Continuous.mul continuous_const ?_
  refine Continuous.const_cpow ?_ (Or.inl ?_)
  · fun_prop
  · have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)

/-- The squared norm of `M_K` on the critical line is continuous. -/
private lemma mkLine_continuous (K : ℕ) :
    Continuous fun t : ℝ => ‖Work.ZeroDensity.Ingham.MK K
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
  (continuous_MK_line K).norm.pow 2

theorem mkSecondMomentSym :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (T : ℝ), 1 ≤ K → 1 ≤ T →
      (∫ t in (-T)..T, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        ≤ C * (T + (K : ℝ)) * (Real.log ((K : ℝ) + 2)) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hmom⟩ := Work.ZeroDensity.Ingham.MKIntervalMeanSquare
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro K T hK hT
  -- `log (K+2) ≥ 1` for `K ≥ 1`, so `T + K log(K+2) ≤ (T+K) log(K+2)`.
  have hK3 : (3 : ℝ) ≤ (K : ℝ) + 2 := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log ((K : ℝ) + 2) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
      exact le_of_lt Real.exp_one_lt_three
    exact le_trans h3 (Real.log_le_log (by norm_num) hK3)
  have hlog0 : (0 : ℝ) ≤ Real.log ((K : ℝ) + 2) := le_trans zero_le_one hlog1
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hkey : T + (K : ℝ) * Real.log ((K : ℝ) + 2)
      ≤ (T + (K : ℝ)) * Real.log ((K : ℝ) + 2) := by
    have hTL : T ≤ T * Real.log ((K : ℝ) + 2) := by
      simpa using mul_le_mul_of_nonneg_left hlog1 hT0
    nlinarith [hTL]
  have hmul : (T + (K : ℝ) * Real.log ((K : ℝ) + 2)) * Real.log ((K : ℝ) + 2)
      ≤ (T + (K : ℝ)) * (Real.log ((K : ℝ) + 2)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hkey hlog0
    nlinarith [h]
  -- Evenness of the integrand reduces `[-T, T]` to twice `[0, T]`.
  let F : ℝ → ℝ := fun t => ‖Work.ZeroDensity.Ingham.MK K
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
  have hFcont : Continuous F := mkLine_continuous K
  have hFeven : ∀ t, F (-t) = F t := fun t => mkLine_even K t
  have hleft : IntervalIntegrable F volume (-T) 0 := hFcont.intervalIntegrable _ _
  have hright : IntervalIntegrable F volume 0 T := hFcont.intervalIntegrable _ _
  have hneg : (∫ x in (-T)..0, F x) = (∫ x in 0..T, F x) := by
    have heq : (∫ x in (-T)..0, F (-x)) = (∫ x in (-T)..0, F x) :=
      intervalIntegral.integral_congr (fun x _ => hFeven x)
    rw [← heq, intervalIntegral.integral_comp_neg (a := -T) (b := 0) F]
    simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hsymF : (∫ x in (-T)..T, F x) = 2 * (∫ x in 0..T, F x) := by
    rw [← hsum, hneg]; ring
  have hsym : (∫ t in (-T)..T, ‖Work.ZeroDensity.Ingham.MK K
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = 2 * (∫ t in (0 : ℝ)..T, ‖Work.ZeroDensity.Ingham.MK K
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := hsymF
  have hb : (∫ t in (0 : ℝ)..T, ‖Work.ZeroDensity.Ingham.MK K
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ C₀ * ((T + (K : ℝ) * Real.log ((K : ℝ) + 2)) * Real.log ((K : ℝ) + 2)) :=
    hmom K T hK hT
  calc (∫ t in (-T)..T, ‖Work.ZeroDensity.Ingham.MK K
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = 2 * (∫ t in (0 : ℝ)..T, ‖Work.ZeroDensity.Ingham.MK K
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := hsym
    _ ≤ 2 * (C₀ * ((T + (K : ℝ) * Real.log ((K : ℝ) + 2))
          * Real.log ((K : ℝ) + 2))) := by linarith
    _ ≤ 2 * (C₀ * ((T + (K : ℝ)) * (Real.log ((K : ℝ) + 2)) ^ 2)) := by
        have h := mul_le_mul_of_nonneg_left hmul (le_of_lt hC₀pos)
        linarith
    _ = 2 * C₀ * (T + (K : ℝ)) * (Real.log ((K : ℝ) + 2)) ^ 2 := by ring

end Work.ZeroDensity.Ingham.zetaDetectorBig
