import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.LocalConstancy.Bump

/-!
# Vocabulary for the locality lemma for smoothed Dirichlet polynomials (GM Lemma 11.3)

GM Lemma 11.3 is proved by writing the smoothed polynomial
`D(t) = Σ_{n∈[N,2N]} w(n/N) b_n n^{it}` as the average of `D` against the Fourier transform of a
flat-top bump (the `PsiBump` of `Bump.lean`, which is `1` on `[0,1]` and has a rapidly decaying
Fourier transform), and then restricting the averaging variable to `|ξ| ≤ K`.

This module adds the piece of vocabulary specific to Lemma 11.3: the *untwisted* Dirichlet
polynomial `dtp`, obtained from `smoothedPoly` by replacing `n^{it}` by `(n/N)^{it}`.  Its
advantage is that the frequencies are `dlog N n = log (n/N) / (2π) ∈ [0,1]`, independently of `N`
(for `N ≤ n ≤ 2N`), so that the *fixed* bump `PsiBump` applies.
-/

namespace Work.GM.Energy.LocalConstancy

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

/-- The frequency of the `n`-th term of the untwisted polynomial: `dlog N n = log (n/N)/(2π)`. -/
noncomputable def dlog (N n : ℕ) : ℝ := Real.log ((n : ℝ) / (N : ℝ)) / (2 * Real.pi)

/-- For a positive base, the complex power `x^{iτ}` is the character `efun` at `τ log x / (2π)`. -/
lemma ofReal_cpow_pureImag_eq_efun {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    ((x : ℂ) ^ (Complex.I * (τ : ℂ))) = efun (τ * (Real.log x / (2 * Real.pi))) := by
  rw [Complex.cpow_def_of_ne_zero (by simpa using hx.ne'), ← Complex.ofReal_log hx.le]
  unfold efun
  congr 1
  push_cast
  field_simp

/-- `dlog N n ∈ [0,1]` when `N ≥ 1` and `N ≤ n ≤ 2N`.  This is exactly what makes the fixed
flat-top bump `PsiBump` (equal to `1` on `[0,1]`) applicable to the terms of `dtp`. -/
lemma dlog_mem (N n : ℕ) (hN : 1 ≤ N) (hn : n ∈ Finset.Icc N (2 * N)) :
    dlog N n ∈ Set.Icc (0 : ℝ) 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : n ≤ 2 * N := (Finset.mem_Icc.mp hn).2
  have hNn : N ≤ n := (Finset.mem_Icc.mp hn).1
  have hn1 : (1 : ℝ) ≤ n := by
    have : (1 : ℕ) ≤ n := le_trans hN hNn
    exact_mod_cast this
  rw [dlog]
  constructor
  · apply div_nonneg
    · apply Real.log_nonneg
      rw [le_div_iff₀ hNpos, one_mul]
      exact_mod_cast hNn
    · positivity
  · rw [div_le_one (by positivity)]
    have hn2 : ((n : ℝ) / (N : ℝ)) ≤ 2 := by
      rw [div_le_iff₀ hNpos]
      have h : (n : ℝ) ≤ (2 * N : ℕ) := by exact_mod_cast hle
      push_cast at h ⊢
      linarith
    calc Real.log ((n : ℝ) / (N : ℝ)) ≤ Real.log 2 :=
          Real.log_le_log (by positivity) hn2
      _ ≤ 2 * Real.pi := by
          have h1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
          nlinarith [Real.pi_gt_three]

/-- The "untwisted" Dirichlet polynomial `Σ_{n∈[N,2N]} w(n/N) b_n (n/N)^{it}`, written with the
character `efun` so that its dependence on `t` is manifestly smooth.  It is related to the
smoothed polynomial by `smoothedPoly N b t = N^{it} · dtp N b t`. -/
noncomputable def dtp (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N),
    ((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n * efun (t * dlog N n)

/-- The norm of the twisting factor `N^{it}` is `1` (for `N ≥ 1`). -/
lemma norm_cpow_I_mul (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    ‖((N : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN)]
  have h : (Complex.I * (t : ℂ)).re = 0 := by simp
  rw [h, Real.rpow_zero]

/-- `smoothedPoly N b t = N^{it} · dtp N b t`: the smoothed Dirichlet polynomial is the twist by
`N^{it}` of the untwisted one. -/
lemma smoothedPoly_eq_cpow_mul_dtp (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (t : ℝ) :
    Submission.LargeValues.smoothedPoly N b t
      = ((N : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * dtp N b t := by
  unfold Submission.LargeValues.smoothedPoly dtp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℕ) ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
  have hnn : (0 : ℝ) < (n : ℝ) / (N : ℝ) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    positivity
  have hcast : ((N : ℝ) : ℂ) * (((n : ℝ) / (N : ℝ) : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [← hcast, Complex.mul_cpow_ofReal_nonneg (by positivity) hnn.le (Complex.I * (t : ℂ)),
    ofReal_cpow_pureImag_eq_efun hnn t]
  simp only [dlog]
  ring

/-- The untwisted Dirichlet polynomial depends continuously on `t`. -/
lemma continuous_dtp (N : ℕ) (b : ℕ → ℂ) : Continuous (fun t : ℝ => dtp N b t) := by
  unfold dtp
  refine continuous_finset_sum _ fun n hn => ?_
  exact (continuous_const.mul continuous_const).mul
    (efun_continuous.comp (continuous_id.mul continuous_const))

/-- The trivial bound for the untwisted Dirichlet polynomial, with the bump bound `Cw`
(`|bumpW x| ≤ Cw`). -/
lemma norm_dtp_le (N : ℕ) (b : ℕ → ℂ) (Cw : ℝ)
    (hw : ∀ x, |Submission.LargeValues.bumpW x| ≤ Cw) (t : ℝ) :
    ‖dtp N b t‖ ≤ Cw * ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ := by
  have h1 : ‖dtp N b t‖ ≤
      ∑ n ∈ Finset.Icc N (2 * N),
        ‖((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n
          * efun (t * dlog N n)‖ := by
    unfold dtp
    exact norm_sum_le _ _
  refine h1.trans ?_
  calc ∑ n ∈ Finset.Icc N (2 * N),
        ‖((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n
          * efun (t * dlog N n)‖
      = ∑ n ∈ Finset.Icc N (2 * N),
          ‖((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ)‖ * ‖b n‖ := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [norm_mul, norm_mul, efun_norm, mul_one]
    _ ≤ ∑ n ∈ Finset.Icc N (2 * N), Cw * ‖b n‖ := by
        refine Finset.sum_le_sum fun n hn => ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (b n))
        refine (RCLike.norm_ofReal (Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)))).trans_le ?_
        exact hw ((n : ℝ) / (N : ℝ))
    _ = Cw * ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ := by rw [Finset.mul_sum]

end Work.GM.Energy.LocalConstancy
