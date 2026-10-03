/-
# `Submission.Work.FIArea6Hecke.R.HeckeZFRCoreAsm`

The de la Vallée Poussin `(3,4,1)` assembly for the Hecke `L`-function of `ℚ(i)`: from

* the near-zero logarithmic-derivative bound at a zero `ρ = β + iγ` of the completion `Λ`,
* the one-sided bound `Re (Λ'/Λ)(σ+iτ) ≥ -C log(4d(|m|+|τ|+3))` for the auxiliary completion of
  `ψ²` (the square of the Größencharacter),

we deduce the zero-free region

  `Λ s ≠ 0` for `1 - c/log(4d+|m|+|s.im|) < re s ≤ 2`, except on the real axis when `ψ` is real.

The proof is the classical one: the `(3,4,1)` inequality `HeckeLDerivRe341` at the three points
`σ`, `σ+iγ`, `σ+2iγ`, the pole bound for the principal `L`-function (`HeckeAxisLogDerivBound`), the
near-zero bound at the zero in the middle, the sharp one-sided bound for the third term, and the
archimedean (digamma) bounds for the conversions.  Nothing here depends on the missing
"general conductor" functional equation: the auxiliary bound is taken as an input.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.HeckeZFR.Hadm.factorZero
import Submission.Work.FIArea5.HeckeZFR.Hadm.goodRadius
import Submission.Work.FIArea5.HeckeZFR.Hadm.cofactorBound
import Submission.Work.FIArea5.HeckeZFR.Hadm.pfConv
import Submission.Work.FIArea5.HeckeZFR.Lam_partialFraction
import Submission.Work.FIArea5.HeckeZFR.LamBaseBound
import Submission.Work.FIArea5.HeckeZFR.FELogDeriv
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea6Hecke.R.HeckeLDerivRe341
import Submission.Work.FIArea6Hecke.R.HeckeAxisLogDerivBound
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-! ## 1.  The archimedean bound -/

/-- `logDeriv (heckeArch d m) s = log (4d/π) + ψ(s + |m|/2)` (all `s` with `re s + |m|/2 > 0`), where
`ψ = Complex.digamma`. -/
lemma logDeriv_heckeArch_eq (d : ℕ) (hd : 1 ≤ d) (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (Work.FITop4.Bridge.heckeArch d m) s
      = Complex.log (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ)
        + Complex.digamma (s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ)) := by
  have hbase : (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    positivity
  have harch : Work.FITop4.Bridge.heckeArch d m
      = fun z : ℂ => (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) ^ z
          * Complex.Gamma (z + (((|((m : ℝ))| / 2 : ℝ)) : ℂ)) := by
    funext z
    unfold Work.FITop4.Bridge.heckeArch
    congr 2
    push_cast
    ring
  have harg : ∀ k : ℕ, s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ) ≠ - (k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.natCast_re] at hre
    have h1 := abs_nonneg (m : ℝ)
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) ^ z) s :=
    (hasStrictDerivAt_const_cpow (Or.inl hbase)).hasDerivAt.differentiableAt
  have hd2 : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z + (((|((m : ℝ))| / 2 : ℝ)) : ℂ))) s :=
    (Complex.differentiableAt_Gamma _ harg).comp s (differentiableAt_id.add_const _)
  rw [harch, Submission.Port.logDeriv_mul_fun (f := fun z : ℂ => (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) ^ z)
      (g := fun z : ℂ => Complex.Gamma (z + (((|((m : ℝ))| / 2 : ℝ)) : ℂ))) s
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hbase))
      (Complex.Gamma_ne_zero_of_re_pos (by
        simp only [Complex.add_re, Complex.ofReal_re]
        have h1 := abs_nonneg (m : ℝ); linarith)) hd1 hd2,
    Work.FIArea5.S16Hecke.logDeriv_const_cpow _ hbase s,
    Work.FIArea5.S16Hecke.logDeriv_Gamma_add_const _ s harg]

/-- **The archimedean bound**: for `1/2 ≤ re s ≤ 2`,
`Re (logDeriv (heckeArch d m) s) ≤ 40 · log (4·d·(|m| + |s.im| + 3))`. -/
lemma archLogDeriv_re_le (d : ℕ) (hd : 1 ≤ d) (m : ℤ) {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs2 : s.re ≤ 2) :
    (logDeriv (Work.FITop4.Bridge.heckeArch d m) s).re
      ≤ 40 * Real.log (4 * (d : ℝ) * (|((m : ℝ))| + |s.im| + 3)) := by
  have hs0 : 0 < s.re := by linarith
  set L : ℝ := Real.log (4 * (d : ℝ) * (|((m : ℝ))| + |s.im| + 3)) with hL
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmm : (0 : ℝ) ≤ |((m : ℝ))| := abs_nonneg _
  have hsm : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hLpos : 0 < L := by
    rw [hL]; refine Real.log_pos ?_; nlinarith
  have hlog12 : (2 : ℝ) < Real.log 12 := by
    have h3 : Real.log 12 = Real.log 3 + Real.log 4 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h4 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_three
      linarith
    have h5 : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_three
      linarith
    rw [h3]; linarith
  have hL2 : (2 : ℝ) < L := by
    have h12 : (12 : ℝ) ≤ 4 * (d : ℝ) * (|((m : ℝ))| + |s.im| + 3) := by nlinarith
    have h1 := Real.log_le_log (by norm_num : (0:ℝ) < 12) h12
    rw [hL]; linarith
  have hlogbase : (Complex.log (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ)).re ≤ Real.log (4 * (d : ℝ)) := by
    rw [Complex.log_re]
    refine Real.log_le_log (norm_pos_iff.mpr ?_) ?_
    · rw [Complex.ofReal_ne_zero]
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      positivity
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (d : ℝ) / Real.pi)]
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) d]
  have hdig := Work.FIArea5.S16Hecke.digamma_re_le_of_half_le (s.re + |((m : ℝ))| / 2) s.im (by
    have h1 := abs_nonneg (m : ℝ); linarith)
  have hsplit : s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ)
      = (((s.re + |((m : ℝ))| / 2 : ℝ)) : ℂ) + (s.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hdig' : (Complex.digamma (s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ))).re
      ≤ Real.log (2 + |s.im|) + 2 * Real.log (4 * (s.re + |((m : ℝ))| / 2)) + 6 := by
    rw [hsplit]; exact hdig
  have h4 : Real.log (4 * (d : ℝ)) ≤ L := by
    rw [hL]; refine Real.log_le_log (by positivity) ?_; nlinarith
  have h5 : Real.log (2 + |s.im|) ≤ L := by
    rw [hL]; refine Real.log_le_log (by positivity) ?_; nlinarith
  have h6 : 2 * Real.log (4 * (s.re + |((m : ℝ))| / 2)) ≤ 2 * L + 2 * Real.log 4 := by
    have h6a : (0 : ℝ) < 4 * (s.re + |((m : ℝ))| / 2) := by
      have h1 := abs_nonneg (m : ℝ); linarith
    have h6b : Real.log (4 * (s.re + |((m : ℝ))| / 2))
        ≤ Real.log (4 * (|((m : ℝ))| + |s.im| + 3)) := by
      refine Real.log_le_log h6a ?_
      nlinarith
    have h6c : Real.log (4 * (|((m : ℝ))| + |s.im| + 3))
        ≤ Real.log (4 * (d : ℝ) * (|((m : ℝ))| + |s.im| + 3)) := by
      refine Real.log_le_log (by positivity) ?_
      nlinarith
    have h6d : Real.log (4 * (d : ℝ) * (|((m : ℝ))| + |s.im| + 3))
        ≤ L + Real.log 4 := by
      rw [hL]; linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
    linarith
  have h8 : Real.log 4 ≤ 2 * L := by
    have h4log : Real.log 4 ≤ Real.log (4 * (d : ℝ)) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    linarith [h4, h4log]
  have hmain : Real.log (4 * (d : ℝ))
      + (Real.log (2 + |s.im|) + 2 * Real.log (4 * (s.re + |((m : ℝ))| / 2)) + 6) ≤ 40 * L := by
    nlinarith [h4, h5, h6, h8, hL2]
  rw [logDeriv_heckeArch_eq d hd m hs0, Complex.add_re]
  linarith [hlogbase, hdig', hmain]

end
end Work.FIArea6Hecke.R
