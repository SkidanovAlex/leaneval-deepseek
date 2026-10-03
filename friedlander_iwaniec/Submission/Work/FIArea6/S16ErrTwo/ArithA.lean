import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.Decomp
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.NumberTheory.PrimeCounting
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.JointCount.card_filter_le_le_pieces
import Submission.Work.FIArea3.JointCount.card_jointPieceLat_le
import Submission.Work.FIArea3.JointCount.index_jointPieceLat
import Submission.Work.FIArea3.JointCount.maxPieceFinset_card_le
import Submission.Work.FIArea3.JointCount.SStructure
import Submission.Work.FIArea3.JointCount.splitPin
import Submission.Work.FIArea3.JointCount.inertPin
import Submission.Work.FIArea3.JointCount.twoPin
import Submission.Commons.NumberTheory.Diophantine.mertens_three_mod_four_prod_bound
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log
import Submission.Commons.NumberTheory.Diophantine.prime_three_mod_four_dvd_sq_add_sq
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
import Submission.Work.FIArea3.JointCount.countDefs
import Submission.Work.FIArea3.JointCount.maxPieceDefs
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred
import Submission.Commons.NumberTheory.Divisors.sum_filter_dvd_reindex
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_le_log_log_add
import Submission.Commons.NumberTheory.DivisorSum.sum_tau_pow_le
import Submission.Work.FIArea6.four_mul_le_Pz

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary sums -/

/-- `Σ_{d ≤ X} φ(d)/d ≤ X`. -/
lemma totient_div_sum_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) ≤ (X : ℝ) := by
  calc ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
      ≤ ∑ _d ∈ Finset.Icc 1 X, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rcases Finset.mem_Icc.mp hd with ⟨h1, -⟩
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast h1
        rw [div_le_one hd0]
        exact_mod_cast Nat.totient_le d
    _ = (X : ℝ) := by simp

/-! ## 2. The square mass of a round-6 coefficient -/

/-- On the support `‖βz‖ ≤ τ(gnorm z)`: `βz = (q·p)·μ·γ` with `|q|,|p|,|μ| ≤ 1` and
`|γ| ≤ τ`. -/
lemma beta_norm_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hβdef⟩ := hβ
  by_cases hc : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
      ∧ Work.FITop4.IsAxisFree Pa z
  · rw [hβdef z, if_pos hc]
    have h1 : ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
      calc q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
            mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
        _ = 1 := by ring
    have h2 : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := Work.FIPlan.gnorm z)
      have h1' : ‖((ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast h
      rwa [Complex.ofReal_intCast] at h1'
    have h3 : ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
        ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.FITop3.abs_gammaTrunc_le Pa.C (Work.FIPlan.gnorm z)
    calc ‖((q _ * p _ : ℝ) : ℂ) * (ArithmeticFunction.moebius _ : ℂ)
            * (Work.FIPlan.gammaTrunc _ _ : ℂ)‖
        = ‖((q _ * p _ : ℝ) : ℂ)‖ * ‖(ArithmeticFunction.moebius _ : ℂ)‖
            * ‖(Work.FIPlan.gammaTrunc _ _ : ℂ)‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _)
            (by positivity)
      _ = (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
  · rw [hβdef z, if_neg hc] at hz
    exact absurd rfl hz

/-! ## 3. The threshold -/

/-- The threshold of the §16 error analysis. -/
def X0 : ℝ :=
  Real.exp (Real.exp (2 * Work.FITop4.nuU + 100) * (1024 * (3 * Work.FITop4.nuU + 50) ^ (2 : ℕ) + 1))

lemma X0_pos : 0 < X0 := Real.exp_pos _

lemma nuU_nonneg : (0 : ℝ) ≤ Work.FITop4.nuU := le_of_lt Work.FIArea6.nuU_pos

/-- The threshold facts: `log log x ≥ 2ν+100`, `√log x ≥ 32(3ν+50)`, `log log x ≤ 2√log x`. -/
lemma threshold_facts (Pa : Work.FITop.Params) (hx : X0 ≤ (Pa.x : ℝ)) :
    2 * Work.FITop4.nuU + 100 ≤ Real.log (Real.log (Pa.x : ℝ)) ∧
    32 * (3 * Work.FITop4.nuU + 50) ≤ Real.sqrt (Real.log (Pa.x : ℝ)) ∧
    Real.log (Real.log (Pa.x : ℝ)) ≤ 2 * Real.sqrt (Real.log (Pa.x : ℝ)) ∧
    1024 * (3 * Work.FITop4.nuU + 50) ^ (2 : ℕ) + 1 ≤ Real.log (Pa.x : ℝ) ∧
    1 ≤ Real.log (Pa.x : ℝ) ∧ (1 : ℝ) ≤ (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hexp1 : (0 : ℝ) < Real.exp (2 * Work.FITop4.nuU + 100) := Real.exp_pos _
  have hfac1 : (1 : ℝ) ≤ 1024 * (3 * Work.FITop4.nuU + 50) ^ (2 : ℕ) + 1 := by
    nlinarith [sq_nonneg (3 * Work.FITop4.nuU + 50), nuU_nonneg]
  have hlogx : Real.exp (2 * Work.FITop4.nuU + 100) * (1024 * (3 * Work.FITop4.nuU + 50) ^ (2 : ℕ) + 1)
      ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log X0_pos hx
    rwa [X0, Real.log_exp] at h
  have hlogx1 : Real.exp (2 * Work.FITop4.nuU + 100) ≤ Real.log (Pa.x : ℝ) :=
    le_trans (le_mul_of_one_le_right hexp1.le hfac1) hlogx
  have hlogx2 : 1024 * (3 * Work.FITop4.nuU + 50) ^ (2 : ℕ) + 1 ≤ Real.log (Pa.x : ℝ) :=
    le_trans (le_mul_of_one_le_left (by linarith) (Real.one_le_exp (by linarith [nuU_nonneg]))) hlogx
  have hloglog : 2 * Work.FITop4.nuU + 100 ≤ Real.log (Real.log (Pa.x : ℝ)) := by
    have h := Real.log_le_log hexp1 hlogx1
    rwa [Real.log_exp] at h
  have hlogxpos : 0 < Real.log (Pa.x : ℝ) := by linarith [hlogx2]
  have hsqrt : 32 * (3 * Work.FITop4.nuU + 50) ≤ Real.sqrt (Real.log (Pa.x : ℝ)) := by
    have h2 : (32 * (3 * Work.FITop4.nuU + 50)) ^ (2 : ℕ) ≤ Real.log (Pa.x : ℝ) := by
      nlinarith [hlogx2]
    have h3 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (by linarith [nuU_nonneg])] at h3
  have hloglog_le : Real.log (Real.log (Pa.x : ℝ)) ≤ 2 * Real.sqrt (Real.log (Pa.x : ℝ)) := by
    have h := Real.log_le_rpow_div hlogxpos.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.rpow_div_two_eq_sqrt 1 hlogxpos.le, Real.rpow_one] at h
    have h2 : Real.sqrt (Real.log (Pa.x : ℝ)) / (1 / 2)
        = 2 * Real.sqrt (Real.log (Pa.x : ℝ)) := by ring
    linarith
  exact ⟨hloglog, hsqrt, hloglog_le, hlogx2, by linarith [hlogx2], by linarith⟩

end

end Work.FIArea6.S16ErrTwo

#check @Complex.ofReal_intCast
#check @Real.rpow_div_two_eq_sqrt
#check @Complex.norm_intCast
