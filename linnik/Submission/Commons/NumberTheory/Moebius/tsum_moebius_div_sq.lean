import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

set_option maxHeartbeats 1000000

open scoped LSeries.notation

namespace Commons.NumberTheory.Moebius

/-- The Möbius function's Dirichlet series at `s = 2` sums to `1 / ζ(2) = 6 / π ^ 2`. -/
theorem tsum_moebius_div_sq :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
  have h2 : (1 : ℂ).re < (2 : ℂ).re := by norm_num
  have hmul : LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) (2 : ℂ)
      * LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (2 : ℂ) = 1 :=
    ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius h2
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta h2] at hmul
  have hmu : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (2 : ℂ)
      = (6 / (Real.pi : ℂ) ^ 2 : ℂ) := by
    rw [eq_inv_of_mul_eq_one_right hmul, riemannZeta_two]
    norm_num
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr h2
  have hhas : HasSum (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (2 : ℂ))
      (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (2 : ℂ)) := hsum.hasSum
  let f : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
  have hterm : ∀ n : ℕ,
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (2 : ℂ) n = (f n : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp [LSeries.term, ArithmeticFunction.map_zero, f]
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_two]
      simp only [f]
      norm_cast
  have htarget : (6 / (Real.pi : ℂ) ^ 2 : ℂ) = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hhas' : HasSum (fun n : ℕ => (f n : ℂ)) ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    have := hhas
    rw [hmu, htarget] at this
    exact HasSum.congr_fun this (fun n => (hterm n).symm)
  have hreal : HasSum f (6 / Real.pi ^ 2) := Complex.hasSum_ofReal.mp hhas'
  have hthis : (∑' n, f n) = 6 / Real.pi ^ 2 := hreal.tsum_eq
  simpa only [f] using hthis

end Commons.NumberTheory.Moebius