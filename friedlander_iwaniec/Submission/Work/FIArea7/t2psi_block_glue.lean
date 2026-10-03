/-
# `Work.FIArea7.t2psi_block_glue` — small shared lemmas for the block bilinear estimate

These are the elementary facts about the factors `(n)^{it}`, the Möbius function and
integrability that the proof of `Work.FIArea7.t2psi_block_bilinear_gen` (and the two lemmas it
is assembled from, the integral representation and the pointwise bracket bound) need.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs

set_option autoImplicit false

namespace Work.FIArea7

open MeasureTheory

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `‖n^{it}‖ = 1` for a positive integer `n`. -/
lemma norm_natCast_cpow_I (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    ‖(m : ℂ) ^ (t * Complex.I)‖ = 1 := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcast : (m : ℂ) = ((m : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hm']
  have hre : (t * Complex.I).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.rpow_zero]

/-- `t ↦ n^{it}` is continuous for a positive integer `n`. -/
lemma continuous_natCast_cpow_I (m : ℕ) (hm : 1 ≤ m) :
    Continuous fun t : ℝ => (m : ℂ) ^ (t * Complex.I) := by
  have hm0 : (m : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : m ≠ 0)
  exact Continuous.const_cpow (by fun_prop) (Or.inl hm0)

/-- `t ↦ h t · n^{it}` is integrable when `t ↦ h t` is. -/
lemma integrable_h_mul_cpow (h : ℝ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hint : MeasureTheory.Integrable (fun t : ℝ => (h t : ℂ))) :
    MeasureTheory.Integrable (fun t : ℝ => (h t : ℂ) * (m : ℂ) ^ (t * Complex.I)) := by
  have hfc : MeasureTheory.Integrable
      (fun t : ℝ => (m : ℂ) ^ (t * Complex.I) * (h t : ℂ)) := by
    refine MeasureTheory.Integrable.bdd_mul (c := 1) hint
      (Continuous.aestronglyMeasurable (continuous_natCast_cpow_I m hm)) ?_
    filter_upwards with t
    rw [norm_natCast_cpow_I m hm t]
  exact hfc.congr (Filter.Eventually.of_forall fun t => by ring)

/-- `(m n)^{it} = m^{it} · n^{it}` for natural numbers. -/
lemma natCast_cpow_I_mul (m n : ℕ) (t : ℝ) :
    ((m * n : ℕ) : ℂ) ^ (t * Complex.I)
      = (m : ℂ) ^ (t * Complex.I) * (n : ℂ) ^ (t * Complex.I) := by
  rw [Nat.cast_mul, ← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n,
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- `‖μ n‖ ≤ 1` for the Möbius function. -/
lemma norm_moebius_cast_le_one (m : ℕ) :
    ‖((ArithmeticFunction.moebius m : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

end

end Work.FIArea7
