import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Work.FIArea5.HeckeZFR.DigammaShift

namespace Work.FIArea6Hecke.R

open Complex
open scoped Topology

/-- Lower bound for the real part of the digamma function on the half-plane `re ≥ 1/2`: for
`x ≥ 1/2` and real `γ`, `Re ψ(x + iγ) ≥ -(log(2 + |γ|) + 8)`.  (Public counterpart of the private
`digamma_re_ge_of_half_le_R` in `R/baseLowerTwo.lean`: reduce to the strip `1/2 ≤ x' < 3/2` by the
recurrence `ψ(w+k) = ψ w + Σ_{j<k} 1/(w+j)`, whose added terms have nonnegative real part, then
apply `Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound`.) -/
lemma digamma_re_ge_of_half_le (x γ : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    -(Real.log (2 + |γ|) + 8) ≤ (Complex.digamma ((x : ℂ) + (γ : ℂ) * Complex.I)).re := by
  set k : ℕ := ⌊x - 1 / 2⌋₊ with hk
  have hk_le : (k : ℝ) ≤ x - 1 / 2 := Nat.floor_le (by linarith)
  have hk_lt : x - 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one (x - 1 / 2)
  set x' : ℝ := x - (k : ℝ) with hx'
  have hx'1 : (1 : ℝ) / 2 ≤ x' := by rw [hx']; linarith
  have hx'2 : x' < 3 / 2 := by rw [hx']; linarith
  have hsplit : (x : ℂ) + (γ : ℂ) * Complex.I
      = ((x' : ℂ) + (γ : ℂ) * Complex.I) + (k : ℂ) := by
    rw [hx']; push_cast; ring
  have hw : ∀ j : ℕ, 0 < (((x' : ℂ) + (γ : ℂ) * Complex.I) + (j : ℂ)).re := by
    intro j
    have h1 : (((x' : ℂ) + (γ : ℂ) * Complex.I) + (j : ℂ)).re = x' + (j : ℝ) := by simp
    rw [h1]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  rw [hsplit, Work.FIArea5.S16Hecke.digamma_add_nat hw, Complex.add_re]
  have hstrip : ‖Complex.digamma ((x' : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ Real.log (2 + |γ|) + 8 :=
    Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound x' γ (by linarith) (by linarith)
  have hmid : -(Real.log (2 + |γ|) + 8)
      ≤ (Complex.digamma ((x' : ℂ) + (γ : ℂ) * Complex.I)).re := by
    have h := (abs_le.mp
      (Complex.abs_re_le_norm (Complex.digamma ((x' : ℂ) + (γ : ℂ) * Complex.I)))).1
    linarith
  have hsum : 0 ≤ (∑ j ∈ Finset.range k, (((x' : ℂ) + (γ : ℂ) * Complex.I) + (j : ℂ))⁻¹).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg (fun j _ => ?_)
    have h1 : (((x' : ℂ) + (γ : ℂ) * Complex.I) + (j : ℂ)).re = x' + (j : ℝ) := by simp
    have h2 : (((x' : ℂ) + (γ : ℂ) * Complex.I) + (j : ℂ)).im = γ := by simp
    rw [Complex.inv_re, Complex.normSq_apply, h1, h2]
    apply div_nonneg
    · have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    · nlinarith [sq_nonneg (x' + (j : ℝ)), sq_nonneg γ]
  linarith

end Work.FIArea6Hecke.R
