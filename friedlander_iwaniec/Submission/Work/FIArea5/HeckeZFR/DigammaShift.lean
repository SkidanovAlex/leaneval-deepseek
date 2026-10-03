/-
# `Submission.Work.FIArea5.HeckeZFR.DigammaShift`

A **digamma bound with no restriction on the real part**: for `x ≥ 1/2`,

  `Re ψ(x + iγ) ≤ log(2 + |γ|) + 2 log(4x) + 6`.

The commons supply `digamma_mid_strip_le`, valid only for `1/2 ≤ x ≤ 8`; the shift
`ψ(w + k) = ψ w + Σ_{j<k} 1/(w+j)` (from `Complex.digamma_apply_add_one`) reduces a large `x` to
the strip `[1/2, 3/2]` at the cost of a harmonic sum, which is bounded by the telescoping
`2 Σ_j log((j+3/2)/(j+1/2)) = 2 log(2k+1)` (via `Real.le_log_one_add_of_nonneg`).

This is the estimate that converts `Λ'/Λ(2+iγ) = log(4d/π) + ψ(2+iγ+m/2) + L'/L(2+iγ,ψ)` into a
`O(log(4d) + log(m+|γ|+3))` bound, uniformly in `m`.
-/
import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Complex Finset
open scoped Real

noncomputable section

/-- The harmonic sum over half-integers, bounded telescopically. -/
lemma sum_inv_half_le (k : ℕ) :
    ∑ j ∈ Finset.range k, (1 : ℝ) / ((j : ℝ) + 1 / 2) ≤ 2 * Real.log (2 * k + 1) := by
  have hterm : ∀ j : ℕ,
      (1 : ℝ) / ((j : ℝ) + 1 / 2)
        ≤ 2 * (Real.log ((j : ℝ) + 3 / 2) - Real.log ((j : ℝ) + 1 / 2)) := by
    intro j
    have hpos : (0 : ℝ) < (j : ℝ) + 1 / 2 := by positivity
    have h1 : 2 * ((1 : ℝ) / ((j : ℝ) + 1 / 2)) / ((1 : ℝ) / ((j : ℝ) + 1 / 2) + 2)
        ≤ Real.log (1 + (1 : ℝ) / ((j : ℝ) + 1 / 2)) :=
      Real.le_log_one_add_of_nonneg (by positivity)
    have h2 : 2 * ((1 : ℝ) / ((j : ℝ) + 1 / 2)) / ((1 : ℝ) / ((j : ℝ) + 1 / 2) + 2)
        = 1 / ((j : ℝ) + 1) := by
      field_simp; ring
    rw [h2] at h1
    have h3 : Real.log (1 + (1 : ℝ) / ((j : ℝ) + 1 / 2))
        = Real.log ((j : ℝ) + 3 / 2) - Real.log ((j : ℝ) + 1 / 2) := by
      rw [show 1 + (1 : ℝ) / ((j : ℝ) + 1 / 2) = ((j:ℝ) + 3/2) / ((j:ℝ) + 1/2) from by
        field_simp; ring]
      rw [Real.log_div (by positivity) (by positivity)]
    rw [h3] at h1
    have h4 : (1 : ℝ) / ((j : ℝ) + 1 / 2) ≤ 2 * (1 / ((j : ℝ) + 1)) := by
      have hden : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [div_le_iff₀ hpos,
        show (2 : ℝ) * (1 / ((j : ℝ) + 1)) * ((j : ℝ) + 1 / 2)
            = 2 * ((j : ℝ) + 1 / 2) / ((j : ℝ) + 1) from by ring,
        le_div_iff₀ hden]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith
    linarith
  refine (Finset.sum_le_sum (fun j _ => hterm j)).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  have hcongr : ∑ i ∈ Finset.range k, (Real.log ((i : ℝ) + 3 / 2) - Real.log ((i : ℝ) + 1 / 2))
      = ∑ i ∈ Finset.range k,
          ((fun j : ℕ => Real.log ((j : ℝ) + 1 / 2)) (i + 1)
            - (fun j : ℕ => Real.log ((j : ℝ) + 1 / 2)) i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    ring_nf
  rw [hcongr, Finset.sum_range_sub (fun j : ℕ => Real.log ((j : ℝ) + 1 / 2))]
  have h2 : Real.log (((0 : ℕ) : ℝ) + 1 / 2) = -Real.log 2 := by
    rw [show ((0:ℕ):ℝ) + 1/2 = (1:ℝ)/2 from by norm_num, Real.log_div one_ne_zero (by norm_num)]
    norm_num
  rw [h2]
  have h3 : Real.log ((k : ℝ) + 1 / 2) + Real.log 2 = Real.log (2 * k + 1) := by
    rw [← Real.log_mul (by positivity) (by norm_num : (2:ℝ) ≠ 0)]
    congr 1; ring
  linarith [h3]

/-- The recurrence, iterated: `ψ(w + k) = ψ w + Σ_{j<k} 1/(w+j)`. -/
lemma digamma_add_nat {w : ℂ} {k : ℕ} (hw : ∀ j : ℕ, 0 < (w + (j : ℂ)).re) :
    Complex.digamma (w + (k : ℂ))
      = Complex.digamma w + ∑ j ∈ Finset.range k, (w + (j : ℂ))⁻¹ := by
  have hne : ∀ (j m : ℕ), w + (j : ℂ) ≠ - (m : ℂ) := by
    intro j m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have := hw j
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re] at this
    linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : Complex.digamma (w + (k : ℂ) + 1) = Complex.digamma (w + (k : ℂ)) + (w + (k : ℂ))⁻¹ :=
      Complex.digamma_apply_add_one (w + (k : ℂ)) (fun m => hne k m)
    rw [show w + ((k + 1 : ℕ) : ℂ) = w + (k : ℂ) + 1 from by push_cast; ring, hstep]
    rw [ih, Finset.sum_range_succ]
    ring

/-- **Digamma bound with no upper restriction on the real part.** -/
theorem digamma_re_le_of_half_le (x γ : ℝ) (hx : (1 : ℝ) / 2 ≤ x) :
    (Complex.digamma ((x : ℂ) + (γ : ℂ) * I)).re ≤
      Real.log (2 + |γ|) + 2 * Real.log (4 * x) + 6 := by
  set k : ℕ := ⌊x - 1 / 2⌋₊ with hk
  have hk1 : (k : ℝ) ≤ x - 1 / 2 := Nat.floor_le (by linarith)
  have hk2 : x - 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one (x - 1 / 2)
  set x' : ℝ := x - (k : ℝ) with hx'
  have hx'1 : (1 : ℝ) / 2 ≤ x' := by rw [hx']; linarith
  have hx'2 : x' < 3 / 2 := by rw [hx']; linarith
  have hre : ∀ j : ℕ, ((x' : ℂ) + (γ : ℂ) * I + ((j : ℕ) : ℂ)).re = x' + (j : ℝ) := by
    intro j; simp
  have hw : ∀ j : ℕ, 0 < (((x' : ℂ) + (γ : ℂ) * I) + ((j : ℕ) : ℂ)).re := by
    intro j; rw [hre j]; have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j; linarith
  have hzsplit : (x : ℂ) + (γ : ℂ) * I = ((x' : ℂ) + (γ : ℂ) * I) + (k : ℂ) := by
    rw [hx']; push_cast; ring
  rw [hzsplit, digamma_add_nat hw, Complex.add_re]
  have hmid : (Complex.digamma ((x' : ℂ) + (γ : ℂ) * I)).re ≤ Real.log (2 + |γ|) + 2 :=
    le_trans (Complex.re_le_norm _) (Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le x' γ hx'1 (by linarith))
  have hsum : (∑ j ∈ Finset.range k, (((x' : ℂ) + (γ : ℂ) * I) + ((j : ℕ) : ℂ))⁻¹).re
      ≤ 2 * Real.log (4 * x) := by
    have hpt : ∀ j ∈ Finset.range k,
        ((((x' : ℂ) + (γ : ℂ) * I) + ((j : ℕ) : ℂ))⁻¹).re
          ≤ (1 : ℝ) / ((j : ℝ) + 1 / 2) := by
      intro j _
      have h1 : ((((x' : ℂ) + (γ : ℂ) * I) + ((j : ℕ) : ℂ))⁻¹).re
          = (x' + (j : ℝ)) / ((x' + (j:ℝ)) ^ 2 + γ ^ 2) := by
        rw [Complex.inv_re, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
          Complex.natCast_im, mul_zero, add_zero, zero_mul]
        ring
      rw [h1]
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hnum : (0 : ℝ) < x' + (j : ℝ) := by linarith
      have hden : (0 : ℝ) < (x' + (j : ℝ)) ^ 2 + γ ^ 2 := by positivity
      rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < (j : ℝ) + 1 / 2)]
      nlinarith [sq_nonneg γ, hnum, hj0, hx'1]
    have hsum0 : (∑ j ∈ Finset.range k, (((x' : ℂ) + (γ : ℂ) * I) + ((j : ℕ) : ℂ))⁻¹).re
        = ∑ j ∈ Finset.range k, ((((x' : ℂ) + (γ : ℂ) * I) + ((j : ℕ) : ℂ))⁻¹).re :=
      map_sum (Complex.reCLM : ℂ →+ ℝ) _ _
    rw [hsum0]
    refine (Finset.sum_le_sum hpt).trans ?_
    refine (sum_inv_half_le k).trans ?_
    have hk4 : (2:ℝ) * k + 1 ≤ 4 * x := by
      have hkx : (k : ℝ) ≤ x := by linarith
      linarith
    have hspos : (0:ℝ) < 2 * (k:ℝ) + 1 := by positivity
    have hx4 : (0:ℝ) < 4 * x := by linarith
    have := Real.log_le_log hspos hk4
    linarith
  linarith [hmid, hsum]

end

end Work.FIArea5.S16Hecke
