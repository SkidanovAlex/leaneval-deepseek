/-
# `Submission.Work.FIArea6Hecke.R.continuousOn_thetaDual`

Continuity of the **dual theta function** `thetaDual d χ w = Σ_{ξ∈ℤ[i]} ĝ(ξ)·e^{-π|ξ|²w}` on
`(0,∞)` (with `ĝ(ξ) = gaussSum d chi ξ` the Gauss sum of `χ`), assuming only the size bound
`‖χ‖ ≤ 1` on the coefficients.  This is one of the two analytic inputs (the other is the
exponential decay at `∞` when `ĝ(0) = 0`) used to continue the completed Hecke `L`-function; see
`Submission/Work/FIArea6Hecke/R/A6HeckeDual.lean` for the definition and its rôle.

The proof is the standard "locally uniformly convergent series of continuous functions" argument:

* the Gauss sum is bounded by the number of terms of its defining finite sum,
  `‖gaussSum d chi ξ‖ ≤ (4d)²`, which uses only `‖χ‖ ≤ 1` (`thetaDualGaussBound`);
* hence for each fixed `a > 0` the summand `ξ ↦ ĝ(ξ)e^{-π|ξ|²w}` is dominated uniformly on
  the half-line `(a,∞)` by the (summable over `ℤ²`) Gaussian `(4d)²·e^{-π|ξ|²a}`
  (`thetaDualDominated`), so `Mathlib`'s `continuousOn_tsum` gives continuity on `(a,∞)`;
* `(a,∞)` is a neighbourhood of every point of `(0,∞)` for suitable `a = w/2`, giving
  `ContinuousWithinAt` at each `w > 0`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.A6HeckeDual

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Bound on the Gauss sum

The Gauss sum is a finite sum of `(4d)²` terms, each of which is either `0` or `χ α` times a
phase of modulus `1`; the triangle inequality and `‖χ‖ ≤ 1` give the bound. -/

theorem thetaDualGaussBound_aux (d : ℕ) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (ξ : GaussianInt) :
    ‖Work.FIArea5.S16Hecke.gaussSum d chi ξ‖ ≤ ((4 * d : ℕ) : ℝ) ^ 2 := by
  rw [Work.FIArea5.S16Hecke.gaussSum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ α ∈ (Finset.range (4 * d)).product (Finset.range (4 * d)),
      ‖(if Work.FIArea5.S16Hecke.isOddG (⟨α.1, α.2⟩ : GaussianInt) then
        chi (⟨α.1, α.2⟩ : GaussianInt) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((((α.1 * ξ.re + α.2 * ξ.im : ℤ)) : ℂ) / ((4 * d : ℕ) : ℂ)))
       else 0)‖ ≤ 1 := by
    intro α _
    by_cases h : Work.FIArea5.S16Hecke.isOddG (⟨α.1, α.2⟩ : GaussianInt)
    · rw [if_pos h, norm_mul,
        Work.FIArea5.S16Hecke.norm_exp_two_pi_I_mul_div (α.1 * ξ.re + α.2 * ξ.im) (4 * d),
        mul_one]
      exact hchi _
    · rw [if_neg h]; simp
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  simp [Finset.card_product, Finset.card_range]
  ring

/-! ## Summability of the dominating Gaussian over `ℤ²` -/

theorem thetaDualDominated_aux (a : ℝ) (ha : 0 < a) :
    Summable (fun p : ℤ × ℤ => Real.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * a))) := by
  have h := Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add (c := Real.pi * a)
    (by positivity) 0 0
  refine h.congr (fun p => ?_)
  simp only [zero_mul, add_zero, pow_zero, mul_one]
  congr 1
  ring

/-! ## Continuity on each half-line `(a,∞)`, `a > 0` -/

theorem continuousOn_thetaDual_Ioi (d : ℕ) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (thetaDual d chi) (Set.Ioi a) := by
  have key : thetaDual d chi = fun w : ℝ => ∑' ξ : ℤ × ℤ,
      Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        Complex.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)) := by
    funext w
    rw [thetaDual]
  have hconv : ContinuousOn (fun w : ℝ => ∑' ξ : ℤ × ℤ,
      Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        Complex.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w))) (Set.Ioi a) := by
    refine continuousOn_tsum (u := fun ξ : ℤ × ℤ => ((4 * d : ℕ) : ℝ) ^ 2 *
      Real.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a))) ?_ ?_ ?_
    · intro ξ
      have hcont : Continuous (fun w : ℝ =>
          Complex.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w))) := by fun_prop
      exact (continuous_const.mul hcont).continuousOn
    · exact (thetaDualDominated_aux a ha).mul_left _
    · intro ξ w hw
      rw [norm_mul]
      have ht : 0 ≤ (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 := by positivity
      have hnorm : ‖Complex.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w))‖
          = Real.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)) := by
        rw [show -Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)
            = ((-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w) : ℝ) : ℂ) by
              push_cast; ring]
        rw [Complex.norm_exp_ofReal]
      have hmono : Real.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w))
          ≤ Real.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a)) := by
        apply Real.exp_le_exp.mpr
        have h1 : ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a
            ≤ ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w :=
          mul_le_mul_of_nonneg_left (le_of_lt hw) ht
        have h2 : Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * a)
            ≤ Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w) :=
          mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
        linarith [h2]
      rw [hnorm]
      exact mul_le_mul (thetaDualGaussBound_aux d hchi _) hmono (Real.exp_pos _).le
        (by positivity)
  rw [key]
  exact hconv

/-- **Continuity of the dual theta function on `(0,∞)`.** -/
theorem continuousOn_thetaDual (d : ℕ) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ContinuousOn (Work.FIArea6Hecke.R.thetaDual d chi) (Set.Ioi 0) := by
  intro w hw
  have hw0 : (0 : ℝ) < w := hw
  have hhalf : (0 : ℝ) < w / 2 := by linarith
  have hcont : ContinuousOn (thetaDual d chi) (Set.Ioi (w / 2)) :=
    continuousOn_thetaDual_Ioi d hchi hhalf
  have hmem : Set.Ioi (w / 2) ∈ nhds w :=
    isOpen_Ioi.mem_nhds (show w / 2 < w from by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

end

end Work.FIArea6Hecke.R
