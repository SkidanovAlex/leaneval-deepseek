import Mathlib
import Submission.Work.GM.S3.Base

/-!
# Definitions and elementary calculus for GM Lemma 4.3 (`hhat_decay`)

The task `hhat_decay` proves GM Lemma 4.3: `‖ĥ_t(ξ)‖ ≤ C_j (1+|t|)^j / |ξ|^j`, where
`ĥ_t(ξ) = ∫ e(-ξu) w(u)² u^{it} du`.

This file sets up the vocabulary used by that proof (and by the lemmas delegated for it):

* `w2C u = w(u)²` seen as a complex-valued function;
* `phi t u = exp(i t log u)`, the oscillatory factor, so that `hfun t = w2C · phi t` **everywhere**
  (`hfun_eq_w2C_mul_phi`);
* the transfer lemmas `deriv_ofReal_comp` / `iteratedDeriv_ofReal_comp` comparing the iterated
  derivatives of `ℝ → ℂ` functions of the shape `fun y => (f y : ℂ)` with those of `f : ℝ → ℝ`
  (this is how the derivative bounds for `w(u)²` are imported from `bumpW_deriv_bdd`).
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (hfun)

/-- `w(u)²` as a complex valued function. -/
noncomputable def w2C (u : ℝ) : ℂ := ((Submission.LargeValues.bumpW u : ℂ)) ^ 2

/-- The oscillatory factor `u^{it} = exp(i t log u)`. -/
noncomputable def phi (t : ℝ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (Real.log u : ℂ))

theorem w2C_eq (u : ℝ) : w2C u = ((Submission.LargeValues.bumpW u ^ 2 : ℝ) : ℂ) := by
  rw [w2C]; push_cast; ring

theorem w2C_eq_zero_of_notMem {u : ℝ} (hu : u ∉ Set.Icc (1 : ℝ) 2) : w2C u = 0 := by
  rw [w2C, Submission.LargeValues.bumpW_eq_zero_of_notMem hu]
  simp

theorem w2C_eq_mul (u : ℝ) :
    w2C u = ((Submission.LargeValues.bumpW u : ℂ)) * ((Submission.LargeValues.bumpW u : ℂ)) := by
  rw [w2C, sq]

theorem norm_w2C (u : ℝ) : ‖w2C u‖ = Submission.LargeValues.bumpW u ^ 2 := by
  rw [w2C, norm_pow]
  simp [abs_of_nonneg (Submission.LargeValues.bumpW_nonneg u), sq]

/-- `hfun t = w² · u^{it}`, everywhere (for `u ≤ 0` both sides vanish because `w u = 0`). -/
theorem hfun_eq_w2C_mul_phi (t u : ℝ) : hfun t u = w2C u * phi t u := by
  rw [hfun, w2C, phi]
  push_cast
  rcases le_or_gt u 0 with hu | hu
  · have h1 : u ∉ Set.Icc (1 : ℝ) 2 := by
      simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith
    rw [Submission.LargeValues.bumpW_eq_zero_of_notMem h1]; simp
  · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hu), Complex.ofReal_log hu.le]
    ring_nf

/-- As functions, `hfun t = w2C · phi t`. -/
theorem hfun_eq_mul (t : ℝ) : hfun t = w2C * phi t := by
  ext u; exact hfun_eq_w2C_mul_phi t u

/-- The iterated derivative of a `ℝ → ℂ` function obtained by coercing an `ℝ → ℝ` function
is the coercion of the iterated derivative. -/
theorem deriv_ofReal_comp (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => ((f y : ℝ) : ℂ)) x = ((deriv f x : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ f x
  · exact (h.hasDerivAt.ofReal_comp).deriv
  · have h2 : ¬ DifferentiableAt ℝ (fun y : ℝ => ((f y : ℝ) : ℂ)) x := by
      intro hd
      have hcomp : DifferentiableAt ℝ (Complex.re ∘ fun y : ℝ => ((f y : ℝ) : ℂ)) x :=
        Complex.reCLM.differentiableAt.comp x hd
      exact h (by simpa [Function.comp_def] using hcomp)
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h2]
    simp

theorem iteratedDeriv_ofReal_comp : ∀ (k : ℕ) (f : ℝ → ℝ),
    iteratedDeriv k (fun y => ((f y : ℝ) : ℂ)) = fun y => ((iteratedDeriv k f y : ℝ) : ℂ) := by
  intro k
  induction k with
  | zero => intro f; ext x; simp
  | succ k ih =>
    intro f
    have hd : deriv (fun y : ℝ => ((f y : ℝ) : ℂ)) = fun y => ((deriv f y : ℝ) : ℂ) :=
      funext fun x => deriv_ofReal_comp f x
    rw [iteratedDeriv_succ', hd, ih (deriv f)]
    ext x
    simp only [iteratedDeriv_succ']

end Work.GM.S3
