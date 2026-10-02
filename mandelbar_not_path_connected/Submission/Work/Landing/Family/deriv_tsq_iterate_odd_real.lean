import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ComplexConjugate

namespace Work.Landing.Family

open LeanEval.ComplexAnalysis (Tantibar)

/-- If `f` is complex-differentiable at `x` and `star (f x) = x`, then the antiholomorphic map
`star ∘ f` has holomorphic square `(star ∘ f) ∘ (star ∘ f)`, whose complex derivative at `x` is
the non-negative real number `‖deriv f x‖²`.  This is the "antilinear multiplier squared" of
Hubbard–Schleicher §2. -/
lemma deriv_star_comp_self {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℂ f x)
    (hx : star (f x) = x) :
    deriv ((star ∘ f) ∘ (star ∘ f)) x = (↑(Complex.normSq (deriv f x)) : ℂ) := by
  have hFeq : (star ∘ f) ∘ (star ∘ f) = (star ∘ f ∘ star) ∘ f := by
    funext z; rfl
  rw [hFeq]
  have hpt : f x = (starRingEnd ℂ) x := by
    rw [starRingEnd_apply]
    have := congrArg star hx
    simpa using this
  have hfd : DifferentiableAt ℂ (star ∘ f ∘ star) (f x) := by
    rw [hpt]
    exact hf.conj_conj
  rw [deriv_comp x hfd hf]
  have hderivfun : deriv (star ∘ f ∘ star) = star ∘ deriv f ∘ star := by
    simp
  have hderiv : deriv (star ∘ f ∘ star) (f x) = star (deriv f x) := by
    rw [hderivfun]
    simp only [Function.comp_apply]
    rw [hx]
  rw [hderiv, mul_comm (star (deriv f x)) (deriv f x)]
  exact Complex.mul_conj (deriv f x)

theorem deriv_tsq_iterate_odd_real (c : ℂ) {k : ℕ} (hk : Odd k) {x : ℂ}
    (hx : (LeanEval.ComplexAnalysis.Tantibar c)^[k] x = x) :
    ∃ r : ℝ, 0 ≤ r ∧ deriv ((Work.Landing.Tsq c)^[k]) x = ↑r := by
  obtain ⟨m, rfl⟩ := hk
  have hcomp1 : Tantibar c ∘ Tantibar c = Work.Landing.Tsq c := by
    funext z
    simp only [Function.comp_apply, Tantibar, Work.Landing.Tsq, starRingEnd_apply,
      star_add, star_pow, star_star]
  have hT2 : (Tantibar c)^[2] = Work.Landing.Tsq c := by
    rw [show (2:ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
    exact hcomp1
  have hT : (Tantibar c)^[2*m+1] = Tantibar c ∘ (Work.Landing.Tsq c)^[m] := by
    rw [show 2*m+1 = 1 + 2*m by omega, Function.iterate_add, Function.iterate_one,
      Function.iterate_mul (Tantibar c) 2 m, hT2]
  have hstarT : (star : ℂ → ℂ) ∘ Tantibar c = fun z : ℂ => z^2 + star c := by
    funext z
    simp only [Function.comp_apply, Tantibar, starRingEnd_apply, star_add, star_pow, star_star]
  let f : ℂ → ℂ := fun z => star ((Tantibar c)^[2*m+1] z)
  have hf_eq : f = (fun w : ℂ => w^2 + star c) ∘ (Work.Landing.Tsq c)^[m] := by
    have h1 : f = (star : ℂ → ℂ) ∘ (Tantibar c)^[2*m+1] := rfl
    rw [h1, hT, ← Function.comp_assoc, hstarT]
  have hf_diff : DifferentiableAt ℂ f x := by
    rw [hf_eq]
    have hp : Differentiable ℂ (fun w : ℂ => w^2 + star c) := by fun_prop
    have hS : Differentiable ℂ (Work.Landing.Tsq c) := by
      unfold Work.Landing.Tsq; fun_prop
    exact (hp.comp (hS.iterate m)).differentiableAt
  have hfx : star (f x) = x := by
    simp only [f, star_star]
    exact hx
  have key := deriv_star_comp_self (f := f) (x := x) hf_diff hfx
  have hsf : star ∘ f = (Tantibar c)^[2*m+1] := by
    funext z
    simp only [Function.comp_apply, f, star_star]
  have hfun : (star ∘ f) ∘ (star ∘ f) = (Work.Landing.Tsq c)^[2*m+1] := by
    rw [hsf, ← Function.iterate_add (Tantibar c) (2*m+1) (2*m+1),
      show (2*m+1) + (2*m+1) = 2*(2*m+1) by ring,
      Function.iterate_mul (Tantibar c) 2 (2*m+1), hT2]
  refine ⟨Complex.normSq (deriv f x), Complex.normSq_nonneg _, ?_⟩
  rw [← hfun]
  exact key

end Work.Landing.Family
