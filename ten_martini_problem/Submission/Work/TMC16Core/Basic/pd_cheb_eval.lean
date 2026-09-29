/-
# `P_k(x) = pd α λ (x - ctr k α) E (k+1)`: evaluation of the bivariate Chebyshev form

`Work.TMC16Core.Cheb.Pbiv α lam E k` is the continuant of the length-`k` list of
potentials `E - 2λ cos (2π (x + jα - centre))`, encoded as a bivariate polynomial in
`X = cos 2πx`, `Y = sin 2πx`.  This file proves that evaluating it at the point
`(cos 2πx, sin 2πx)` recovers the continuant `Work.TMC16Core.pd`, i.e. the Dirichlet
determinant `det ((E - H)|_{[0,k-1]})`.

The proof has three ingredients, each proved elsewhere in the workspace:

* `Work.TMC16Core.Basic.cont_range_map` — `cont` of a `range`-indexed list is the
  two-step recursion `Cheb.contSeq` (list/transfer-matrix algebra);
* `Work.TMC16Core.Basic.pd_eq_contSeq` — `pd` *is* that recursion, with the potentials of
  the almost Mathieu operator (a definitional unfolding);
* `Work.TMC16Core.Basic.afun_eval` — the evaluation of a single potential, i.e.
  `cos A · cos B - sin A · sin B = cos (A + B)` (the angle-addition formula).

The remaining step, done here, is that evaluation is a ring homomorphism and therefore
commutes with the continuant recursion (`Cheb.cont_map`).
-/
import Mathlib
import Submission.Work.TMC16Core.Basic.pd_cheb_setup
import Submission.Work.TMC16Core.Basic.pd_cheb_cont
import Submission.Work.TMC16Core.Basic.cont_range_map
import Submission.Work.TMC16Core.Basic.pd_eq_contSeq
import Submission.Work.TMC16Core.Basic.afun_eval

namespace Work.TMC16Core.Basic

theorem pd_cheb_eval (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) :
    (Work.TMC16Core.Cheb.Pbiv α lam E k).eval₂
        (Polynomial.evalRingHom (((Real.cos (2 * Real.pi * x) : ℝ)) : ℂ))
        (((Real.sin (2 * Real.pi * x) : ℝ)) : ℂ)
      = Work.TMC16Core.pd α lam (x - Work.TMC16Core.Cheb.ctr k α) E (k + 1) := by
  -- Evaluation at `(cos 2πx, sin 2πx)` is the ring homomorphism `ψ` on `ℂ[X][X]`.
  let ψ : Polynomial (Polynomial ℂ) →+* ℂ :=
    Polynomial.eval₂RingHom (Polynomial.evalRingHom (((Real.cos (2 * Real.pi * x) : ℝ)) : ℂ))
      (((Real.sin (2 * Real.pi * x) : ℝ)) : ℂ)
  show ψ (Work.TMC16Core.Cheb.Pbiv α lam E k)
      = Work.TMC16Core.pd α lam (x - Work.TMC16Core.Cheb.ctr k α) E (k + 1)
  -- `ψ` commutes with the continuant, which is a polynomial in the entries of the list.
  have h2 : ψ (Work.TMC16Core.Cheb.Pbiv α lam E k)
      = Work.TMC16Core.Cheb.contSeq (fun j => ψ (Work.TMC16Core.Cheb.afun α lam E k j))
          (k + 1) := by
    rw [Work.TMC16Core.Cheb.Pbiv,
      ← Work.TMC16Core.Cheb.cont_map ψ (Work.TMC16Core.Cheb.listA α lam E k),
      Work.TMC16Core.Cheb.listA, List.map_map]
    exact cont_range_map (⇑ψ ∘ Work.TMC16Core.Cheb.afun α lam E k) k
  rw [h2]
  -- The evaluated sequence of potentials is the one appearing in `pd`.
  have h3 : (fun j => ψ (Work.TMC16Core.Cheb.afun α lam E k j))
      = (fun j => E - ((Work.TMC16Core.amoPot α lam (x - Work.TMC16Core.Cheb.ctr k α)
          ((j : ℕ) : ℤ) : ℝ) : ℂ)) := by
    funext j
    exact afun_eval α lam E k j x
  rw [h3]
  exact (pd_eq_contSeq α lam (x - Work.TMC16Core.Cheb.ctr k α) E (k + 1)).symm

end Work.TMC16Core.Basic
