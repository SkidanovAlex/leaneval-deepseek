import Mathlib
import Submission.Work.ADcl.tfun
import Submission.Work.ADcl.ode_H
import Submission.Work.ADcl.ode_Hw
import Submission.Work.ADcl.reduce_generic
import Submission.Work.CDcl.xrel_linalg

/-!
# The order-four `x`-side relation for the Theorem-A pullbacks

`T k = (G^{(k)})∘y` for `G = Sym⁺(a·H_A + b·H_B + c·H_C)`, and `Aop f = ρ·f'` is `d/dy` acting on
the `x`-side.  Since `A^k H = a_k H + b_k H' + d_k` and `A^k (H∘φ) = ã_k (H∘φ) + b̃_k (H∘φ)' + d̃_k`
(`reduce_H`, `reduce_Hw`), every `T k` lies in the `ℚ(x)`-span of `H, H', H∘φ, (H∘φ)'` plus a
rational function.  Five vectors in the span of four are dependent (`Work.CDcl.xrel_linalg`), and
clearing denominators gives a nontrivial `ℚ[x]`-relation among `T 0, …, T 4`.
-/

namespace Work.ADcl

noncomputable section

/-- the reduction for `H`: `A^k H = a_k H + b_k H' + d_k`. -/
theorem reduce_H (a b c : ℚ) (k : ℕ) :
    Work.CDcl.Aop^[k] (Hfun a b c) = Work.CDcl.toL (seqA b c k).1 * Hfun a b c
      + Work.CDcl.toL (seqA b c k).2.1 * Work.CDcl.dL (Hfun a b c)
      + Work.CDcl.toL (seqA b c k).2.2 :=
  reduce_generic (Hfun a b c) alphaA betaA (gammaA b c) (ode_H a b c) k

/-- the reduction for `H∘φ`. -/
theorem reduce_Hw (a b c : ℚ) (k : ℕ) :
    Work.CDcl.Aop^[k] (Hwfun a b c) = Work.CDcl.toL (seqAt b c k).1 * Hwfun a b c
      + Work.CDcl.toL (seqAt b c k).2.1 * Work.CDcl.dL (Hwfun a b c)
      + Work.CDcl.toL (seqAt b c k).2.2 :=
  reduce_generic (Hwfun a b c) alphaAt betaAt (gammaAt b c) (ode_Hw a b c) k

/-- **the nontrivial `ℚ[x]`-relation among `T 0, …, T 4`**. -/
theorem x_relation_A (a b c : ℚ) :
    ∃ (Q : Fin 5 → Polynomial ℚ) (r : Polynomial ℚ), Q ≠ 0 ∧
      ∑ k : Fin 5, (Q k : PowerSeries ℚ) * Tz a b c k = (r : PowerSeries ℚ) := by
  classical
  let U : Fin 5 → Fin 4 → RatFunc ℚ := fun k i =>
    if i = 0 then (seqA b c (k : ℕ)).1
    else if i = 1 then (seqA b c (k : ℕ)).2.1
    else if i = 2 then (seqAt b c (k : ℕ)).1
    else (seqAt b c (k : ℕ)).2.1
  let D : Fin 5 → RatFunc ℚ := fun k =>
    (seqA b c (k : ℕ)).2.2 + (seqAt b c (k : ℕ)).2.2
  have hF : ∀ k : Fin 5, Tfun a b c (k : ℕ)
      = Work.CDcl.toL (U k 0) * Hfun a b c + Work.CDcl.toL (U k 1) * Work.CDcl.dL (Hfun a b c)
        + Work.CDcl.toL (U k 2) * Hwfun a b c
        + Work.CDcl.toL (U k 3) * Work.CDcl.dL (Hwfun a b c) + Work.CDcl.toL (D k) := by
    intro k
    have h0 : U k 0 = (seqA b c (k : ℕ)).1 := rfl
    have h1 : U k 1 = (seqA b c (k : ℕ)).2.1 := rfl
    have h2 : U k 2 = (seqAt b c (k : ℕ)).1 := rfl
    have h3 : U k 3 = (seqAt b c (k : ℕ)).2.1 := rfl
    have hD : D k = (seqA b c (k : ℕ)).2.2 + (seqAt b c (k : ℕ)).2.2 := rfl
    rw [Tfun_iter, Tfun_zero, Aop_iterate_add, reduce_H a b c (k : ℕ), reduce_Hw a b c (k : ℕ),
      h0, h1, h2, h3, hD, map_add]
    ring
  obtain ⟨Q, r, hQ, hrel⟩ := Work.CDcl.xrel_linalg (fun k => Tfun a b c (k : ℕ))
    (Hfun a b c) (Work.CDcl.dL (Hfun a b c)) (Hwfun a b c) (Work.CDcl.dL (Hwfun a b c)) U D hF
  refine ⟨Q, r, hQ, ?_⟩
  apply IsFractionRing.injective (PowerSeries ℚ) Work.CDcl.LF
  have hQk : ∀ k : Fin 5, algebraMap (PowerSeries ℚ) Work.CDcl.LF ((Q k : Polynomial ℚ) : PowerSeries ℚ)
      = Work.CDcl.toL (Q k) := by
    intro k
    simp only [RatFunc.coePolynomial, Work.CDcl.toL_algebraMap]
  have hr : algebraMap (PowerSeries ℚ) Work.CDcl.LF ((r : Polynomial ℚ) : PowerSeries ℚ)
      = Work.CDcl.toL r := by
    simp only [RatFunc.coePolynomial, Work.CDcl.toL_algebraMap]
  have h1 : algebraMap (PowerSeries ℚ) Work.CDcl.LF
      (∑ k : Fin 5, (Q k : PowerSeries ℚ) * Tz a b c k)
      = ∑ k : Fin 5, Work.CDcl.toL (Q k) * Tfun a b c (k : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hQk k]
    rfl
  rw [h1, hr]
  exact hrel

end

end Work.ADcl
