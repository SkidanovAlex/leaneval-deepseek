import Mathlib

/-!
# Monomial continuous multilinear maps on `ℂ × ℂ`

This file sets up the basic objects used in `Work.RedProj.monomial_formalSeries`:
the two coordinate projections of `ℂ × ℂ` and the "monomial" continuous
multilinear map of arity `n` whose `m`-th term evaluates, on a constant tuple
`(u,v)`, to `u^m * v^(n-m)`.
-/

namespace Work.RedProj

noncomputable section

/-- First coordinate projection `ℂ × ℂ →L[ℂ] ℂ`. -/
def pi1 : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ ℂ

/-- Second coordinate projection `ℂ × ℂ →L[ℂ] ℂ`. -/
def pi2 : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ

@[simp] lemma pi1_apply (p : ℂ × ℂ) : pi1 p = p.1 := rfl

@[simp] lemma pi2_apply (p : ℂ × ℂ) : pi2 p = p.2 := rfl

/-- The monomial continuous multilinear map of arity `n` and index `m`:
`x ↦ ∏ i, (if (i : ℕ) < m then (x i).1 else (x i).2)`. -/
def monomial (n m : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun i : Fin n => if (i : ℕ) < m then pi1 else pi2)

@[simp] lemma monomial_apply_apply (n m : ℕ) (x : Fin n → ℂ × ℂ) :
    monomial n m x = ∏ i : Fin n, (if (i : ℕ) < m then (x i).1 else (x i).2) := by
  rw [monomial, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases h : (i : ℕ) < m <;> simp [h]

end

end Work.RedProj
