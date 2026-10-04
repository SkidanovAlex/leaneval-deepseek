import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_succ_eq`: splitting the `Hᵏ⁺¹` energy into first derivatives

The physical-space energy of the STE development is

  `ENormSq k f = Σ_{l : Fin k → ι} ∫_{unitCube} ‖∂^l f‖²`

(`Submission/Work/Diff/STE/Torus.lean`), the sum of the `L²` norms squared of *all* iterated
partial derivatives of order `k`, indexed by tuples `l : Fin k → ι`.  This file records the
recursion that is used to turn the `Hᵏ⁺¹` energy estimate into an estimate on `Hᵏ`:

  `ENormSq (k+1) u = Σ_{l : Fin k → ι} Σ_{i : ι} ∫_{unitCube} ‖∂ᵢ (∂^l u)‖²`,

i.e. the `(k+1)`-fold derivatives are obtained by composing the `k`-fold ones with the first
derivatives `∂ᵢ`.

The content is purely combinatorial:

* `pdVec_cons_eq`: `pdVec (k+1) (Fin.cons i l) f = pd i (pdVec k l f)` (the tuple
  `Fin.cons i l` is the list `i :: ofFn l`, and `pdList` is a `List.foldr` of `pd`,
  which peels the head off);
* `finConsEquiv`: the bijection `(Fin k → ι) × ι ≃ (Fin (k+1) → ι)`, `(l, i) ↦ Fin.cons i l`
  (a re-ordering of Mathlib's `Fin.consEquiv`);
* the conclusion is then a reindexing of the finite sum over `Fin (k+1) → ι`.

No integrability or smoothness assumption is needed: the integrals are treated as a function of
the index only.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE

/-- Iterated partial derivatives peel off the first direction: applying `pdVec (k+1)` to a tuple
whose first entry is `i` is the same as applying `∂ᵢ` to the `k`-fold derivative
`pdVec k` of the tail. -/
lemma pdVec_cons_eq {ι : Type*} [DecidableEq ι] (k : ℕ) (i : ι) (l : Fin k → ι)
    (f : (ι → ℝ) → ℂ) :
    pdVec (k + 1) (Fin.cons i l) f = pd i (pdVec k l f) := by
  simp only [pdVec, pdList, List.ofFn_cons, List.foldr_cons]

/-- The tuples `Fin (k+1) → ι` are the pairs (first coordinate, tail), reordered so that the
tail (a `Fin k → ι`) comes first.  This is `Fin.cons` as an `Equiv`. -/
def finConsEquiv {ι : Type*} (k : ℕ) : (Fin k → ι) × ι ≃ (Fin (k + 1) → ι) where
  toFun p := Fin.cons p.2 p.1
  invFun l := (Fin.tail l, l 0)
  left_inv p := by simp [Fin.tail_cons]
  right_inv l := by simp

lemma finConsEquiv_apply {ι : Type*} (k : ℕ) (p : (Fin k → ι) × ι) :
    finConsEquiv (ι := ι) k p = Fin.cons p.2 p.1 := rfl

/-- `ENormSq (k+1)` is obtained from `ENormSq`-type sums by adding one first derivative: the sum
over all `(k+1)`-tuples of directions splits into a sum over the tail `l : Fin k → ι` and the
first direction `i : ι`, and `pdVec (k+1) (Fin.cons i l) = pd i (pdVec k l)`. -/
theorem ENormSq_succ_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (u : (ι → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq (k + 1) u
      = ∑ l : Fin k → ι, ∑ i : ι,
          ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pd i (Work.Diff.STE.pdVec k l u) x‖ ^ 2 := by
  rw [ENormSq]
  rw [← Equiv.sum_comp (finConsEquiv (ι := ι) k)
        (fun l' : Fin (k + 1) → ι => ∫ x in unitCube, ‖pdVec (k + 1) l' u x‖ ^ 2)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [finConsEquiv_apply]
  rw [pdVec_cons_eq]

end Work.Diff.STE
