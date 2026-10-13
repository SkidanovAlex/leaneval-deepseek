import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Basic
import Submission.Work.WilC5.LRcReduct

namespace Work.WilC5

open FirstOrder Language

/-- **Every `LRc`-term takes values in the definable closure of the parameter set.**

This is the closure step behind `dclClosed_substructure`: a term is *itself* a formula, so the
value `t.realize x` of a term at a tuple `x` of parameters in `A` is definable from `A`
(namely by the formula `t(τ) = z`, `τ` the constants attached to the parameters `x`).

The formula is built in `Set.definable_iff_exists_formula_sum` form: over `LRc`, with the
parameters adjoined as extra free variables of type `A`. -/
lemma term_realize_mem_dcl {M : Type} [Language.Structure WilkiesDesign.CG.LRc M] {A : Set M}
    {n : ℕ} (t : Language.Term WilkiesDesign.CG.LRc (Fin n)) (x : Fin n → M)
    (hx : ∀ i, x i ∈ A) :
    t.realize x ∈ Work.WilC2.Dcl A := by
  rw [Work.WilC2.mem_dcl, Set.Definable₁, Set.definable_iff_exists_formula_sum]
  refine ⟨(Term.var (Sum.inr (0 : Fin 1))).equal
    (t.relabel (fun i => Sum.inl (⟨x i, hx i⟩ : A))), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  have hc : (Sum.elim (Subtype.val : A → M) v) ∘
      (fun i => Sum.inl (⟨x i, hx i⟩ : A)) = x := by
    funext i
    rfl
  have key : Term.realize (Sum.elim (Subtype.val : A → M) v)
      (t.relabel (fun i => Sum.inl (⟨x i, hx i⟩ : A))) = t.realize x := by
    rw [Term.realize_relabel, hc]
  rw [Formula.realize_equal, key, Term.realize_var, Sum.elim_inr]

/-- **A set closed under definable closure is the underlying set of a substructure.**

In the language `LRc = (ring ⊕ rexp)[[ℝ]]` the function symbols are the ring operations, the
restricted exponential, and a constant for every real.  For a function symbol `f` of arity `n`
and a tuple `x` of elements of `A`, the element `funMap f x` is the value of the term
`Functions.term f`, hence lies in `Dcl A` by `term_realize_mem_dcl`, hence in `A` by hypothesis.
So `A` itself is a legitimate carrier of an `LRc`-substructure. -/
theorem dclClosed_substructure {M : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LRc M]
    {A : Set M} (hA : Work.WilC2.Dcl A ⊆ A) :
    ∃ S : WilkiesDesign.CG.LRc.Substructure M, (S : Set M) = A := by
  refine ⟨⟨A, ?_⟩, rfl⟩
  intro n f x hx
  have h := hA (term_realize_mem_dcl (Functions.term f) x hx)
  simpa [Functions.term, Term.realize_func, Term.realize_var] using h

end Work.WilC5
