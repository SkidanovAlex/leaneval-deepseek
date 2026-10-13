/-
  WilVP : `Work.WilVP.definable_bound`.

  The set `{v : α → M | ∃ u : M, v i * v i + u * u = v j * v j}` is *literally* the
  realization set of an `LRc`-formula: `∃ y, x_i * x_i + y * y = x_j * x_j`, a formula of the
  language of rings (with `x_i`, `x_j` free and `y` bound), pushed into
  `LRc = (ring ⊕ rexpL)[[ℝ]]` along the language inclusion `ring →ᴸ LRc`.  Nothing about the
  order, the exponential or the constants is used: the claim is purely syntactic.

  The only subtlety is the quantifier bookkeeping: the quantified variable is the unique
  element of `Fin 1`, and `FirstOrder.Language.Formula.ex` on a formula with free variables
  `α` is exactly the existential quantification over `Fin 1`.
-/
import Mathlib
import Submission.Work.WilC2.Basic

set_option autoImplicit false

namespace Work.WilVP

open FirstOrder FirstOrder.Language

/-- The formula `x_i * x_i + y * y = x_j * x_j` of the language of rings, with free variables
`α` (`x_k = Sum.inl k`) and a single bound variable `y = Sum.inr 0`. -/
def boundB {α : Type} (i j : α) : FirstOrder.Language.ring.BoundedFormula α 1 :=
  Term.bdEqual
    (Term.var (Sum.inl i) * Term.var (Sum.inl i) +
      Term.var (Sum.inr (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)))
    (Term.var (Sum.inl j) * Term.var (Sum.inl j))

/-- The formula `∃ y, x_i * x_i + y * y = x_j * x_j` of the language of rings. -/
def boundF {α : Type} (i j : α) : FirstOrder.Language.ring.Formula α := (boundB i j).ex

/-- Realization of `boundF`: `∃ y, x_i * x_i + y * y = x_j * x_j`. -/
lemma boundF_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] {α : Type} (i j : α) (v : α → M) :
    (boundF i j).Realize v ↔ ∃ u : M, v i * v i + u * u = v j * v j := by
  rw [boundF, Formula.Realize, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [boundB, BoundedFormula.realize_bdEqual] at ha
    simpa [Sum.elim_inl, Sum.elim_inr, Ring.realize_add, Ring.realize_mul, Fin.snoc_zero] using ha
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [boundB, BoundedFormula.realize_bdEqual]
    simpa [Sum.elim_inl, Sum.elim_inr, Ring.realize_add, Ring.realize_mul, Fin.snoc_zero] using hu

theorem definable_bound {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {α : Type} (i j : α) :
    (∅ : Set M).Definable WilkiesDesign.CG.LRc
      {v : α → M | ∃ u : M, v i * v i + u * u = v j * v j} := by
  rw [Set.empty_definable_iff]
  refine ⟨Work.WilC2.ringToLRc.onFormula (boundF i j), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [LHom.realize_onFormula]
  exact (boundF_realize i j v).symm

end Work.WilVP
