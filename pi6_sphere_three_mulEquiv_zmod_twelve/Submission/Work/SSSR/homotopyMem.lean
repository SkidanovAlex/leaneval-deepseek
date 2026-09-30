import Mathlib
import Submission.Work.SSSR.collapseDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Simplicial
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
/-- The first component of `(f ▷ L).app Δ` is `f.app Δ` applied to the first component.
(Specialised to `SSet`, where the tensor product is the product of simplicial sets.) -/
lemma whiskerRight_fst {K K' : SSet.{0}} (f : K ⟶ K') (L : SSet.{0}) (Δ : SimplexCategoryᵒᵖ)
    (x : (K ⊗ L).obj Δ) : ((f ▷ L).app Δ x).1 = f.app Δ x.1 := rfl

/-- **A homotopy whose graph stays in a subcomplex preserves that subcomplex.**
Let `X` be a simplicial set, `A ⊆ X` a subcomplex, `f g : X ⟶ X` and `H : SSet.Homotopy f g`
with `H.h : X ⊗ Δ[1] ⟶ X` (so `H.h` is the homotopy map).  If the graph of `H.h` over `A` lies in
`A` — that is, if `A.prod ⊤ ≤ A.preimage H.h` — then each component
`H.toSimplicialObjectHomotopy.h j` of the associated combinatorial homotopy
(`CategoryTheory.SimplicialObject.Homotopy`) maps `Aₙ` into `A_{n+1}`.

This is a statement about the explicit formula for
`SSet.Homotopy.toSimplicialObjectHomotopy`, whose `h j` is
`x ↦ H.h ((yonedaEquiv.symm x ▷ Δ[1]) (SSet.prodStdSimplex.nonDegenerateEquiv₁ j).1)`; the
argument `(yonedaEquiv.symm x ▷ Δ[1]) (nonDegenerateEquiv₁ j).1` of `H.h` lies in `A.prod ⊤`
whenever `x ∈ Aₙ`. -/
theorem homotopyMem {X : SSet.{0}} (A : X.Subcomplex) {f g : X ⟶ X} (H : SSet.Homotopy f g)
    (hA : A.prod (⊤ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet).Subcomplex)
      ≤ A.preimage H.h) :
    ∀ (n : ℕ) (j : Fin (n+1)) (x : X.obj (Opposite.op (SimplexCategory.mk n))),
      x ∈ A.obj (Opposite.op (SimplexCategory.mk n)) →
      (H.toSimplicialObjectHomotopy).h j x ∈ A.obj (Opposite.op (SimplexCategory.mk (n+1))) := by
  intro n j x hx
  -- The value of `(yonedaEquiv.symm x).app Δ a` is `X.map (objEquiv a).op x`, which stays in `A`
  -- because `A` is a subfunctor closed under the structure maps of `X`.
  have hyon : ∀ (a : (Δ[n] : SSet).obj (op ⦋n+1⦌)),
      (SSet.yonedaEquiv.symm x).app (op ⦋n+1⦌) a ∈ A.obj (op ⦋n+1⦌) := by
    intro a
    rw [← SSet.stdSimplex.map_objEquiv_op_apply x a]
    exact A.map (SSet.stdSimplex.objEquiv a).op hx
  -- The argument of `H.h` lies in the product subcomplex `A.prod ⊤`.
  have hpair : ((SSet.yonedaEquiv.symm x ▷ Δ[1]).app (op ⦋n+1⦌)
      (SSet.prodStdSimplex.nonDegenerateEquiv₁ j).1) ∈ (A.prod ⊤).obj (op ⦋n+1⦌) := by
    rw [SSet.Subcomplex.prod_obj]
    apply Set.mem_prod.mpr
    constructor
    · rw [whiskerRight_fst]
      exact hyon _
    · trivial
  -- Unfold the definition of `toSimplicialObjectHomotopy` and apply `hA`.
  change H.h.app (op ⦋n+1⦌) ((SSet.yonedaEquiv.symm x ▷ Δ[1]).app (op ⦋n+1⦌)
    (SSet.prodStdSimplex.nonDegenerateEquiv₁ j).1) ∈ A.obj (op ⦋n+1⦌)
  exact hA (op ⦋n+1⦌) hpair

end Work.SSSR
