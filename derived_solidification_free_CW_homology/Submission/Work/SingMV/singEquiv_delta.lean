import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# The identification `singEquiv` is compatible with the simplicial face maps

`singEquiv X n` identifies the `n`-simplices of the singular simplicial set of `X` with the
continuous maps `Δⁿ ⟶ X`. The simplicial structure (face maps `δ i`) corresponds, under this
identification, to precomposition with the topological coface inclusion
`coface n i = SimplexCategory.toTop₀.map (SimplexCategory.δ i)`.

Both sides are, by definition, precomposition with the monotone map `Fin.succAbove i`; the proof
below is the bookkeeping that unfolds `singEquiv`, the relevant Mathlib lemma
`TopCat.toSSetObjEquiv_δ_apply` and the definition of `coface`.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

noncomputable section

namespace Work.SingMV

/-- The underlying map of the topological coface inclusion `coface n i : Δⁿ ⟶ Δⁿ⁺¹` is the
monotone injection `Fin.succAbove i`. -/
lemma coface_hom_apply (n : ℕ) (i : Fin (n+2)) (z : StdSimplex ℝ (Fin (n+1))) :
    (coface n i).hom z = StdSimplex.map i.succAbove z := rfl

theorem singEquiv_delta (X : TopCat) (n : ℕ) (i : Fin (n+2)) (σ : Work.SingMV.singMap X (n+1)) :
    Work.SingMV.singEquiv X n
        ((TopCat.toSSet.obj X).δ i ((Work.SingMV.singEquiv X (n+1)).symm σ)) =
      σ.comp ((Work.SingMV.coface n i).hom) := by
  ext z
  rw [singEquiv, singEquiv, TopCat.toSSetObjEquiv_δ_apply, ContinuousMap.comp_apply,
    Equiv.apply_symm_apply, coface_hom_apply]

end Work.SingMV
