import Mathlib
import Submission.Work.SSS.serreE1PieceDefs

/-!
# The collapse of the prism `Δ[s] × Δ[1]` onto the last vertex of `Δ[s]`

For `s : ℕ`, `Work.SSS.collapseMap s` is the morphism of simplicial sets

  `collapseMap s : Δ[s] ⊗ Δ[1] ⟶ Δ[s]`

which sends the vertex `(j,0)` of the prism `Δ[s] × Δ[1]` to the vertex `j` of `Δ[s]` and
the vertex `(j,1)` to the vertex `s`.  Since `Δ[s] ⊗ Δ[1]` is the nerve of the product poset
`[s] × [1]`, this is a simplicial map; in coordinates, for an `n`-simplex `(a, μ)` of the prism
(where `a : [n] → [s]` and `μ : [n] → [1]` are monotone) its value is the monotone map

  `j ↦ if μ j = 0 then a j else s`.

This is the combinatorial "straight-line collapse" of `Δ[s]` to its last vertex `v_s`; its two
endpoints are `ι₀ ≫ collapseMap s = 𝟙` and `ι₁ ≫ collapseMap s = const v_s`.  It maps the part
of the prism lying over the horn `Λ ⊆ Δ[s]` into the horn, which is what makes it a contraction
of the pair `(Δ[s], Λ)` to the last vertex (see `Work.SSS.pieceContraction`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial
open MonoidalCategory

noncomputable section

/-- The order homomorphism underlying the collapse on `n`-simplices: given monotone maps
`a : [n] → [s]` and `μ : [n] → [1]`, it is `j ↦ if μ j = 0 then a j else s`. -/
def collapseHom {s n : ℕ} (a : Fin (n + 1) →o Fin (s + 1)) (mu : Fin (n + 1) →o Fin 2) :
    Fin (n + 1) →o Fin (s + 1) where
  toFun j := if (mu j : ℕ) = 0 then a j else Fin.last s
  monotone' := by
    intro i j hij
    have hle : (mu i : ℕ) ≤ (mu j : ℕ) := mu.monotone hij
    by_cases hi : (mu i : ℕ) = 0
    · by_cases hj : (mu j : ℕ) = 0
      · simp only [hi, hj, ↓reduceIte]
        exact a.monotone hij
      · simp only [hi, hj, ↓reduceIte]
        exact Fin.le_last _
    · have hj : (mu j : ℕ) ≠ 0 := by omega
      simp only [hi, hj, ↓reduceIte, le_refl]

/-- **The collapse of the prism `Δ[s] × Δ[1]` onto the last vertex of `Δ[s]`.** -/
noncomputable def collapseMap (s : ℕ) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet) ⊗
      (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet) : SSet) ⟶
      (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet) where
  app := fun X => ↾fun z =>
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
      (collapseHom
        (SimplexCategory.Hom.toOrderHom (SSet.stdSimplex.objEquiv z.1))
        (SimplexCategory.Hom.toOrderHom
          (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk 1) (m := X) z.2))))
  naturality := by
    intro X Y f
    ext z
    dsimp only [SSet.prod_map_fst, SSet.prod_map_snd]
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    ext j
    dsimp only
    rfl

end

end Work.SSS
