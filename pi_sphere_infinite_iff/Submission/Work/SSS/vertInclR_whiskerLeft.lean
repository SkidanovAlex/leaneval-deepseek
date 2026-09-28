import Mathlib
import Submission.Work.SSS.coherentLiftR

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

/-- **The cosimplicial coface `δ_j` (with `j ≠ 0`) fixes the `0`-th vertex.**  The vertex
`Work.SSS.ssetVertex n = (SSet.stdSimplex.obj₀Equiv).symm 0` is the `0`-simplex of `Δ[n]` at the
vertex `0`; the coface `δ_j : Δ[n] ⟶ Δ[n+1]` skips vertex `j`, so when `j ≠ 0` it sends vertex `0`
to vertex `0`. -/
lemma vertex_delta_apply {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0) :
    (SSet.stdSimplex.δ (n := n) j).app (Opposite.op (SimplexCategory.mk 0)) (ssetVertex n)
      = ssetVertex (n + 1) := by
  have hA : SSet.stdSimplex.objEquiv (ssetVertex n) ≫ SimplexCategory.δ j
      = SSet.stdSimplex.objEquiv (ssetVertex (n + 1)) := by
    apply SimplexCategory.Hom.ext_zero_left
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, SimplexCategory.δ,
      SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
      Fin.succAboveOrderEmb_apply, Function.comp_apply]
    exact Fin.succAbove_ne_zero_zero hj
  rw [CosimplicialObject.δ, ← Equiv.symm_apply_apply (SSet.stdSimplex.objEquiv) (ssetVertex n),
      ← SSet.stdSimplex.objEquiv_symm_comp, hA, Equiv.symm_apply_apply]

/-- **The right-handed fibre inclusion is compatible with the face inclusions of the simplex.**
`Work.SSS.vertInclR p b' n : sSing (p⁻¹b') ⟶ sSing (p⁻¹b') ⊗ Δ[n]` is `σ ↦ (σ, v₀)`; applying
a face inclusion `δ_j` (with `j ≠ 0`) to the simplex coordinate gives `vertInclR p b' (n+1)`.
Proof: check the two components against `fst` and `snd`
(`CartesianMonoidalCategory.hom_ext`, `CartesianMonoidalCategory.whiskerLeft_fst`,
`CartesianMonoidalCategory.whiskerLeft_snd`, `Work.SSS.vertInclR_fst`, `Work.SSS.vertInclR_snd`),
and use `SSet.const_comp` and the fact that `δ_j` with `j ≠ 0` fixes the `0`-th vertex
(`Work.SSS.vertex_delta_apply`). -/
theorem vertInclR_whiskerLeft {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b' : B) {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0) :
    Work.SSS.vertInclR p b' n ≫
        (Work.SSS.sSing (Work.StemsB.fibre p b') ◁ SSet.stdSimplex.δ (n := n) j)
      = Work.SSS.vertInclR p b' (n + 1) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst, vertInclR_fst]
  · rw [Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd, ← Category.assoc,
      vertInclR_snd, SSet.const_comp, vertex_delta_apply j hj, vertInclR_snd]

end Work.SSS
