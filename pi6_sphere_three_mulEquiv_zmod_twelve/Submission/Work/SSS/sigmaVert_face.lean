import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.serreE1PieceDefs

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-- **The vertex underlying a simplex is unchanged by a face that omits a vertex other than the
first one.**  `sigmaVert σ` is the value of the continuous map `Δ[s] → B` underlying `σ` at the
`0`-th vertex `v₀ = Pi.single 0 1`.  For a face inclusion `δ i : Δ[t] ⟶ Δ[t+1]` with `i ≠ 0`, the
composite `δ i ≫ σ` still has `v₀` as its `0`-th vertex, so `sigmaVert (δ i ≫ σ) = sigmaVert σ`.

(The hypothesis `i ≠ 0` is necessary: for `i = 0` the face omits `v₀` and sends the `0`-th vertex
to `v₁`, i.e. `sigmaVert (δ 0 ≫ σ) = τ(v₁)`.) -/
theorem sigmaVert_face {B : Type} [TopologicalSpace B] {t : ℕ} (i : Fin (t+2)) (hi : i ≠ 0)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := t) i ≫ σ) = Work.SSS.sigmaVert σ := by
  -- The simplex underlying `δ i ≫ σ` is the `i`-th face of the simplex underlying `σ`.
  have h1 : SSet.yonedaEquiv (SSet.stdSimplex.δ (n := t) i ≫ σ)
      = (TopCat.toSSet.obj (TopCat.of B)).δ i (SSet.yonedaEquiv σ) := by
    have hcomp : SSet.yonedaEquiv (SSet.stdSimplex.δ (n := t) i ≫ σ)
        = σ.app (op ⦋t⦌) (SSet.yonedaEquiv (SSet.stdSimplex.δ (n := t) i)) := by
      have h := SSet.yonedaEquiv_symm_comp
        (SSet.yonedaEquiv (SSet.stdSimplex.δ (n := t) i)) σ
      rw [Equiv.symm_apply_apply] at h
      rw [h, Equiv.apply_symm_apply]
    have hδ : SSet.yonedaEquiv (SSet.stdSimplex.δ (n := t) i)
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) :=
      SSet.yonedaEquiv_map (SimplexCategory.δ i)
    rw [hcomp, hδ]
    conv_lhs => rw [← Equiv.symm_apply_apply SSet.yonedaEquiv σ]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    rw [SimplicialObject.δ_def]
  -- The `0`-th vertex of `Δ[t+1]` restricts along `δ i` (with `i ≠ 0`) to the `0`-th vertex.
  have hv : stdSimplex.map (S := ℝ) (i.succAbove)
        (stdSimplex.vertex (S := ℝ) (X := Fin (t+1)) (0 : Fin (t+1)))
      = stdSimplex.vertex (S := ℝ) (X := Fin (t+2)) (0 : Fin (t+2)) := by
    rw [stdSimplex.map_vertex]
    congr 1
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa using Fin.pos_iff_ne_zero.mpr hi)]
    simp
  simp only [Work.SSS.sigmaVert]
  rw [h1, TopCat.toSSetObjEquivT_δ_apply, hv]

end Work.SSS
