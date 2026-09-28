import Mathlib
import Submission.Work.SSS.serreE1EZ

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

-- As in `Work.SSS.serreE1EZ`: the terms below are built from the (semi)cartesian monoidal
-- structure of `SSet`, and the default transparency of the unifier is not enough to see that
-- `CosimplicialObject SSet` is `SimplexCategory ⥤ SSet` while matching the rewriting patterns.
set_option backward.isDefEq.respectTransparency false

/-- **The lift of the pullback is natural under the cofaces `δ i` with `i ≠ 0`.**

`Work.SSS.ezSimplex p Φ hproj P b σ h : Δ[P] ⊗ Sing (F_b) ⟶ T_σ` (where `T_σ` is the pullback
`Δ[P] ×_{Sing B} Sing E`) is the pairing of the first projection with the lift
`Φ P b σ h : Δ[P] ⊗ Sing F_b ⟶ Sing E`.  For `i ≠ 0` the coface `δ i : Δ[Q] ⟶ Δ[Q+1]` keeps the
`0`-th vertex (`(δ i) v₀ = v₀`), so the face `d_iσ` is again based at `b`
(`Work.SSS.sigmaVert_face`), and the coherence clause (iii) of the lift family
(`Work.SSS.liftFam_coh`) says exactly that the lift commutes with `δ i ⊗ 𝟙`.  Hence the two
composites agree, `T_{d_iσ} ⟶ T_σ` being the pullback inclusion `Work.SSS.pullFaceIncl`.

This is the "`i ≠ 0` face" input for the computation of the first differential `d¹` of the Serre
filtration (`REFS/NOTES_LEAD_SSS.md` §2): for `i ≠ 0` the `i`-th face of `ι_σ τ` is `ι_{d_iσ} τ`. -/
theorem ezSimplex_liftFam_coface {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (Q+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (i : Fin (Q+2)) (hi : i ≠ 0)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := Q) i ≫ σ) = b) :
    (SSet.stdSimplex.δ (n := Q) i ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
        ≫ Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (Q+1) b σ h
      = Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) Q b
            (SSet.stdSimplex.δ (n := Q) i ≫ σ) h'
        ≫ Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ i := by
  -- Both sides are morphisms into the pullback `T_σ = pullAlong (sSingP p) σ`, which is the
  -- limit of `σ` and `sSingP p`; it suffices to compare the two projections.
  apply pullback.hom_ext
  · -- First projection.  Both sides reduce to the first projection of `Δ[-] ⊗ Sing F_b`
    -- (this is `ezSimplex_fst` and `pullFaceIncl_fst`), and the remaining identity is the
    -- naturality of the first projection, `CartesianMonoidalCategory.tensorHom_fst`.
    simp only [Category.assoc, Work.SSS.ezSimplex_fst, Work.SSS.pullFaceIncl_fst]
    rw [← Category.assoc, Work.SSS.ezSimplex_fst]
    exact CartesianMonoidalCategory.tensorHom_fst _ _
  · -- Second projection.  Both sides reduce to the lift `Φ` (this is `ezSimplex_snd` and
    -- `pullFaceIncl_snd`), and the remaining identity is exactly the coherence clause (iii) of
    -- the lift family.
    simp only [Category.assoc, Work.SSS.ezSimplex_snd, Work.SSS.pullFaceIncl_snd]
    exact Work.SSS.liftFam_coh p hfib Q b σ h i hi h'

end Work.SSS
