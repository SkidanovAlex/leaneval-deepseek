import Mathlib
import Submission.Work.SSSR.serreE1EZ
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
set_option backward.isDefEq.respectTransparency false

/-- **The lift of the pullback is natural under the cofaces `δ i` with `i ≠ 0`.**

`Work.SSSR.ezSimplex p Φ hproj P b σ h : Δ[P] ⊗ Sing (F_b) ⟶ T_σ` (where `T_σ` is the pullback
`Δ[P] ×_{Sing B} Sing E`) is the pairing of the first projection with the lift
`Φ P b σ h : Δ[P] ⊗ Sing F_b ⟶ Sing E`.  For `i ≠ 0` the coface `δ i : Δ[Q] ⟶ Δ[Q+1]` keeps the
`0`-th vertex (`(δ i) v₀ = v₀`), so the face `d_iσ` is again based at `b`
(`Work.SSSR.sigmaVert_face`), and the coherence clause (iii) of the lift family
(`Work.SSSR.liftFam_coh`) says exactly that the lift commutes with `δ i ⊗ 𝟙`.  Hence the two
composites agree, `T_{d_iσ} ⟶ T_σ` being the pullback inclusion `Work.SSSR.pullFaceIncl`.

This is the "`i ≠ 0` face" input for the computation of the first differential `d¹` of the Serre
filtration (`REFS/NOTES_LEAD_SSS.md` §2): for `i ≠ 0` the `i`-th face of `ι_σ τ` is `ι_{d_iσ} τ`. -/
theorem ezSimplex_liftFam_coface {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (Q+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (i : Fin (Q+2)) (hi : i ≠ 0)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := Q) i ≫ σ) = b) :
    (SSet.stdSimplex.δ (n := Q) i ⊗ₘ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)))
        ≫ Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (Q+1) b σ h
      = Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) Q b
            (SSet.stdSimplex.δ (n := Q) i ≫ σ) h'
        ≫ Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ i := by
  -- Both sides are morphisms into the pullback `T_σ = pullAlong (sSingP p) σ`, which is the
  -- limit of `σ` and `sSingP p`; it suffices to compare the two projections.
  apply pullback.hom_ext
  · -- First projection.  Both sides reduce to the first projection of `Δ[-] ⊗ Sing F_b`
    -- (this is `ezSimplex_fst` and `pullFaceIncl_fst`), and the remaining identity is the
    -- naturality of the first projection, `CartesianMonoidalCategory.tensorHom_fst`.
    simp only [Category.assoc, Work.SSSR.ezSimplex_fst, Work.SSSR.pullFaceIncl_fst]
    rw [← Category.assoc, Work.SSSR.ezSimplex_fst]
    exact CartesianMonoidalCategory.tensorHom_fst _ _
  · -- Second projection.  Both sides reduce to the lift `Φ` (this is `ezSimplex_snd` and
    -- `pullFaceIncl_snd`), and the remaining identity is exactly the coherence clause (iii) of
    -- the lift family.
    simp only [Category.assoc, Work.SSSR.ezSimplex_snd, Work.SSSR.pullFaceIncl_snd]
    exact Work.SSSR.liftFam_coh p hfib Q b σ h i hi h'

end Work.SSSR
