import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- For `i ≠ 0` the `i`-th face restriction of the coherent lift is the coherent lift of the `i`-th
face: both are `pullback.lift fst (Φ s b (δ i ≫ σ) h') _`, and the second components agree by
`Work.SSS.liftFam_coh` (`(δ i ⊗ 𝟙) ≫ liftFam (s+1) b σ h = liftFam s b (δ i ≫ σ) h'`), while the
first components are both `fst`; the `pullback.lift` proof arguments are `Prop`-valued.
Use `pullback.hom_ext` with `faceLift_fst`/`faceLift_snd` and `ezSimplex_fst`/`ezSimplex_snd`. -/
theorem faceRestr_eq_ezSimplex (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (i : Fin (s + 2)) (hi : i ≠ 0)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) i ≫ σ) = b) :
    Work.SSS.faceRestr p hfib s b σ h i
      = Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b
          (SSet.stdSimplex.δ (n := s) i ≫ σ) h' := by
  apply pullback.hom_ext
  · rw [faceRestr, faceLift_fst, ezSimplex_fst]
  · rw [faceRestr, faceLift_snd, ezSimplex_snd, ezSimplex_snd,
      liftFam_coh p hfib s b σ h i hi h']

end Work.SSS
