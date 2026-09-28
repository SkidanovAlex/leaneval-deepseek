import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `0`-th face restriction of the coherent lift is the `0`-face lift `Work.SSS.ezSimplexZero`.
Both sides are `pullback.lift fst ((δ 0 ⊗ 𝟙) ≫ ezSimplex_σ ≫ snd) _`, differing only by the
association of `≫`; the proof is `pullback.hom_ext` together with `faceLift_fst`/`faceLift_snd` and
`ezSimplexZero_fst`/`ezSimplexZero_snd`. -/
theorem faceRestr_eq_ezSimplexZero (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    Work.SSS.faceRestr p hfib s b σ h 0
      = Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b σ h
    := by
  rw [Work.SSS.faceRestr]
  apply pullback.hom_ext
  · rw [Work.SSS.faceLift_fst, Work.SSS.ezSimplexZero_fst]
  · rw [Work.SSS.faceLift_snd, Work.SSS.ezSimplexZero_snd]
    exact (Category.assoc _ _ _).symm

end Work.SSS
