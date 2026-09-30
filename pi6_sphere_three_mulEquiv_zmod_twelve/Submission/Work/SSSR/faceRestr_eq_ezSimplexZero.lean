import Mathlib
import Submission.Work.SSSR.serreE1CruxDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `0`-th face restriction of the coherent lift is the `0`-face lift `Work.SSSR.ezSimplexZero`.
Both sides are `pullback.lift fst ((δ 0 ⊗ 𝟙) ≫ ezSimplex_σ ≫ snd) _`, differing only by the
association of `≫`; the proof is `pullback.hom_ext` together with `faceLift_fst`/`faceLift_snd` and
`ezSimplexZero_fst`/`ezSimplexZero_snd`. -/
theorem faceRestr_eq_ezSimplexZero (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    Work.SSSR.faceRestr p hfib s b σ h 0
      = Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b σ h
    := by
  rw [Work.SSSR.faceRestr]
  apply pullback.hom_ext
  · rw [Work.SSSR.faceLift_fst, Work.SSSR.ezSimplexZero_fst]
  · rw [Work.SSSR.faceLift_snd, Work.SSSR.ezSimplexZero_snd]
    exact (Category.assoc _ _ _).symm

end Work.SSSR
