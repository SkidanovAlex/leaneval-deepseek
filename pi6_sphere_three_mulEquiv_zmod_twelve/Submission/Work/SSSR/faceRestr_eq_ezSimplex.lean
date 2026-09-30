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

/-- For `i ≠ 0` the `i`-th face restriction of the coherent lift is the coherent lift of the `i`-th
face: both are `pullback.lift fst (Φ s b (δ i ≫ σ) h') _`, and the second components agree by
`Work.SSSR.liftFam_coh` (`(δ i ⊗ 𝟙) ≫ liftFam (s+1) b σ h = liftFam s b (δ i ≫ σ) h'`), while the
first components are both `fst`; the `pullback.lift` proof arguments are `Prop`-valued.
Use `pullback.hom_ext` with `faceLift_fst`/`faceLift_snd` and `ezSimplex_fst`/`ezSimplex_snd`. -/
theorem faceRestr_eq_ezSimplex (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (i : Fin (s + 2)) (hi : i ≠ 0)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) i ≫ σ) = b) :
    Work.SSSR.faceRestr p hfib s b σ h i
      = Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b
          (SSet.stdSimplex.δ (n := s) i ≫ σ) h' := by
  apply pullback.hom_ext
  · rw [faceRestr, faceLift_fst, ezSimplex_fst]
  · rw [faceRestr, faceLift_snd, ezSimplex_snd, ezSimplex_snd,
      liftFam_coh p hfib s b σ h i hi h']

end Work.SSSR
