import Mathlib
import Submission.Work.SSSR.grFMap
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.ezGen_snd_sum_zero
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.serreSubcomplexToN
import Submission.Work.SSSR.StemsB.SerreFiltration
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

variable {X Y : SSet.{0}}

/-- **The second projection of the pullback `T_σ` into a term `R_k` of the Serre filtration.**
Whenever the image of the second projection `T_σ ⟶ X` lies in `f ⁻¹' (sk k)`, it factors through
`R_k = f ⁻¹' (sk k)`. -/
noncomputable def sndToSerre (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) (k : ℕ)
    (hk : SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.SSSR.StemsB.serreSubcomplex f k) :
    pullAlong f σ ⟶ ((Work.SSSR.StemsB.serreSubcomplex f k : X.Subcomplex) : SSet) :=
  SSet.Subcomplex.lift (pullback.snd σ f) hk

@[simp] lemma sndToSerre_ι (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) (k : ℕ)
    (hk : SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.SSSR.StemsB.serreSubcomplex f k) :
    sndToSerre f σ k hk ≫ (Work.SSSR.StemsB.serreSubcomplex f k).ι = pullback.snd σ f :=
  SSet.Subcomplex.lift_ι _ _

/-- `Work.SSSR.sndToR` is the special case of `Work.SSSR.sndToSerre` attached to a nondegenerate
simplex. -/
lemma sndToR_eq_sndToSerre (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    sndToR f y = sndToSerre f (nIndexSigma Y d y) (d+1) (T_range_le f y) := rfl


variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The `i`-th face of the Eilenberg–Zilber lift** `ezSimplex_σ`: the composite
`(δ i ⊗ 𝟙) ≫ ezSimplex_σ`. -/
def ezFaceLift (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (i : Fin (s+2)) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
        sSing (Work.SSSR.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) σ :=
  (SSet.stdSimplex.δ (n := s) i ⊗ₘ 𝟙 (sSing (Work.SSSR.StemsB.fibre p b))) ≫
    ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) (s+1) b σ h

/-- **The Eilenberg–Zilber chain of `σ` over a chain `z` of the fibre**, in `C(T_σ)`. -/
def iotaTLin (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (z : (fibreCC (R := R) p b).X t) :
    (sCC R (pullAlong (sSingP p) σ)).X ((s+1)+t) :=
  (ModuleCat.Hom.hom ((sCCMap R (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib)
      (s+1) b σ h)).f ((s+1)+t)))
    (ezLinSnd (s+1) t (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
      (sSing (Work.SSSR.StemsB.fibre p b)) (stdIdSimplex (s+1)) z)

/-- **The `i`-th face term of the boundary of `iotaTLin`.** -/
def iotaTLinFace (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (i : Fin (s+2)) (z : (fibreCC (R := R) p b).X t) :
    (sCC R (pullAlong (sSingP p) σ)).X (s+t) :=
  (ModuleCat.Hom.hom ((sCCMap R (ezFaceLift p hfib s b σ h i)).f (s+t)))
    (ezLinSnd s t (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
      (sSing (Work.SSSR.StemsB.fibre p b)) (stdIdSimplex s) z)

end

end Work.SSSR
