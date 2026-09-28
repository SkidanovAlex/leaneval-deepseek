import Mathlib
import Submission.Work.SSS.grFMap
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.ezGen_snd_sum_zero
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.serreSubcomplexToN
import Submission.Work.StemsB.SerreFiltration

/-!
# The second projection of a pullback into the Serre filtration

For a morphism of simplicial sets `f : X ⟶ Y`, a simplex `σ : Δ[P] ⟶ Y` of the target and a term
`R_k = f ⁻¹' (sk k)` of the Serre filtration, the second projection
`pullback.snd σ f : T_σ = Δ[P] ×_Y X ⟶ X` factors through `R_k` whenever its image lies there;
`Work.SSS.sndToSerre` is that factorisation.

It generalises `Work.SSS.sndToR` (the case `σ = nIndexSigma Y d y, k = d+1`) to *arbitrary*
simplices, which is what the computation of the first differential `d¹` needs: the boundary of a
lifted σ-cycle decomposes into face terms indexed by the faces `δ i ≫ σ`, and each has to be
compared with the term for the nondegenerate face `d_iσ` of `Work.SSS.nIndex`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {X Y : SSet.{0}}

/-- **The second projection of the pullback `T_σ` into a term `R_k` of the Serre filtration.**
Whenever the image of the second projection `T_σ ⟶ X` lies in `f ⁻¹' (sk k)`, it factors through
`R_k = f ⁻¹' (sk k)`. -/
noncomputable def sndToSerre (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) (k : ℕ)
    (hk : SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.StemsB.serreSubcomplex f k) :
    pullAlong f σ ⟶ ((Work.StemsB.serreSubcomplex f k : X.Subcomplex) : SSet) :=
  SSet.Subcomplex.lift (pullback.snd σ f) hk

@[simp] lemma sndToSerre_ι (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) (k : ℕ)
    (hk : SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.StemsB.serreSubcomplex f k) :
    sndToSerre f σ k hk ≫ (Work.StemsB.serreSubcomplex f k).ι = pullback.snd σ f :=
  SSet.Subcomplex.lift_ι _ _

/-- `Work.SSS.sndToR` is the special case of `Work.SSS.sndToSerre` attached to a nondegenerate
simplex. -/
lemma sndToR_eq_sndToSerre (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    sndToR f y = sndToSerre f (nIndexSigma Y d y) (d+1) (T_range_le f y) := rfl


/-! ## The Eilenberg–Zilber chain of a simplex of the base, and its face terms

These are the explicit chains whose boundary is computed in the first differential `d¹`:
`iotaTLin` is the shuffle chain `ι_σ(z)` pushed into the pullback `T_σ` (before projecting to the
σ-piece), and `iotaTLinFace i` is its `i`-th face term, obtained by restricting the lift to the
`i`-th face `δ i ≫ σ` of `σ`. -/

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The `i`-th face of the Eilenberg–Zilber lift** `ezSimplex_σ`: the composite
`(δ i ⊗ 𝟙) ≫ ezSimplex_σ`. -/
def ezFaceLift (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (i : Fin (s+2)) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⊗
        sSing (Work.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) σ :=
  (SSet.stdSimplex.δ (n := s) i ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b))) ≫
    ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) (s+1) b σ h

/-- **The Eilenberg–Zilber chain of `σ` over a chain `z` of the fibre**, in `C(T_σ)`. -/
def iotaTLin (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (z : (fibreCC p b).X t) :
    (sCC (pullAlong (sSingP p) σ)).X ((s+1)+t) :=
  (ModuleCat.Hom.hom ((sCCMap (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib)
      (s+1) b σ h)).f ((s+1)+t)))
    (ezLinSnd (s+1) t (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
      (sSing (Work.StemsB.fibre p b)) (stdIdSimplex (s+1)) z)

/-- **The `i`-th face term of the boundary of `iotaTLin`.** -/
def iotaTLinFace (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (i : Fin (s+2)) (z : (fibreCC p b).X t) :
    (sCC (pullAlong (sSingP p) σ)).X (s+t) :=
  (ModuleCat.Hom.hom ((sCCMap (ezFaceLift p hfib s b σ h i)).f (s+t)))
    (ezLinSnd s t (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
      (sSing (Work.StemsB.fibre p b)) (stdIdSimplex s) z)

end

end Work.SSS
