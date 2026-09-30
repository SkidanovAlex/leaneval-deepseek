import Mathlib
import Submission.Work.SSSR.serreE1PieceDefs
import Submission.Work.SSSR.lastFaceDefs
import Submission.Work.SSSR.cokerInfSupChain
import Submission.Work.SSSR.coker_conj_iso
import Submission.Work.SSSR.boundary_eq_hornSimp_sup_lastFaceSimp
import Submission.Work.SSSR.hornSimp_preimage_delta_last
import Submission.Work.SSSR.range_eq_preimage_range_of_isPullback
import Submission.Work.SSSR.image_preimage_eq_inf_range

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-!
## Auxiliary generalities
-/

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- The functor `X ↦ C(X)`, the singular chain complex with `ℤ`-coefficients. -/
abbrev sCCFunctor : SSet.{0} ⥤ ChainComplex (ModuleCat R) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)

/-- `sCCMap R` is functorial. -/
lemma sCCMap_comp' {X Y Z : SSet.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    sCCMap R (g ≫ h) = sCCMap R g ≫ sCCMap R h :=
  CategoryTheory.Functor.map_comp _ _ _

/-!
## The last-face pasting map
-/

/-- The range of the last-face pasting map `Δ[t] ×_Y X ⟶ Δ[t+1] ×_Y X` is the last-face
subcomplex. -/
theorem range_lastFaceMap {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    SSet.Subcomplex.range (lastFaceMap f t σ) = pieceLastFace f σ := by
  rw [range_eq_preimage_range_of_isPullback (lastFaceMap_isPullback f t σ), pieceLastFace,
    lastFaceSimp, ← SSet.stdSimplex.range_δ]
  rfl

/-- The preimage of the horn under the last-face pasting map is the boundary of the last face. -/
theorem preimage_lastFaceMap {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    (pieceHorn f σ).preimage (lastFaceMap f t σ) =
      bdryAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) := by
  have key : (hornSimp (t+1)).preimage (lastFaceMap f t σ ≫ pullback.fst σ f) =
      (hornSimp (t+1)).preimage (pullback.fst (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f ≫
        SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) := by
    rw [lastFaceMap_fst]
  rw [pieceHorn, bdryAlong, ← hornSimp_preimage_delta_last t]
  exact key

/-- The boundary of the pullback is the union of the horn and of the last face. -/
theorem bdryAlong_eq_horn_sup_lastFace {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    pieceHorn f σ ⊔ pieceLastFace f σ = bdryAlong f σ := by
  simp only [pieceHorn, pieceLastFace, bdryAlong, boundary_eq_hornSimp_sup_lastFaceSimp]
  rfl

end

end Work.SSSR
