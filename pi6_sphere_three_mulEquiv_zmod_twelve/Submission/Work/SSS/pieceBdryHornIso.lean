import Mathlib
import Submission.Work.SSS.serreE1PieceDefs
import Submission.Work.SSS.lastFaceDefs
import Submission.Work.SSS.cokerInfSupChain
import Submission.Work.SSS.coker_conj_iso
import Submission.Work.SSS.boundary_eq_hornSimp_sup_lastFaceSimp
import Submission.Work.SSS.hornSimp_preimage_delta_last
import Submission.Work.SSS.range_eq_preimage_range_of_isPullback
import Submission.Work.SSS.image_preimage_eq_inf_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

/-!
## Auxiliary generalities
-/

/-- The functor `X ↦ C(X)`, the singular chain complex with `ℤ`-coefficients. -/
abbrev sCCFunctor : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- `sCCMap` is functorial. -/
lemma sCCMap_comp' {X Y Z : SSet.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    sCCMap (g ≫ h) = sCCMap g ≫ sCCMap h :=
  CategoryTheory.Functor.map_comp _ _ _

/-- `homOfLE` depends only on its source and target. -/
lemma homOfLE_eq_of_eq {Z : SSet.{0}} {S₁ S₂ : Z.Subcomplex} (h₁ h₂ : S₁ ≤ S₂) :
    SSet.Subcomplex.homOfLE h₁ = SSet.Subcomplex.homOfLE h₂ := rfl

/-- The cokernel of `C(A) ⟶ C(B)` depends only on the subcomplexes `A` and `B`. -/
lemma coker_homOfLE_congr {Z : SSet.{0}} {A A' B B' : Z.Subcomplex} (hA : A = A')
    (hB : B = B') (hAB : A ≤ B) (hAB' : A' ≤ B') :
    Nonempty (cokernel (sCCMap (SSet.Subcomplex.homOfLE hAB)) ≅
      cokernel (sCCMap (SSet.Subcomplex.homOfLE hAB'))) := by
  refine ⟨cokernel.mapIso _ _ (sCCFunctor.mapIso (SSet.Subcomplex.eqToIso hA))
    (sCCFunctor.mapIso (SSet.Subcomplex.eqToIso hB)) ?_⟩
  simp only [CategoryTheory.Functor.mapIso_hom, SSet.Subcomplex.eqToIso_hom]
  rw [← sCCMap_comp', ← sCCMap_comp', SSet.Subcomplex.homOfLE_comp,
    SSet.Subcomplex.homOfLE_comp]

/-- The cokernel of `C(P) ⟶ C(Z)` (the inclusion of a subcomplex) depends only on `P`. -/
lemma coker_iota_congr {Z : SSet.{0}} {P Q : Z.Subcomplex} (h : P = Q) :
    Nonempty (cokernel (sCCMap P.ι) ≅ cokernel (sCCMap Q.ι)) := by
  rw [h]
  exact ⟨Iso.refl _⟩

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
  try rfl

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

/-!
## The main theorem
-/

/-- **The boundary/horn quotient is the σ-piece over the last face.**  For a morphism of simplicial
sets `f : X ⟶ Y` and a simplex `σ : Δ[t+1] ⟶ Y`, the quotient `C(∂T_σ)/C(Λ)` of the boundary
subcomplex `∂T_σ = bdryAlong f σ` by the horn `Λ = pieceHorn f σ` is, as a chain complex, the
σ-piece of the **last face** `d_{t+1}σ = SSet.stdSimplex.δ (Fin.last (t+1)) ≫ σ : Δ[t] ⟶ Y`.

The point is that `∂Δ[t+1] = Λ ⊔ d_{t+1}Δ[t+1]` (as subcomplexes of `Δ[t+1]`) with
`Λ ⊓ d_{t+1}Δ[t+1] = ∂(d_{t+1}Δ[t+1])`; pulling back along `pullback.fst σ f` gives
`C(∂T_σ)/C(Λ) ≅ C(D)/C(Λ ⊓ D)` where `D = pieceLastFace f σ`, and the pullback-pasting
isomorphism `D ≅ pullAlong f (d_{t+1}σ)` (the preimage of a range `Subcomplex.range (δ)` under the
first projection of a pullback is again a pullback) identifies `Λ ⊓ D` with
`bdryAlong f (d_{t+1}σ)`. -/
theorem pieceBdryHornIso {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Nonempty (Work.SSS.pieceBdryHornC f σ ≅
      Work.SSS.pieceAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) := by
  obtain ⟨e₁⟩ := coker_inf_sup_iso_chain (pullAlong f σ) (pieceHorn f σ) (pieceLastFace f σ)
  haveI : Mono (lastFaceMap f t σ) := lastFaceMap_mono f t σ
  obtain ⟨e₂⟩ := coker_conj_iso (lastFaceMap f t σ)
    ((pieceHorn f σ).preimage (lastFaceMap f t σ))
  obtain ⟨t₁⟩ := coker_homOfLE_congr (Z := pullAlong f σ) (A := pieceHorn f σ)
    (A' := pieceHorn f σ) (B := bdryAlong f σ) (B' := pieceHorn f σ ⊔ pieceLastFace f σ)
    rfl (bdryAlong_eq_horn_sup_lastFace f t σ).symm (pieceHorn_le_bdryAlong f σ) le_sup_left
  have himg : ((pieceHorn f σ).preimage (lastFaceMap f t σ)).image (lastFaceMap f t σ)
      = pieceHorn f σ ⊓ pieceLastFace f σ :=
    (image_preimage_eq_inf_range (pieceHorn f σ) (lastFaceMap f t σ)).trans
      (congrArg (fun S => pieceHorn f σ ⊓ S) (range_lastFaceMap f t σ))
  obtain ⟨t₃⟩ := coker_homOfLE_congr (Z := pullAlong f σ)
    (A := pieceHorn f σ ⊓ pieceLastFace f σ)
    (A' := ((pieceHorn f σ).preimage (lastFaceMap f t σ)).image (lastFaceMap f t σ))
    (B := pieceLastFace f σ) (B' := SSet.Subcomplex.range (lastFaceMap f t σ))
    himg.symm (range_lastFaceMap f t σ).symm inf_le_right (SSet.Subcomplex.image_le_range _ _)
  obtain ⟨t₄⟩ := coker_iota_congr (Z := pullAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
    (P := (pieceHorn f σ).preimage (lastFaceMap f t σ))
    (Q := bdryAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
    (preimage_lastFaceMap f t σ)
  exact ⟨t₁ ≪≫ e₁.symm ≪≫ t₃ ≪≫ e₂ ≪≫ t₄⟩

end

end Work.SSS
