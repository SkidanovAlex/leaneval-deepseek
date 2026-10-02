import Mathlib
import Submission.Work.ThomBordism.iUnion.psiInterface
import Submission.Work.ThomBordism.chainSetup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

/-!
# The `psiAbs`/`localThomMap` interface

`Work.ThomBordism.PsiClassHyp Z n U τ W hW` asks that, for every cocycle `a : C^m(W;ℤ)`, the
relative cohomology class of the cochain-level cup `psiAbs Z n U τ W hW m a` (the cup of the
pullback of `a` to the piece `Z.proj ⁻¹' W` with the chosen relative representative `tauRepAt` of
`τ|_W`) is the local Thom map of the restricted class `τ|_W` applied to the class of `a`.

The proof is the comparison of the concrete Alexander–Whitney cup product on cochains with the
abstract mixed cup product `Work.Thom.mixedCupC = Classical.choose (mixedRelCupH …)`, whose
defining property (`Work.Cohomology.mixedRelCupH`) is exactly

`mixedCupC (class of a) (class of b) = class of (cup a b)`

for a cocycle `a` (absolute) and a relative cocycle `b`.  Two small naturality lemmas are needed to
put the two inputs into that shape:

* `CohMap_cohomologyClassOf` — the pullback `CohMap (pieceProj Z W) ℤ m` sends the cohomology
  class of the cocycle `a` to the class of the cochain-level pullback `pullAbs Z W m a`;
* `pdCohMap_classOf_tauRepAt` — the restriction `pdCohMap … τ` of `τ` to the piece over `W` is the
  relative cohomology class of the representative `tauRepAt Z n U τ W hW`.
-/

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι)

/-- **Naturality of the cohomology class under the pullback of a base cochain.**  The pullback
`CohMap (pieceProj Z W) ℤ m` of the singular-cohomology class of a cocycle `a : C^m(W;ℤ)` is the
class of the cochain-level pullback `pullAbs Z W m a` (with the induced cocycle condition). -/
lemma CohMap_cohomologyClassOf (W : Set B) (m : ℕ) (a : BaseC W m)
    (ha : cochainDiff ℤ (baseSSet W) a = 0) :
    (Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ m).hom
        (cohomologyClassOf ℤ (baseSSet W) a ha)
    = cohomologyClassOf ℤ (baseSSet (Z.proj ⁻¹' W)) (pullAbs Z W m a)
        (cochainDiff_dualMap_chainComplexMap ℤ
          (TopCat.toSSet.map (TopCat.ofHom (Work.Thom.pieceProj Z W))) a ha) := by
  exact singularCohomologyMap_classOf ℤ (TopCat.ofHom (Work.Thom.pieceProj Z W)) a ha

/-- **The restricted class `τ|_W` is the class of the representative `tauRepAt`.**  The restriction
`pdCohMap … τ` of a piece class `τ ∈ H^n(X|_U, X|_U∖0)` to a smaller piece `W ⊆ U` is the relative
cohomology class of the chosen representative `tauRepAt = (chosen representative of τ)|_W`. -/
lemma pdCohMap_classOf_tauRepAt (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (W : Set B) (hW : W ⊆ U) :
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hW) n).hom τ
    = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
        (tauRepAt Z n U τ W hW) (tauRepAt_cocycle Z n U τ W hW) := by
  have hclass : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hW) n).hom τ
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hW) n).hom
          (relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' U)) (relPiece Z U)
            (tauRep Z n U τ) (tauRep_cocycle Z n U τ)) := by
    rw [tauRep_class Z n U τ]
  have h := homologyMap_relComplexMap_relClassOf (R := ℤ)
      (X₁ := TopCat.of ↥(Z.proj ⁻¹' W)) (X₂ := TopCat.of ↥(Z.proj ⁻¹' U))
      (relPiece Z W) (relPiece Z U)
      (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace) (Z.proj ⁻¹' U) (Z.proj ⁻¹' W)
        (Set.preimage_mono hW)) (fun y hy => hy) (n := n) (tauRep Z n U τ) (tauRep_cocycle Z n U τ)
  rw [hclass]
  rw [show Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hW) n
      = HomologicalComplex.homologyMap
          (Work.Cohomology.relComplexMap ℤ
            (X₁ := TopCat.of ↥(Z.proj ⁻¹' W)) (X₂ := TopCat.of ↥(Z.proj ⁻¹' U))
            {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ Work.Thom.zeroComplement Z}
            {y : ↥(Z.proj ⁻¹' U) | (y : Z.TotalSpace) ∈ Work.Thom.zeroComplement Z}
            (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace) (Z.proj ⁻¹' U) (Z.proj ⁻¹' W)
              (Set.preimage_mono hW)) (fun y hy => hy)) n from rfl]
  rw [h]
  exact relClassOf_proof_irrel ℤ _ _ _ _ _

/-- **The `psiAbs`/`localThomMap` interface.**  For every degree `m` and every **cocycle**
`a : C^m(W)`, the relative cohomology class of the cochain-level cup `psiAbs … a` is the local Thom
map of the restricted class `τ|_W` applied to the class of `a`. -/
theorem psiClassHyp {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) :
    Work.ThomBordism.PsiClassHyp Z n U τ W hW := by
  intro m a ha hcyc
  -- Unfold the local Thom map into the mixed cup product of the base class with `τ|_W`.
  have hl := Work.Thom.localThomMap_apply Z n W
    ((ModuleCat.Hom.hom
        (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hW) n)) τ) m
    (cohomologyClassOf ℤ (baseSSet W) a ha)
  rw [hl]
  -- Replace the two inputs by the classes of their cochain-level representatives.
  rw [CohMap_cohomologyClassOf Z W m a ha]
  rw [pdCohMap_classOf_tauRepAt Z n U τ W hW]
  -- Apply the defining property of the mixed cup product to those representatives.
  obtain ⟨hmem, hc, heq⟩ := Classical.choose_spec
    (mixedRelCupH ℤ (TopCat.of ↥(Z.proj ⁻¹' W))
      ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' Work.Thom.zeroComplement Z))
    m n (pullAbs Z W m a) (tauRepAt Z n U τ W hW)
    (cochainDiff_dualMap_chainComplexMap ℤ
      (TopCat.toSSet.map (TopCat.ofHom (Work.Thom.pieceProj Z W))) a ha)
    (tauRepAt_cocycle Z n U τ W hW)
  -- The cochain-level cup is exactly `psiAbs`, so the two classes agree.
  have helem : (psiAbs Z n U τ W hW m a : ↥(relKern ℤ
        (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n)))
      = ⟨cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) (pullAbs Z W m a)
          ((tauRepAt Z n U τ W hW).1 : Cochain ℤ
            (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n), hmem⟩ := by
    apply Subtype.ext
    rfl
  have hA₁ : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
        (psiAbs Z n U τ W hW m a) hcyc
      = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
          ⟨cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) (pullAbs Z W m a)
            ((tauRepAt Z n U τ W hW).1 : Cochain ℤ
              (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n), hmem⟩ hc :=
    relClassOf_congr ℤ _ _ hcyc hc helem
  have hA₂ : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)
        ⟨cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) (pullAbs Z W m a)
          ((tauRepAt Z n U τ W hW).1 : Cochain ℤ
            (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n), hmem⟩ hc
      = relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W))
          ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' Work.Thom.zeroComplement Z)
          ⟨cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) (pullAbs Z W m a)
            ((tauRepAt Z n U τ W hW).1 : Cochain ℤ
              (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n), hmem⟩ hc := rfl
  refine (hA₁.trans hA₂).trans (heq.symm.trans ?_)
  rfl

end

end Work.ThomBordism
