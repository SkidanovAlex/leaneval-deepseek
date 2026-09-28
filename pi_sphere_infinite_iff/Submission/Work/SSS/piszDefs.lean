import Mathlib
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.iotaF_chainMap
import Submission.Work.SSS.coherentLiftDefs
import Submission.Work.SSS.ezSimplex_liftFam_coface
import Submission.Work.SSS.ssetVertex_delta_apply

/-!
# The `0`-face collapse: vocabulary

For a Serre fibration `p : E → B`, a simplex `σ : Δ[P+1] ⟶ Sing B` and a lift
`ez : Δ[P+1] ⊗ F ⟶ T_σ` of `pr₁ ≫ σ` (i.e. `ez ≫ pullback.fst = pr₁`), this file records

* `Work.SSS.faceLift` — the restriction of `ez` to the `i`-th face, the lift
  `Δ[P] ⊗ F ⟶ T_{δ i ≫ σ}` obtained from the pullback square, with
  `Work.SSS.faceLift_pullFaceIncl`: `faceLift ≫ pullFaceIncl = (δ i ⊗ 𝟙) ≫ ez`;
* `Work.SSS.vertIncl_coface` — the compatibility of the `v₀`-vertex inclusion with the last coface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
variable {X Y : SSet.{0}}

/-- **The restriction of a lift of the pullback to the `i`-th face.**  If
`ez : Δ[P+1] ⊗ F ⟶ T_σ` is a lift of `pr₁ ≫ σ` (i.e. `ez ≫ pullback.fst = pr₁`), then
`(δ i ⊗ 𝟙) ≫ ez` has first projection `pr₁ ≫ δ i`, hence factors through the inclusion of the face
`T_{δ i ≫ σ} ⟶ T_σ`; `faceLift f σ ez hez i` is that factorisation. -/
noncomputable def faceLift {F : SSet.{0}} {P : ℕ}
    (f : X ⟶ Y)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Y)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (i : Fin (P+2)) :
    (((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})) ⊗ F) ⟶
      pullAlong f (SSet.stdSimplex.δ (n := P) i ≫ σ) :=
  pullback.lift (SemiCartesianMonoidalCategory.fst _ _)
    ((SSet.stdSimplex.δ (n := P) i ⊗ₘ 𝟙 F) ≫ ez ≫ pullback.snd σ f)
    (by
      simp only [Category.assoc]
      rw [← pullback.condition, ← Category.assoc ez (pullback.fst σ f) σ, hez,
        ← Category.assoc (SSet.stdSimplex.δ (n := P) i ⊗ₘ 𝟙 F)
          (SemiCartesianMonoidalCategory.fst
            (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F) σ,
        CartesianMonoidalCategory.tensorHom_fst, Category.assoc])

@[simp] lemma faceLift_fst {F : SSet.{0}} {P : ℕ} (f : X ⟶ Y)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Y)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (i : Fin (P+2)) :
    faceLift f σ ez hez i ≫ pullback.fst (SSet.stdSimplex.δ (n := P) i ≫ σ) f
      = SemiCartesianMonoidalCategory.fst _ _ :=
  pullback.lift_fst _ _ _

@[simp] lemma faceLift_snd {F : SSet.{0}} {P : ℕ} (f : X ⟶ Y)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Y)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (i : Fin (P+2)) :
    faceLift f σ ez hez i ≫ pullback.snd (SSet.stdSimplex.δ (n := P) i ≫ σ) f
      = (SSet.stdSimplex.δ (n := P) i ⊗ₘ 𝟙 F) ≫ ez ≫ pullback.snd σ f :=
  pullback.lift_snd _ _ _

/-- **The defining property of the face restriction**: including it into `T_σ` gives the face
restriction of `ez`. -/
theorem faceLift_pullFaceIncl {F : SSet.{0}} {P : ℕ} (f : X ⟶ Y)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Y)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (i : Fin (P+2)) :
    faceLift f σ ez hez i ≫ pullFaceIncl f σ i
      = (SSet.stdSimplex.δ (n := P) i ⊗ₘ 𝟙 F) ≫ ez := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullFaceIncl_fst, ← Category.assoc, faceLift_fst]
    rw [Category.assoc, hez, CartesianMonoidalCategory.tensorHom_fst]
  · rw [Category.assoc, pullFaceIncl_snd, faceLift_snd]
    simp only [Category.assoc]

/-- The vertex inclusion `τ ↦ (v₀, τ)` is compatible with the last coface (which fixes `v₀`). -/
theorem vertIncl_coface (p : C(E, B)) (b : B) (P : ℕ) :
    vertIncl p b P ≫ (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ⊗ₘ 𝟙
        (sSing (Work.StemsB.fibre p b))) = vertIncl p b (P+1) := by
  have hlast : Fin.last (P+1) ≠ (0 : Fin (P+2)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp [Fin.last] at hv
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.tensorHom_fst, vertIncl_fst,
      ← Category.assoc, vertIncl_fst, SSet.const_comp,
      ssetVertex_delta_apply (n := P) (Fin.last (P+1)) hlast]
  · rw [Category.assoc, CartesianMonoidalCategory.tensorHom_snd, ← Category.assoc,
      vertIncl_snd, Category.id_comp, vertIncl_snd]

end

end Work.SSS
