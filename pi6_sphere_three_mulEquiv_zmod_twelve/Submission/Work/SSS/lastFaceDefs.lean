import Mathlib
import Submission.Work.SSS.serreE1PieceDefs

/-!
# The pasting map onto the last face of a simplex

For a morphism of simplicial sets `f : X ⟶ Y` and a simplex `σ : Δ[t+1] ⟶ Y`, the last face of
`Δ[t+1]` is the image of `δ := SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) : Δ[t] ⟶ Δ[t+1]`.  The
pasting of the pullback squares exhibits `Δ[t] ×_Y X` as the preimage of this last face inside
`Δ[t+1] ×_Y X`; the map doing so is `lastFaceMap f t σ`.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

/-- The **last-face pasting map** `Δ[t] ×_Y X ⟶ Δ[t+1] ×_Y X`, whose image is the preimage of the
last face `d_{t+1}Δ[t+1] ⊆ Δ[t+1]` under the first projection. -/
def lastFaceMap {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    pullback (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f ⟶ pullback σ f :=
  pullback.lift
    (pullback.fst (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f ≫
      SSet.stdSimplex.δ (n := t) (Fin.last (t+1)))
    (pullback.snd (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f)
    (by rw [Category.assoc, pullback.condition])

/-- The first projection of the pasting map. -/
@[reassoc (attr := simp)]
lemma lastFaceMap_fst {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    lastFaceMap f t σ ≫ pullback.fst σ f =
      pullback.fst (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f ≫
        SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) :=
  pullback.lift_fst _ _ _

/-- The second projection of the pasting map. -/
@[reassoc (attr := simp)]
lemma lastFaceMap_snd {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    lastFaceMap f t σ ≫ pullback.snd σ f =
      pullback.snd (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f :=
  pullback.lift_snd _ _ _

/-- The pasting square is a pullback square: `Δ[t] ×_Y X` is the pullback of the last-face
inclusion `δ : Δ[t] ⟶ Δ[t+1]` along the first projection of `Δ[t+1] ×_Y X`. -/
theorem lastFaceMap_isPullback {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    IsPullback (lastFaceMap f t σ)
      (pullback.fst (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f)
      (pullback.fst σ f)
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) := by
  exact IsPullback.of_right (X₁₃ := X) (X₂₃ := Y)
    (h₁₂ := pullback.snd σ f) (h₂₂ := σ) (v₁₃ := f)
    (by
      rw [lastFaceMap_snd]
      exact IsPullback.flip
        (IsPullback.of_hasPullback (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) f))
    (by rw [lastFaceMap_fst])
    (IsPullback.flip (IsPullback.of_hasPullback σ f))

/-- The pasting map is a monomorphism (the inclusion of a subcomplex). -/
theorem lastFaceMap_mono {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Mono (lastFaceMap f t σ) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (lastFaceMap_isPullback f t σ).isLimit

end

end Work.SSS
