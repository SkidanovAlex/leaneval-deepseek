import Submission.Work.CoreTopology.Disk

/-!
# Tori that are images of the standard torus under a homeomorphism of `ℝ³`

Pardon's theorem is applied to the image of the standard torus of revolution under an ambient
isotopy, i.e. to a torus `F' = ψ(F)` for a homeomorphism `ψ : ℝ³ ≃ₜ ℝ³`, with the knot the
image of the standard `(p,q)`-curve.  This file sets up that setting in the vocabulary of
`Work.CoreTopology`: `ParamTorus.mapHomeomorph ψ` is the parametrised torus
`(x, y) ↦ ψ (torusMap x y)`, and `ClosedCurve.mapHomeomorph ψ γ` is the image of the closed
curve `γ`.  All the topological notions of this directory transport along `ψ`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- The image of the standard torus of revolution under a homeomorphism `ψ` of `ℝ³`. -/
def ParamTorus.mapHomeomorph (ψ : R3 ≃ₜ R3) : ParamTorus where
  psi := fun x y => ψ (Work.Core.torusMap x y)
  cont := by
    have h : Function.uncurry (fun x y : ℝ => ψ (Work.Core.torusMap x y)) =
        (⇑ψ) ∘ (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) := rfl
    rw [h]
    exact ψ.continuous.comp torusMap_continuous
  per_left := fun x y => by rw [Work.Core.torusMap_add_two_pi_left]
  per_right := fun x y => by rw [Work.Core.torusMap_add_two_pi_right]
  inj_mod := fun x y x' y' => by
    rw [ψ.injective.eq_iff, Work.Core.torusMap_eq_iff]

@[simp] theorem ParamTorus.mapHomeomorph_psi (ψ : R3 ≃ₜ R3) (x y : ℝ) :
    (ParamTorus.mapHomeomorph ψ).psi x y = ψ (Work.Core.torusMap x y) := rfl

/-- The image of a closed curve on the standard torus under a homeomorphism of `ℝ³`. -/
def ClosedCurve.mapHomeomorph (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard) :
    ClosedCurve (ParamTorus.mapHomeomorph ψ) where
  γ := ⇑ψ ∘ γ.γ
  cont := ψ.continuous.comp γ.cont
  periodic := fun t => by simp only [Function.comp_apply, γ.periodic t]
  mem := fun t => by
    obtain ⟨p, hp⟩ := γ.mem t
    have hp' : standard.psi p.1 p.2 = γ.γ t := hp
    exact ⟨p, by
      show ψ (standard.psi p.1 p.2) = ψ (γ.γ t)
      rw [hp']⟩

@[simp] theorem ClosedCurve.mapHomeomorph_apply (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard)
    (t : ℝ) : (ClosedCurve.mapHomeomorph ψ γ) t = ψ (γ t) := rfl

/-- Pull a closed curve on `ParamTorus.mapHomeomorph ψ` back to the standard torus. -/
def ClosedCurve.mapHomeomorphInv (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) : ClosedCurve standard where
  γ := ⇑(ψ.symm) ∘ γ.γ
  cont := ψ.symm.continuous.comp γ.cont
  periodic := fun t => by simp only [Function.comp_apply, γ.periodic t]
  mem := fun t => by
    obtain ⟨p, hp⟩ := γ.mem t
    have hp' : ψ (standard.psi p.1 p.2) = γ.γ t := hp
    refine ⟨p, ?_⟩
    show standard.psi p.1 p.2 = ψ.symm (γ.γ t)
    rw [← hp', ψ.symm_apply_apply]

@[simp] theorem ClosedCurve.mapHomeomorphInv_apply (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) (t : ℝ) :
    (ClosedCurve.mapHomeomorphInv ψ γ) t = ψ.symm (γ t) := rfl

theorem ClosedCurve.mapHomeomorph_isSimple (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard)
    (h : IsSimple standard γ) : IsSimple (ParamTorus.mapHomeomorph ψ)
      (ClosedCurve.mapHomeomorph ψ γ) :=
  fun _ ht _ ht' h' => h ht ht' (ψ.injective h')

/-- Pushing a closed curve forward along a homeomorphism does not change the winding vector:
the parameters of a lift of `γ` are also parameters of a lift of the image of `γ`. -/
theorem ClosedCurve.winding_mapHomeomorph (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard)
    (L : LiftOf standard γ) :
    ∃ L' : LiftOf (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ γ),
      L'.winding = L.winding := by
  have hlifts : ∀ t : ℝ, (ParamTorus.mapHomeomorph ψ).psi (L.Θ t) (L.Φ t)
      = (ClosedCurve.mapHomeomorph ψ γ).γ t := by
    intro t
    show ψ (standard.psi (L.Θ t) (L.Φ t)) = ψ (γ.γ t)
    rw [L.lifts t]
  let L' : LiftOf (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ γ) :=
    { Θ := L.Θ, Φ := L.Φ, contΘ := L.contΘ, contΦ := L.contΦ, lifts := hlifts }
  exact ⟨L', LiftOf.winding_congr L L' (fun _ => rfl) (fun _ => rfl)⟩

/-- The winding vector of a closed curve on the standard torus and of its image under a
homeomorphism of `ℝ³` are one and the same: being essential transports. -/
theorem ClosedCurve.isEssential_mapHomeomorph (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard)
    (h : IsEssential standard γ) : IsEssential (ParamTorus.mapHomeomorph ψ)
      (ClosedCurve.mapHomeomorph ψ γ) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨L', hL'⟩ := ClosedCurve.winding_mapHomeomorph ψ γ L
  exact ⟨L', by rw [hL']; exact hL⟩

end

end Work.CoreTopology
