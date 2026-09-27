import Mathlib
import Submission.Work.Surf.tame_cut_parity
import Submission.Work.Drive.EZCSetup

/-!
# The perturbed auxiliary family for the smooth cut/ray parity

`Work.Surf.tame_cut_parity` proves the cut/ray parity for a family `cutMap F v (σ,x) = F x - σ • v`
that is *tame*: at every point of the square where `F` is parallel to `v`, the derivative of `F`
together with `ℝv` spans the plane, so that `0` is a regular value of `cutMap F v` on the cube.

For the smooth version (`Work.Surf.smooth_cut_parity`) no tameness is assumed, and the family is
perturbed in the interior of the cube by `σ (1 - σ) χ x • w`.  The perturbation

* vanishes on the faces `σ = 0`, `σ = 1` (factor `σ (1-σ)`), and
* vanishes on the side faces of the cube (the bump `χ` is supported on the interior of the square),

so that the *boundary zeros* of the perturbed family `scpG F v w` are exactly those of `cutMap F v`;
while in the interior of the cube the perturbation can be chosen generically (`w` outside the critical
values of the "solution map" `scpSol`, weak Sard on `𝔼³ → 𝔼²`) so that all interior zeros become
regular.
-/

namespace Work.Surf

open Set

noncomputable section

/-- `φ t = smoothTransition t * smoothTransition (1 - t)`: smooth, nonnegative, and positive exactly
on `(0,1)`. -/
def scpPhi (t : ℝ) : ℝ := Real.smoothTransition t * Real.smoothTransition (1 - t)

/-- The interior bump `χ (x₀, x₁) = φ x₀ * φ x₁`: smooth, nonnegative, vanishing exactly on the
boundary of the square `[0,1]²` and positive on its interior. -/
def scpChi (x : EuclideanSpace ℝ (Fin 2)) : ℝ := scpPhi (x 0) * scpPhi (x 1)

/-- The perturbation term `z ↦ σ (1 - σ) χ x • w`, `z = (σ, x)`. -/
def scpPert (w : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) :=
  (Work.Drive.ezPhi (cutSig z) * scpChi (cutSp z)) • w

/-- The perturbed auxiliary family `scpG F v w (σ,x) = F x - σ • v - σ (1-σ) χ x • w`. -/
def scpG (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
  fun z => F (cutSp z) - cutSig z • v - scpPert w z

/-- The **solution map** of the interior perturbation: at an interior zero `z` of `scpG F v w` one has
`w = scpSol F v z`, and `w` is a regular value of `scpSol F v` on `scpU` exactly when every interior
zero of `scpG F v w` is a regular point. -/
def scpSol (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  (Work.Drive.ezPhi (cutSig z) * scpChi (cutSp z))⁻¹ • (F (cutSp z) - cutSig z • v)

/-- The open set on which the perturbation factor `σ (1-σ) χ x` does not vanish: the cube points
strictly above the interior of the square and strictly between the faces `σ = 0` and `σ = 1`. -/
def scpU : Set (EuclideanSpace ℝ (Fin 3)) :=
  {z | 0 < cutSig z ∧ cutSig z < 1 ∧ 0 < scpChi (cutSp z)}

/-- The interior of the cube `[0,1]³`. -/
def scpIntBox : Set (EuclideanSpace ℝ (Fin 3)) := {z | ∀ i : Fin 3, 0 < z i ∧ z i < 1}

@[simp] theorem scpG_apply (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v w : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    scpG F v w z = F (cutSp z) - cutSig z • v - scpPert w z := rfl

@[simp] theorem scpPert_apply (w : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    scpPert w z =
      (Work.Drive.ezPhi (cutSig z) * scpChi (cutSp z)) • w := rfl

end

end Work.Surf
