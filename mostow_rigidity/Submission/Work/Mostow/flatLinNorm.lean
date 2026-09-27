import Mathlib
import Submission.Work.Mostow.stabFlatDefs

/-!
# The linear part of the flat horospherical action is an isometry

For `ξ ∈ Sph n`, a `J`-orthogonal matrix `M` with `M θ_ξ = θ_ξ`, and a vector `y ⊥ ξ`, the
linear part `flatLin ξ M` of the action of `M` on the flat coordinates of the horosphere at `ξ`
preserves the Euclidean norm of `y`.

This is the linear-algebraic content of "a horospherical isometry acts on the horosphere by an
affine isometry": `flatLin ξ M y` is the `V^⊥`-component of `M (y,0)`, and on `V^⊥` the Minkowski
form restricts to the ordinary Euclidean form.
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity Matrix

open scoped Matrix

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

private lemma hspat_wvec' (y : E n) : hspat (wvec y) = y := rfl

private lemma htime_wvec' (y : E n) : htime (wvec y) = 0 := rfl

/-- A vector of `ξ^⊥ ⊕ {0}` is fixed by the horospherical projection. -/
lemma horoProj_wvec' {n : ℕ} {ξ y : E n} (hy : inner ℝ y ξ = 0) :
    horoProj ξ (wvec y) = wvec y := by
  have h1 : mform (wvec y) (theta ξ) = 0 := by
    simp [mform_eq, hspat_wvec', htime_wvec', hy]
  have h2 : mform (wvec y) (horoEta ξ) = 0 := by
    simp [mform_eq, hspat_wvec', htime_wvec', hy]
  rw [horoProj, h1, h2]
  simp

/-- The Minkowski square of `(y,0)` is the Euclidean square of `y`. -/
lemma mform_wvec_self (y : E n) : mform (wvec y) (wvec y) = ‖y‖ ^ 2 := by
  rw [mform_eq]
  simp [hspat_wvec', htime_wvec']

theorem flatLinNorm {n : ℕ} (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (hO : Work.Mostow.IsJOrth M)
    (hθ : M.mulVec (Work.Mostow.theta ξ) = Work.Mostow.theta ξ)
    (y : Submission.Mostow.E n) (hy : inner ℝ y ξ = 0) :
    ‖Work.Mostow.flatLin ξ M y‖ = ‖y‖ := by
  -- `M θ = θ`, so the normal-form parameter is `w = 1`
  have hθ' : M *ᵥ theta ξ = (1 : ℝ) • theta ξ := by simpa using hθ
  -- `(y,0) ∈ V^⊥`, so `parabQ_isom` applies to it
  have hxy : horoProj ξ (wvec y) = wvec y := horoProj_wvec' hy
  have hpres := parabQ_isom ξ hξ hO hθ' (by norm_num) hxy hxy
  have hpres' : mform (horoProj ξ (M *ᵥ wvec y)) (horoProj ξ (M *ᵥ wvec y))
      = mform (wvec y) (wvec y) := by
    simpa [parabQ] using hpres
  -- on `V^⊥` the Minkowski form is the Euclidean form of the spatial part
  have hzidem : horoProj ξ (horoProj ξ (M *ᵥ wvec y)) = horoProj ξ (M *ᵥ wvec y) :=
    horoProj_idem ξ hξ (M *ᵥ wvec y)
  have hL : mform (horoProj ξ (M *ᵥ wvec y)) (horoProj ξ (M *ᵥ wvec y))
      = ‖hspat (horoProj ξ (M *ᵥ wvec y))‖ ^ 2 :=
    mform_eq_norm_sq_of_horoProj ξ hξ hzidem
  have hsq : ‖hspat (horoProj ξ (M *ᵥ wvec y))‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← hL, hpres', mform_wvec_self]
  have hs := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hs
  rw [flatLin_apply]
  exact hs

end

end Work.Mostow
