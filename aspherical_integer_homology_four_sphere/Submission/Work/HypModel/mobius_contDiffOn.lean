import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Smoothness of the Möbius action on the upper half space model

`mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)` is the action of a Lorentz matrix `A` on the upper half
space model of hyperbolic 4-space.  We prove that for `A` in the (orthochronous) Lorentz group it
is `C^∞` on the open upper half space `upperHalfSpace = {q : 0 < q 3}`.

The proof is a composition of three smooth maps:

* `hypOfUHS` is `C^∞` on `upperHalfSpace` (its coordinates are the rational functions
  `qᵢ/q₃` and `(‖q‖²±1)/(2q₃)`, denominators nonvanishing there);
* `P ↦ A *ᵥ P` is linear, hence `C^∞`;
* `uhsOfHyp` is `C^∞` on the open set `{P : 0 < P₄ − P₃}` where the height does not vanish.

The only point where the Lorentz hypothesis enters is the last: the image of `upperHalfSpace` under
`q ↦ A *ᵥ hypOfUHS q` lies on the upper sheet of the hyperboloid, where the height `P₄ − P₃` is
positive.  This uses that `A` preserves the Lorentz form, so that the resulting vector is again on
the hyperboloid, and the time orientation `A 4 4 > 0` to see that it is on the *upper* sheet.
-/

noncomputable section

open scoped Matrix InnerProductSpace
open Matrix

namespace Work.HypModel

/-- A matrix satisfying `Aᵀ J A = J` preserves the Lorentz form. -/
theorem lorentz_mulVec_of_isLorentzMat {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (x y : V5) : lorentz (A *ᵥ x) (A *ᵥ y) = lorentz x y := by
  rw [lorentz_eq_dotProduct, lorentz_eq_dotProduct, dotProduct_mulVec_transpose]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA.1]

/-- The open set where the height function `P ↦ P 4 - P 3` is positive. -/
private def heightPos : Set V5 := {P : V5 | 0 < P 4 - P 3}

/-- **`hypOfUHS` is smooth on the upper half space.**  Its coordinates are `qᵢ/q₃` for
`i = 0,1,2` and `(‖q‖² ∓ 1)/(2q₃)` for the last two, and `q₃ > 0` on `upperHalfSpace`. -/
theorem contDiffOn_hypOfUHS : ContDiffOn ℝ ⊤ hypOfUHS upperHalfSpace := by
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · show ContDiffOn ℝ ⊤ (fun x : E4 => x 0 / x 3) upperHalfSpace
    apply ContDiffOn.div
    · exact (EuclideanSpace.proj (0 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · intro x hx; exact ne_of_gt hx
  · show ContDiffOn ℝ ⊤ (fun x : E4 => x 1 / x 3) upperHalfSpace
    apply ContDiffOn.div
    · exact (EuclideanSpace.proj (1 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · intro x hx; exact ne_of_gt hx
  · show ContDiffOn ℝ ⊤ (fun x : E4 => x 2 / x 3) upperHalfSpace
    apply ContDiffOn.div
    · exact (EuclideanSpace.proj (2 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · intro x hx; exact ne_of_gt hx
  · show ContDiffOn ℝ ⊤ (fun x : E4 => (‖x‖ ^ 2 - 1) / (2 * x 3)) upperHalfSpace
    apply ContDiffOn.div
    · exact ((contDiff_norm_sq (𝕜 := ℝ)).sub contDiff_const).contDiffOn
    · have h1 : ContDiff ℝ ⊤ (fun _ : E4 => (2 : ℝ)) := contDiff_const
      have h2 : ContDiff ℝ ⊤ (fun x : E4 => x 3) :=
        (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff
      exact (h1.mul h2).contDiffOn
    · intro x hx
      have hx3 : (0 : ℝ) < x 3 := hx
      have : (0 : ℝ) < 2 * x 3 := by linarith
      exact ne_of_gt this
  · show ContDiffOn ℝ ⊤ (fun x : E4 => (‖x‖ ^ 2 + 1) / (2 * x 3)) upperHalfSpace
    apply ContDiffOn.div
    · exact ((contDiff_norm_sq (𝕜 := ℝ)).add contDiff_const).contDiffOn
    · have h1 : ContDiff ℝ ⊤ (fun _ : E4 => (2 : ℝ)) := contDiff_const
      have h2 : ContDiff ℝ ⊤ (fun x : E4 => x 3) :=
        (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff
      exact (h1.mul h2).contDiffOn
    · intro x hx
      have hx3 : (0 : ℝ) < x 3 := hx
      have : (0 : ℝ) < 2 * x 3 := by linarith
      exact ne_of_gt this

/-- **`uhsOfHyp` is smooth wherever the height `P 4 - P 3` is positive.**  Each coordinate is
`Pᵢ · (P₄ − P₃)⁻¹` (or `(P₄ − P₃)⁻¹`). -/
theorem contDiffOn_uhsOfHyp : ContDiffOn ℝ ⊤ uhsOfHyp heightPos := by
  have hsub : ContDiffOn ℝ ⊤ (fun P : V5 => P 4 - P 3) heightPos :=
    ((ContinuousLinearMap.proj (4 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn).sub
      ((ContinuousLinearMap.proj (3 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn)
  have h1 : ContDiffOn ℝ ⊤ (fun P : V5 => (P 4 - P 3)⁻¹) heightPos :=
    hsub.inv (fun P hP => ne_of_gt hP)
  rw [contDiffOn_piLp (p := 2) (E := fun _ : Fin 4 => ℝ)]
  intro i
  fin_cases i
  · show ContDiffOn ℝ ⊤ (fun P : V5 => P 0 * (P 4 - P 3)⁻¹) heightPos
    exact ((ContinuousLinearMap.proj (0 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn).mul h1
  · show ContDiffOn ℝ ⊤ (fun P : V5 => P 1 * (P 4 - P 3)⁻¹) heightPos
    exact ((ContinuousLinearMap.proj (1 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn).mul h1
  · show ContDiffOn ℝ ⊤ (fun P : V5 => P 2 * (P 4 - P 3)⁻¹) heightPos
    exact ((ContinuousLinearMap.proj (2 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn).mul h1
  · show ContDiffOn ℝ ⊤ (fun P : V5 => (P 4 - P 3)⁻¹) heightPos
    exact h1

/-- The linear map `P ↦ A *ᵥ P` is `C^∞`. -/
theorem contDiff_mulVec (A : Matrix (Fin 5) (Fin 5) ℝ) :
    ContDiff ℝ ⊤ (fun P : V5 => A *ᵥ P) := by
  have h : (fun P : V5 => A *ᵥ P) = ⇑((Matrix.mulVecLin A).toContinuousLinearMap) := by
    funext P
    rw [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]
  rw [h]
  exact (Matrix.mulVecLin A).toContinuousLinearMap.contDiff

/-- The Möbius action `mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)` of a Lorentz matrix on the upper
half space is smooth. -/
theorem mobius_contDiffOn {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    ContDiffOn ℝ ⊤ (mobius A) upperHalfSpace := by
  have hcomp : ContDiffOn ℝ ⊤ (fun q => A *ᵥ hypOfUHS q) upperHalfSpace :=
    (contDiff_mulVec A).comp_contDiffOn contDiffOn_hypOfUHS
  have hmaps : Set.MapsTo (fun q => A *ᵥ hypOfUHS q) upperHalfSpace heightPos := by
    intro q hq
    have hq3 : 0 < q 3 := hq
    have hP : hypOfUHS q ∈ upperSheet :=
      ⟨lorentz_hypOfUHS_self (ne_of_gt hq3), hypOfUHS_four_pos hq3⟩
    have hQQ : lorentz (A *ᵥ hypOfUHS q) (A *ᵥ hypOfUHS q) = -1 := by
      rw [lorentz_mulVec_of_isLorentzMat hA]; exact hP.1
    have hvv : lorentz (A *ᵥ timeVec) (A *ᵥ timeVec) = -1 := by
      rw [lorentz_mulVec_of_isLorentzMat hA]
      exact lorentz_timeVec_self
    have hv4 : 0 < (A *ᵥ timeVec) 4 := by rw [mulVec_timeVec_four]; exact hA.2
    have huv : lorentz (A *ᵥ hypOfUHS q) (A *ᵥ timeVec) < 0 := by
      rw [lorentz_mulVec_of_isLorentzMat hA, lorentz_left_timeVec]
      have := hypOfUHS_four_pos hq3
      linarith
    have hQ4 : 0 < (A *ᵥ hypOfUHS q) 4 := four_pos_of_lorentz_pair_neg hQQ hvv hv4 huv
    exact upperSheet_four_sub_three_pos ⟨hQQ, hQ4⟩
  have key := contDiffOn_uhsOfHyp.comp hcomp hmaps
  exact key.congr (fun q _ => rfl)

end Work.HypModel
