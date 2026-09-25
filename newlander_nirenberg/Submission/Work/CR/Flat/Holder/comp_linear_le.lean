import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

/-- Composing a map `φ : X → A` with a continuous linear map `L : A →L[ℝ] B` multiplies
both the `C^i` sup-norm `iDN` and the `C^{i,α}` Hölder seminorm `hSN` on `Ω` by at most
the operator norm of `L`.

Both bounds are immediate from the chain rule for the iterated derivative of a left
composition with a continuous linear map,
`D^i (L ∘ φ) = L.compContinuousMultilinearMap (D^i φ)`, together with the bound
`‖L.compContinuousMultilinearMap m‖ ≤ ‖L‖ * ‖m‖`; in the Hölder case one additionally
uses that `compContinuousMultilinearMap` is linear in the multilinear-map argument, so
that the difference of the derivatives factors through `L`. -/
theorem comp_linear_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) (i : ℕ) (α : ℝ) {φ : X → A} {Ω : Set X}
    (hφ : ContDiffOn ℝ (i : ℕ∞) φ Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (L ∘ φ) Ω ≤ ENNReal.ofReal ‖L‖ * iDN i φ Ω ∧
      hSN i α (L ∘ φ) Ω ≤ ENNReal.ofReal ‖L‖ * hSN i α φ Ω := by
  constructor
  · refine iSup₂_le fun x hx => ?_
    have hb := L.norm_iteratedFDerivWithin_comp_left (hφ.contDiffWithinAt hx) hΩ hx (le_rfl)
    calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (L ∘ φ) Ω x‖
        ≤ ENNReal.ofReal (‖L‖ * ‖iteratedFDerivWithin ℝ i φ Ω x‖) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal ‖L‖ * ENNReal.ofReal ‖iteratedFDerivWithin ℝ i φ Ω x‖ :=
          ENNReal.ofReal_mul (norm_nonneg L)
      _ ≤ ENNReal.ofReal ‖L‖ * iDN i φ Ω := mul_le_mul_right (le_iDN i hx) _
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hb : ‖iteratedFDerivWithin ℝ i (L ∘ φ) Ω x - iteratedFDerivWithin ℝ i (L ∘ φ) Ω y‖
        ≤ ‖L‖ * ‖iteratedFDerivWithin ℝ i φ Ω x - iteratedFDerivWithin ℝ i φ Ω y‖ := by
      have e1 := L.iteratedFDerivWithin_comp_left (hφ.contDiffWithinAt hx) hΩ hx le_rfl
      have e2 := L.iteratedFDerivWithin_comp_left (hφ.contDiffWithinAt hy) hΩ hy le_rfl
      rw [e1, e2]
      have hsub : L.compContinuousMultilinearMap (iteratedFDerivWithin ℝ i φ Ω x)
          - L.compContinuousMultilinearMap (iteratedFDerivWithin ℝ i φ Ω y)
          = L.compContinuousMultilinearMap (iteratedFDerivWithin ℝ i φ Ω x
              - iteratedFDerivWithin ℝ i φ Ω y) := by
        rw [← ContinuousLinearMap.compContinuousMultilinearMapL_apply]
        exact (map_sub (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i => X)
          A B L) _ _).symm
      rw [hsub]
      exact L.norm_compContinuousMultilinearMap_le _
    have he : (0:ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    calc ENNReal.ofReal
            (‖iteratedFDerivWithin ℝ i (L ∘ φ) Ω x
              - iteratedFDerivWithin ℝ i (L ∘ φ) Ω y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (‖L‖ * (‖iteratedFDerivWithin ℝ i φ Ω x
              - iteratedFDerivWithin ℝ i φ Ω y‖ / ‖x - y‖ ^ α)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right hb he
      _ = ENNReal.ofReal ‖L‖ * ENNReal.ofReal (‖iteratedFDerivWithin ℝ i φ Ω x
              - iteratedFDerivWithin ℝ i φ Ω y‖ / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_mul (norm_nonneg L)
      _ ≤ ENNReal.ofReal ‖L‖ * hSN i α φ Ω := mul_le_mul_right (le_hSN i α hx hy hxy) _

end Work.CR.Flat.Holder
