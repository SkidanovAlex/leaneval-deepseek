import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Fréchet differentiability of `uhsOfHyp`

The upper half space coordinate map `uhsOfHyp` sends a point `P` of `ℝ^{1,4}` to
`(P₀, P₁, P₂, 1) / (P₄ − P₃)`; it is smooth wherever `P₄ − P₃ ≠ 0`, and its derivative is the
explicit linear map `dUhsOfHyp P`.

The proof decomposes `uhsOfHyp` as the product of the scalar function `P ↦ (P₄ − P₃)⁻¹` and the
*affine* map `uhsNum P = (P₀, P₁, P₂, 1)`, and applies the product rule
`HasFDerivAt.smul`, the chain rule `HasFDerivAt.comp` and `hasFDerivAt_inv`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix
open ContinuousLinearMap (toSpanSingleton)

/-! ### The affine numerator of `uhsOfHyp` -/

/-- The affine numerator `P ↦ (P 0, P 1, P 2, 1)` of `uhsOfHyp`. -/
private def uhsNum (P : V5) : E4 := !₂[P 0, P 1, P 2, 1]

/-- The constant part of `uhsNum`. -/
private def uhsNumZero : E4 := !₂[0, 0, 0, 1]

/-- The linear part of `uhsNum`: `v ↦ (v 0, v 1, v 2, 0)`. -/
private def dUhsNum : V5 →L[ℝ] E4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v : V5 => !₂[v 0, v 1, v 2, 0]
      map_add' := by intro v w; ext i; fin_cases i <;> simp
      map_smul' := by intro c v; ext i; fin_cases i <;> simp }

/-- `uhsNum` is the sum of its constant and linear parts. -/
private theorem uhsNum_eq (P : V5) : uhsNum P = uhsNumZero + dUhsNum P := by
  ext i; fin_cases i <;> simp [uhsNum, uhsNumZero, dUhsNum]

/-- `uhsNum` is affine, with derivative the linear part `dUhsNum`. -/
private theorem hasFDerivAt_uhsNum (P : V5) : HasFDerivAt uhsNum dUhsNum P := by
  have hc : HasFDerivAt (fun _ : V5 => uhsNumZero) (0 : V5 →L[ℝ] E4) P :=
    hasFDerivAt_const _ _
  have h : HasFDerivAt ((fun _ : V5 => uhsNumZero) + ⇑dUhsNum) (0 + dUhsNum) P :=
    hc.add (ContinuousLinearMap.hasFDerivAt dUhsNum (x := P))
  have hfun : ((fun _ : V5 => uhsNumZero) + ⇑dUhsNum) = uhsNum := by
    funext Q; exact (uhsNum_eq Q).symm
  rw [hfun, zero_add] at h
  exact h

/-! ### The height functional and its inverse -/

/-- The linear functional `P ↦ P 4 - P 3`. -/
private def dHeight : V5 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (4 : Fin 5) : V5 →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj (3 : Fin 5) : V5 →L[ℝ] ℝ)

/-- The derivative of `P ↦ (P 4 - P 3)⁻¹` at a point where the height does not vanish. -/
private theorem hasFDerivAt_invHeight (P : V5) (hP : P 4 - P 3 ≠ 0) :
    HasFDerivAt (fun Q : V5 => (Q 4 - Q 3)⁻¹)
      (toSpanSingleton ℝ (-((P 4 - P 3) ^ 2)⁻¹) ∘L dHeight) P := by
  have h2 : HasFDerivAt (fun Q : V5 => Q 4 - Q 3) dHeight P :=
    (ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj (4 : Fin 5) : V5 →L[ℝ] ℝ)).sub
      (ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj (3 : Fin 5) : V5 →L[ℝ] ℝ))
  exact (hasFDerivAt_inv hP).comp P h2

/-- `uhsOfHyp` is the quotient of the affine numerator `uhsNum` by the height `P₄ - P₃`. -/
private theorem uhsOfHyp_eq (P : V5) :
    uhsOfHyp P = (P 4 - P 3)⁻¹ • uhsNum P := by
  simp only [uhsOfHyp, uhsNum]
  ext i; fin_cases i <;> simp <;> ring

theorem hasFDerivAt_uhsOfHyp {P : V5} (hP : P 4 - P 3 ≠ 0) :
    HasFDerivAt uhsOfHyp (dUhsOfHyp P) P := by
  have hnum : HasFDerivAt uhsNum dUhsNum P := hasFDerivAt_uhsNum P
  have hinv : HasFDerivAt (fun Q : V5 => (Q 4 - Q 3)⁻¹)
      (toSpanSingleton ℝ (-((P 4 - P 3) ^ 2)⁻¹) ∘L dHeight) P :=
    hasFDerivAt_invHeight P hP
  have hsmul := hinv.smul hnum
  have hfun : uhsOfHyp = (fun Q : V5 => (Q 4 - Q 3)⁻¹ • uhsNum Q) := by
    funext Q; exact uhsOfHyp_eq Q
  have hder : ((P 4 - P 3)⁻¹ • dUhsNum +
        (toSpanSingleton ℝ (-((P 4 - P 3) ^ 2)⁻¹) ∘L dHeight).smulRight (uhsNum P)) =
      dUhsOfHyp P := by
    ext v i
    fin_cases i <;>
      simp [dUhsOfHyp, dUhsNum, uhsNum, dHeight, ContinuousLinearMap.toSpanSingleton_apply] <;>
      ring
  have key : HasFDerivAt (fun Q : V5 => (Q 4 - Q 3)⁻¹ • uhsNum Q) (dUhsOfHyp P) P := by
    rw [hder] at hsmul
    exact hsmul
  rw [← hfun] at key
  exact key

end Work.HypModel
