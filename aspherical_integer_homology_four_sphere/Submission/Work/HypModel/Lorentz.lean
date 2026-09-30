import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Lorentz group acting on the hyperboloid

Basic consequences of `IsLorentzMat A` (i.e. `Aᵀ J A = J` and `A 4 4 > 0`): a Lorentz matrix
preserves the Lorentz form, the upper sheet, and hence acts on the Klein and upper half space
models.  Also the identification of the derivatives of the three charts.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- A Lorentz matrix preserves the Lorentz form. -/
theorem lorentz_mulVec {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) (x y : V5) :
    lorentz (A *ᵥ x) (A *ᵥ y) = lorentz x y := by
  rw [lorentz_eq_dotProduct, lorentz_eq_dotProduct, dotProduct_mulVec_transpose]
  congr 1
  rw [mulVec_mulVec, mulVec_mulVec, hA.1]

/-- A Lorentz matrix with `A 4 4 > 0` preserves the upper sheet of the hyperboloid. -/
theorem mulVec_mem_upperSheet {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) {x : V5}
    (hx : x ∈ upperSheet) : A *ᵥ x ∈ upperSheet := by
  refine ⟨by rw [lorentz_mulVec hA, hx.1], ?_⟩
  refine four_pos_of_lorentz_pair_neg (u := A *ᵥ x) (v := A *ᵥ timeVec)
    (by rw [lorentz_mulVec hA, hx.1]) (by rw [lorentz_mulVec hA, lorentz_timeVec_self])
    (by rw [mulVec_timeVec_four]; exact hA.2) ?_
  rw [lorentz_mulVec hA, lorentz_left_timeVec]
  linarith [hx.2]

/-- The Lorentz group is closed under multiplication. -/
theorem IsLorentzMat.mul {A B : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hB : IsLorentzMat B) : IsLorentzMat (A * B) := by
  refine ⟨?_, ?_⟩
  · rw [transpose_mul]
    calc Bᵀ * Aᵀ * J * (A * B) = Bᵀ * (Aᵀ * J * A) * B := by noncomm_ring
      _ = Bᵀ * J * B := by rw [hA.1]
      _ = J := hB.1
  · rw [← mulVec_timeVec_four (A * B), ← mulVec_mulVec]
    exact (mulVec_mem_upperSheet hA (mulVec_mem_upperSheet hB timeVec_mem_upperSheet)).2

theorem IsLorentzMat.one : IsLorentzMat 1 := IsLorentzMat_one

/-- The derivative of `hypOfUHS` is the explicit linear map `dHypOfUHS q`. -/
theorem fderiv_hypOfUHS {q : E4} (hq : q 3 ≠ 0) : fderiv ℝ hypOfUHS q = dHypOfUHS q :=
  (hasFDerivAt_hypOfUHS hq).fderiv

/-- The derivative of `uhsOfHyp` is the explicit linear map `dUhsOfHyp P`. -/
theorem fderiv_uhsOfHyp {P : V5} (hP : P 4 - P 3 ≠ 0) :
    fderiv ℝ uhsOfHyp P = dUhsOfHyp P :=
  (hasFDerivAt_uhsOfHyp hP).fderiv

end Work.HypModel
