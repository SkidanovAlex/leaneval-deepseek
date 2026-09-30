import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.mobius_contDiffOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Möbius action is a (right) action of the Lorentz group

The Möbius transformation of the upper half space model attached to a Lorentz matrix `A` is

`mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)`,

where `hypOfUHS q = (q₀/q₃, q₁/q₃, q₂/q₃, (‖q‖²−1)/(2q₃), (‖q‖²+1)/(2q₃))` parametrises the upper
sheet of the hyperboloid by the upper half space and `uhsOfHyp P = (P₀,P₁,P₂,1)/(P₄−P₃)` is its
inverse on that sheet.

Because the two defining maps are *exact* inverses on the upper sheet
(`hypOfUHS_uhsOfHyp`) and the linear action of a Lorentz matrix preserving the time orientation
carries the upper sheet into itself (`isLorentzMat_mem_upperSheet`), the composite behaves as the
matrix product:

`mobius (A * B) q = mobius A (mobius B q)` for `0 < q 3`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix

/-- **A Lorentz matrix preserving the upper sheet sends the upper sheet into itself.**
`B *ᵥ P` is again on the hyperboloid since `B` preserves the Lorentz form; it is future directed
because its pairing with the future directed `B *ᵥ timeVec` equals `⟨P, timeVec⟩ = -P₄ < 0`. -/
theorem isLorentzMat_mem_upperSheet {B : Matrix (Fin 5) (Fin 5) ℝ} (hB : IsLorentzMat B)
    {P : V5} (hP : P ∈ upperSheet) : B *ᵥ P ∈ upperSheet := by
  refine ⟨?_, ?_⟩
  · rw [lorentz_mulVec_of_isLorentzMat hB]; exact hP.1
  · have hvv : lorentz (B *ᵥ timeVec) (B *ᵥ timeVec) = -1 := by
      rw [lorentz_mulVec_of_isLorentzMat hB, lorentz_timeVec_self]
    have hv4 : 0 < (B *ᵥ timeVec) 4 := by
      rw [mulVec_timeVec_four]; exact hB.2
    have huv : lorentz (B *ᵥ P) (B *ᵥ timeVec) < 0 := by
      rw [lorentz_mulVec_of_isLorentzMat hB, lorentz_left_timeVec]
      linarith [hP.2]
    exact four_pos_of_lorentz_pair_neg (by rw [lorentz_mulVec_of_isLorentzMat hB]; exact hP.1)
      hvv hv4 huv

/-- **The Möbius action is multiplicative.**  Writing `Q := B *ᵥ hypOfUHS q`, which lies on the
upper sheet, the two sides are `uhsOfHyp ((A * B) *ᵥ hypOfUHS q)` and
`uhsOfHyp (A *ᵥ hypOfUHS (uhsOfHyp Q))`, and these agree because
`hypOfUHS (uhsOfHyp Q) = Q`. -/
theorem mobius_mul {A B : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) (hB : IsLorentzMat B)
    {q : E4} (hq : 0 < q 3) : mobius (A * B) q = mobius A (mobius B q) := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  have hP : hypOfUHS q ∈ upperSheet := ⟨lorentz_hypOfUHS_self hq3, hypOfUHS_four_pos hq⟩
  have hQ : B *ᵥ hypOfUHS q ∈ upperSheet := isLorentzMat_mem_upperSheet hB hP
  rw [mobius, mobius, mobius, ← Matrix.mulVec_mulVec (hypOfUHS q) A B, hypOfUHS_uhsOfHyp hQ]

end Work.HypModel
