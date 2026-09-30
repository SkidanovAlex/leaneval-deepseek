import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.hypOfKlein_injOn
import Submission.Work.HypModel.hypOfKlein_kleinOfHyp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- **The central projection sends the upper sheet into the open unit ball.**  Writing
`y = kleinOfHyp P = (P₄)⁻¹ • proj4 P`, the Lorentz identity `⟨P,P⟩ = -1` gives
`‖proj4 P‖² = P₄² - 1`, hence `‖y‖² = 1 - (P₄)⁻¹² < 1` because `P₄ > 0`; as `‖y‖ ≥ 0` this
forces `‖y‖ < 1`. -/
theorem kleinOfHyp_mem_ball_of_upperSheet {P : V5} (hP : P ∈ upperSheet) :
    kleinOfHyp P ∈ ball := by
  have h4 : 0 < P 4 := hP.2
  have h4ne : P 4 ≠ 0 := ne_of_gt h4
  -- The Lorentz identity `⟨P,P⟩ = -1` as a statement about squares of coordinates.
  have hsos : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 = P 4 ^ 2 - 1 := by
    have h := hP.1
    simp only [lorentz] at h
    nlinarith
  -- The norm of the first four coordinates.
  have hproj : ‖proj4 P‖ ^ 2 = P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    simp [dotProduct, proj4, Fin.sum_univ_four]
    ring
  have hnormsq : ‖kleinOfHyp P‖ ^ 2 = ((P 4)⁻¹) ^ 2 * ‖proj4 P‖ ^ 2 := by
    rw [kleinOfHyp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hnorm : ‖kleinOfHyp P‖ ^ 2 = 1 - ((P 4)⁻¹) ^ 2 := by
    rw [hnormsq, hproj, hsos]
    field_simp
  show ‖kleinOfHyp P‖ < 1
  have hlt : ‖kleinOfHyp P‖ ^ 2 < 1 := by
    rw [hnorm]
    have hpos : 0 < ((P 4)⁻¹) ^ 2 := by positivity
    linarith
  nlinarith [norm_nonneg (kleinOfHyp P)]

/-- **The Klein model parametrisation `hypOfKlein : ball → upperSheet` is a bijection.**  The three
components of `Set.BijOn` are:

* `Set.MapsTo`: for `y ∈ ball` the lift `(y,1)/√(1−|y|²)` lies on the upper sheet
  (`hypOfKlein_mem_upperSheet`);
* `Set.InjOn`: `hypOfKlein_injOn`, because the last coordinate of the lift is the nonzero scalar
  `(√(1−|y|²))⁻¹` and the first four coordinates are the ray `y`;
* `Set.SurjOn`: a point `P ∈ upperSheet` is the image of its central projection
  `y := kleinOfHyp P`, which lies in the open unit ball (`kleinOfHyp_mem_ball_of_upperSheet`) and
  satisfies `hypOfKlein (kleinOfHyp P) = P` (`hypOfKlein_kleinOfHyp`). -/
theorem hypOfKlein_bijOn : Set.BijOn hypOfKlein ball upperSheet :=
  ⟨fun _ hy => hypOfKlein_mem_upperSheet hy, hypOfKlein_injOn,
   fun P hP => ⟨kleinOfHyp P, kleinOfHyp_mem_ball_of_upperSheet hP, hypOfKlein_kleinOfHyp hP⟩⟩

end Work.HypModel
