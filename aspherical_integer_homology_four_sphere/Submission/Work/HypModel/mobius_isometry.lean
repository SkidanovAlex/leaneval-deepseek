import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp
import Submission.Work.HypModel.lorentz_dHypOfUHS
import Submission.Work.HypModel.tangent_hypOfUHS
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Möbius action of a Lorentz matrix on the upper half space is an isometry

`mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)` is the action on the upper half space model of the
Lorentz transformation `A` (`Aᵀ J A = J`, `A 4 4 > 0`), transported from the hyperboloid through
the chart `hypOfUHS`.  The metric `uhsMetric q v w = (q 3)⁻²⟪v,w⟫` is pulled back from the Lorentz
form `⟨·,·⟩` of `ℝ^{1,4}`, and since `A` is a Lorentz transformation and the differential of the
chart identifies tangent spaces, `d(mobius A) q` is a linear isometry of `uhsMetric`.

The proof has four independent ingredients, all recorded below:

* (Lorentz invariance) `⟨Ax, Ay⟩ = ⟨x,y⟩`, §1;
* (upper sheet) `A` maps the upper sheet to itself, §2;
* (chart differential) on the tangent space of the hyperboloid, `d(hypOfUHS) ∘ d(uhsOfHyp) = id`,
  §3;
* the resulting identity `uhsMetric (uhsOfHyp P) (d(uhsOfHyp) X) (d(uhsOfHyp) Y) = ⟨X,Y⟩` for
  tangent `X, Y`, §4.

§5 differentiates `mobius` and §6 assembles the theorem.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-! ### 1. Lorentz invariance of the Möbius action -/

/-- A matrix with `Aᵀ J A = J` preserves the Lorentz form: `⟨Ax, Ay⟩ = ⟨x,y⟩`. -/
private theorem lorentz_mulVec {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : Aᵀ * J * A = J) (x y : V5) :
    lorentz (A *ᵥ x) (A *ᵥ y) = lorentz x y := by
  rw [lorentz_eq_dotProduct, lorentz_eq_dotProduct]
  rw [dotProduct_mulVec_transpose]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]

/-! ### 2. The upper sheet is preserved -/

/-- A Lorentz matrix of the identity component of the Lorentz group (`A 4 4 > 0`) maps the upper
sheet of the hyperboloid to itself: the Lorentz square is preserved, and the time orientation is
preserved because `⟨Ax, A e₄⟩ = ⟨x, e₄⟩ = -x 4 < 0` while `(A e₄) 4 = A 4 4 > 0`. -/
private theorem upperSheet_mulVec {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    {x : V5} (hx : x ∈ upperSheet) : A *ᵥ x ∈ upperSheet := by
  refine ⟨?_, ?_⟩
  · rw [lorentz_mulVec hA.1 x x, hx.1]
  · have ht1 : lorentz (A *ᵥ timeVec) (A *ᵥ timeVec) = -1 := by
      rw [lorentz_mulVec hA.1 timeVec timeVec, lorentz_timeVec_self]
    have ht4 : 0 < (A *ᵥ timeVec) 4 := by rw [mulVec_timeVec_four]; exact hA.2
    have h1 : lorentz (A *ᵥ x) (A *ᵥ x) = -1 := by rw [lorentz_mulVec hA.1 x x, hx.1]
    have h2 : lorentz (A *ᵥ x) (A *ᵥ timeVec) < 0 := by
      rw [lorentz_mulVec hA.1 x timeVec, lorentz_left_timeVec]
      linarith [hx.2]
    exact four_pos_of_lorentz_pair_neg h1 ht1 ht4 h2

/-! ### 3. The differentials of the two charts are inverse on the tangent space

`dUhsOfHyp P v` is a coordinate expression: it is `v` divided by the height `δ = P₄ - P₃`
together with a correction term involving `v 4 - v 3`.  Composing with `dHypOfUHS (uhsOfHyp P)`
returns `v` as soon as `lorentz P v = 0`, i.e. for tangent vectors at `P`.  The first three
coordinates are immediate; the last two use the two relations
`P₀²+P₁²+P₂²+1 = (P₄-P₃)(P₄+P₃)` (from `P ∈ upperSheet`) and
`P₀v₀+P₁v₁+P₂v₂ = P₄v₄ - P₃v₃` (from `lorentz P v = 0`). -/

@[simp] private theorem dUhsOfHyp_apply_zero (P v : V5) :
    dUhsOfHyp P v 0 = v 0 / (P 4 - P 3) - P 0 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

@[simp] private theorem dUhsOfHyp_apply_one (P v : V5) :
    dUhsOfHyp P v 1 = v 1 / (P 4 - P 3) - P 1 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

@[simp] private theorem dUhsOfHyp_apply_two (P v : V5) :
    dUhsOfHyp P v 2 = v 2 / (P 4 - P 3) - P 2 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

@[simp] private theorem dUhsOfHyp_apply_three (P v : V5) :
    dUhsOfHyp P v 3 = v 3 / (P 4 - P 3) ^ 2 - v 4 / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]
  ring

private theorem dHypOfUHS_comp_dUhsOfHyp {P : V5} (hP : P ∈ upperSheet) {v : V5}
    (hv : lorentz P v = 0) : dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) = v := by
  have hδ : P 4 - P 3 ≠ 0 := ne_of_gt (upperSheet_four_sub_three_pos hP)
  have hsq : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 - P 4 ^ 2 = -1 := by
    have h := hP.1
    simp only [lorentz] at h
    nlinarith
  have hN : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + 1 = (P 4 - P 3) * (P 4 + P 3) := by nlinarith [hsq]
  have hv'' : P 0 * v 0 + P 1 * v 1 + P 2 * v 2 = P 4 * v 4 - P 3 * v 3 := by
    have h := hv
    simp only [lorentz] at h
    nlinarith
  ext i
  fin_cases i
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 0 = v 0
    simp only [dHypOfUHS_apply_zero, uhsOfHyp_apply_zero, uhsOfHyp_apply_three,
      dUhsOfHyp_apply_zero, dUhsOfHyp_apply_three]
    field_simp
    ring
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 1 = v 1
    simp only [dHypOfUHS_apply_one, uhsOfHyp_apply_one, uhsOfHyp_apply_three,
      dUhsOfHyp_apply_one, dUhsOfHyp_apply_three]
    field_simp
    ring
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 2 = v 2
    simp only [dHypOfUHS_apply_two, uhsOfHyp_apply_two, uhsOfHyp_apply_three,
      dUhsOfHyp_apply_two, dUhsOfHyp_apply_three]
    field_simp
    ring
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 3 = v 3
    simp only [dHypOfUHS_apply_three, uhsOfHyp_apply_three, dUhsOfHyp_apply_zero,
      dUhsOfHyp_apply_one, dUhsOfHyp_apply_two, dUhsOfHyp_apply_three,
      uhsOfHyp_apply_zero, uhsOfHyp_apply_one, uhsOfHyp_apply_two,
      inner_E4_eq_coords, norm_sq_E4_eq_coords]
    field_simp
    ring_nf
    linear_combination (2 * (P 4 - P 3)) * hv'' + (v 3 - v 4) * hN
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 4 = v 4
    simp only [dHypOfUHS_apply_four, uhsOfHyp_apply_three, dUhsOfHyp_apply_zero,
      dUhsOfHyp_apply_one, dUhsOfHyp_apply_two, dUhsOfHyp_apply_three,
      uhsOfHyp_apply_zero, uhsOfHyp_apply_one, uhsOfHyp_apply_two,
      inner_E4_eq_coords, norm_sq_E4_eq_coords]
    field_simp
    ring_nf
    linear_combination (2 * (P 4 - P 3)) * hv'' + (v 3 - v 4) * hN

/-! ### 4. The metric of the upper half space in terms of the Lorentz form -/

/-- The upper half space metric of a chart point, applied to the images under `d(uhsOfHyp P)` of
two tangent vectors at `P`, is their Lorentz pairing: `d(uhsOfHyp P)` is the inverse of
`d(hypOfUHS)`, which is a Lorentz isometry. -/
private theorem uhsMetric_dUhsOfHyp {P : V5} (hP : P ∈ upperSheet) {X Y : V5}
    (hX : lorentz P X = 0) (hY : lorentz P Y = 0) :
    uhsMetric (uhsOfHyp P) (dUhsOfHyp P X) (dUhsOfHyp P Y) = lorentz X Y := by
  have hq3 : (uhsOfHyp P) 3 ≠ 0 := ne_of_gt (uhsOfHyp_three_pos hP)
  rw [← lorentz_dHypOfUHS hq3 (dUhsOfHyp P X) (dUhsOfHyp P Y),
    dHypOfUHS_comp_dUhsOfHyp hP hX, dHypOfUHS_comp_dUhsOfHyp hP hY]

/-! ### 5. Differentiating the Möbius action -/

/-- The linear map `x ↦ A *ᵥ x` as a continuous linear map. -/
private def mulVecCLM (A : Matrix (Fin 5) (Fin 5) ℝ) : V5 →L[ℝ] V5 :=
  (Matrix.mulVecLin A).toContinuousLinearMap

private theorem mulVecCLM_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (x : V5) :
    mulVecCLM A x = A *ᵥ x := by
  simp [mulVecCLM]

/-- The chain rule for the Möbius action: `mobius A = uhsOfHyp ∘ (A ·) ∘ hypOfUHS`, and each of
the three factors is differentiable at the relevant point (`A *ᵥ hypOfUHS q` lies on the upper
sheet, so its height `x₄ - x₃` does not vanish). -/
private theorem hasFDerivAt_mobius {A : Matrix (Fin 5) (Fin 5) ℝ} {q : E4} (hq : q 3 ≠ 0)
    (hP : A *ᵥ hypOfUHS q ∈ upperSheet) :
    HasFDerivAt (fun x : E4 => uhsOfHyp (A *ᵥ hypOfUHS x))
      (dUhsOfHyp (A *ᵥ hypOfUHS q) ∘L mulVecCLM A ∘L dHypOfUHS q) q := by
  have hδ : (A *ᵥ hypOfUHS q) 4 - (A *ᵥ hypOfUHS q) 3 ≠ 0 :=
    ne_of_gt (upperSheet_four_sub_three_pos hP)
  have h1 : HasFDerivAt hypOfUHS (dHypOfUHS q) q := hasFDerivAt_hypOfUHS hq
  have h2 : HasFDerivAt (fun P : V5 => A *ᵥ P) (mulVecCLM A) (hypOfUHS q) := by
    have h := ContinuousLinearMap.hasFDerivAt (mulVecCLM A) (x := hypOfUHS q)
    rw [show (⇑(mulVecCLM A)) = (fun P : V5 => A *ᵥ P) from funext (mulVecCLM_apply A)] at h
    exact h
  have h3 : HasFDerivAt uhsOfHyp (dUhsOfHyp (A *ᵥ hypOfUHS q)) (A *ᵥ hypOfUHS q) :=
    hasFDerivAt_uhsOfHyp hδ
  exact (h3.comp (hypOfUHS q) h2).comp q h1

/-! ### 6. The Möbius action is an isometry of the upper half space metric -/

theorem mobius_isometry {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) {q : E4}
    (hq : 0 < q 3) (v w : E4) :
    uhsMetric (mobius A q) (fderiv ℝ (mobius A) q v) (fderiv ℝ (mobius A) q w) =
      uhsMetric q v w := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  have hP' : hypOfUHS q ∈ upperSheet :=
    ⟨lorentz_hypOfUHS_self hq3, hypOfUHS_four_pos hq⟩
  have hP : A *ᵥ hypOfUHS q ∈ upperSheet := upperSheet_mulVec hA hP'
  have hX : lorentz (A *ᵥ hypOfUHS q) (A *ᵥ dHypOfUHS q v) = 0 := by
    rw [lorentz_mulVec hA.1, tangent_hypOfUHS hq3 v]
  have hY : lorentz (A *ᵥ hypOfUHS q) (A *ᵥ dHypOfUHS q w) = 0 := by
    rw [lorentz_mulVec hA.1, tangent_hypOfUHS hq3 w]
  have hmain := uhsMetric_dUhsOfHyp hP hX hY
  have hfd : fderiv ℝ (mobius A) q
      = dUhsOfHyp (A *ᵥ hypOfUHS q) ∘L mulVecCLM A ∘L dHypOfUHS q := by
    rw [show mobius A = (fun x : E4 => uhsOfHyp (A *ᵥ hypOfUHS x)) from rfl]
    exact (hasFDerivAt_mobius hq3 hP).fderiv
  rw [hfd]
  simp only [mobius, ContinuousLinearMap.comp_apply, mulVecCLM_apply]
  rw [hmain, lorentz_mulVec hA.1 (dHypOfUHS q v) (dHypOfUHS q w),
    lorentz_dHypOfUHS hq3 v w]

end Work.HypModel
