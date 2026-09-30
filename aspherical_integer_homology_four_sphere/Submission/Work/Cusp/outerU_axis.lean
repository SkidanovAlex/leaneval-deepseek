/-
# The meridian coordinate `outerU v` is a coordinate projection

`outerU v x` is the `κ_{v,1}`-coordinate of `x`, i.e. `⟪x, κ_{v,1}⟫ / ‖κ_{v,1}‖²`.  The data
(`Data.kappa`) exhibits `κ_{v,1}` as a nonzero multiple of a **standard basis vector** of `ℝ³` — the
meridian direction of each cusp is an axis of the cube coordinates — and the multiplier has absolute
value `≥ 1` (it is `±1` or `±2`, see the five formulas `outerU_zero`, …, `outerU_four`).  Hence
`outerU v` is a coordinate projection up to a factor of modulus `≥ 1`, which yields the estimate

  `abs_outerU_sub_lt_of : (∀ i, |x i − c i| < δ) → |outerU v x − outerU v c| < δ`

used to see that the meridian coordinate of a point of the (unslabbed) collar box
`cuspBoxTop v c δ` with `δ ≤ 1/2` lies in the interval
`(outerU v c − 1/2, outerU v c + 1/2) = layerA (cuspAnchor v c)` (`outerU_mem_layerA`), which is the
domain of the layer chart `layerPtI`.
-/
import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-- The squared Euclidean norm of a vector of `ℝ³` in coordinates. -/
private lemma norm_sq_piLp3_aux (a b c : ℝ) : ‖(!₂[a,b,c] : E3)‖ ^ 2 = a^2 + b^2 + c^2 := by
  rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-! ### The five meridian directions -/

/-- The meridian direction of the first cusp is `−e₁`: `outerU 0 x = −x 1`. -/
theorem outerU_zero (x : E3) : outerU 0 x = -x 1 := by
  simp [outerU, kappaCoord, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three, norm_sq_piLp3_aux]

/-- The meridian direction of the second cusp is `−e₀`: `outerU 1 x = −x 0`. -/
theorem outerU_one (x : E3) : outerU 1 x = -x 0 := by
  simp [outerU, kappaCoord, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three, norm_sq_piLp3_aux]

/-- The meridian direction of the third cusp is `−e₂`: `outerU 2 x = −x 2`. -/
theorem outerU_two (x : E3) : outerU 2 x = -x 2 := by
  simp [outerU, kappaCoord, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three, norm_sq_piLp3_aux]

/-- The meridian direction of the fourth cusp is `−e₁`: `outerU 3 x = −x 1`. -/
theorem outerU_three (x : E3) : outerU 3 x = -x 1 := by
  simp [outerU, kappaCoord, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three, norm_sq_piLp3_aux]

/-- The meridian direction of the fifth cusp is `−2e₂`: `outerU 4 x = −x 2 / 2`. -/
theorem outerU_four (x : E3) : outerU 4 x = -x 2 / 2 := by
  simp [outerU, kappaCoord, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three, norm_sq_piLp3_aux]
  ring_nf

/-! ### The Lipschitz estimate -/

/-- **The meridian coordinate is `1`-Lipschitz for the sup norm of the coordinates.**  If
`|x i − c i| < δ` for all coordinates `i`, then `|outerU v x − outerU v c| < δ`.  Indeed
`outerU v` is one coordinate of the cube coordinates divided by a factor of modulus `≥ 1`. -/
theorem abs_outerU_sub_lt_of (v : Fin 5) {x c : E3} {δ : ℝ} (h : ∀ i, |x i - c i| < δ) :
    |outerU v x - outerU v c| < δ := by
  fin_cases v <;>
  · have h0 := abs_lt.mp (h 0)
    have h1 := abs_lt.mp (h 1)
    have h2 := abs_lt.mp (h 2)
    simp [outerU, kappaCoord, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three, norm_sq_piLp3_aux]
    rw [abs_lt]
    constructor <;> linarith

/-- **The meridian coordinate of a point of the collar box lies in the layer interval.**  For
`δ ≤ 1/2` and `q ∈ cuspBoxTop v c δ` we have `outerU v (xOf q) ∈ layerA (cuspAnchor v c)`, i.e.
`outerU v c − 1/2 < outerU v (xOf q) < outerU v c + 1/2`: the box moves at most `δ` in the meridian
direction.  This is what makes the layer chart `layerPtI (cuspAnchor v c)` applicable to the collar
source. -/
theorem outerU_mem_layerA (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) {q : E4}
    (hq : q ∈ cuspBoxTop v c δ) : outerU v (xOf q) ∈ layerA (cuspAnchor v c) := by
  have h := abs_outerU_sub_lt_of v (x := xOf q) (c := c) (δ := δ) (fun i => hq.1 i)
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  simp only [layerA, cuspAnchor, Set.mem_Ioo]
  constructor <;> linarith

end Work.Cusp
