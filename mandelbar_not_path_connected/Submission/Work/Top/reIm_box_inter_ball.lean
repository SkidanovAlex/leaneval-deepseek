import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- The open vertical strip `|Re w - R| < a` is `ℝ`-convex: it is the preimage of the open
interval `(R - a, R + a)` under the `ℝ`-linear map `Complex.reLm`. -/
private lemma convex_re_sub_lt (R a : ℝ) : Convex ℝ {w : ℂ | |w.re - R| < a} := by
  have hset : {w : ℂ | |w.re - R| < a} = Complex.reLm ⁻¹' Set.Ioo (R - a) (R + a) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Complex.reLm_coe, Set.mem_Ioo, abs_lt]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hset]
  exact (convex_Ioo _ _).linear_preimage Complex.reLm

/-- The open horizontal strip `|Im w| < b` is `ℝ`-convex: it is the preimage of the open
interval `(-b, b)` under the `ℝ`-linear map `Complex.imLm`. -/
private lemma convex_im_lt (b : ℝ) : Convex ℝ {w : ℂ | |w.im| < b} := by
  have hset : {w : ℂ | |w.im| < b} = Complex.imLm ⁻¹' Set.Ioo (-b) b := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Complex.imLm_coe, Set.mem_Ioo, abs_lt]
  rw [hset]
  exact (convex_Ioo _ _).linear_preimage Complex.imLm

/-- The open disc of radius `R` centred at the origin is `ℝ`-convex. -/
private lemma convex_norm_lt (R : ℝ) : Convex ℝ {w : ℂ | ‖w‖ < R} := by
  have hset : {w : ℂ | ‖w‖ < R} = Metric.ball (0 : ℂ) R := by
    ext w; simp [Metric.mem_ball, dist_eq_norm]
  rw [hset]
  exact convex_ball 0 R

/-- The intersection of the open strip `|Re w - R| < a`, the open strip `|Im w| < b` and the
open disc `‖w‖ < R` is convex, hence preconnected. -/
theorem reIm_box_inter_ball {R a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    IsPreconnected {w : ℂ | |w.re - R| < a ∧ |w.im| < b ∧ ‖w‖ < R} := by
  exact ((convex_re_sub_lt R a).inter ((convex_im_lt b).inter (convex_norm_lt R))).isPreconnected

end Work.Top
