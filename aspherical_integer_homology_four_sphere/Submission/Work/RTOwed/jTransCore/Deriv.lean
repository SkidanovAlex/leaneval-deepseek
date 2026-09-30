/-
# Smoothness, derivative and invertibility of the polar map `jPolMap`

The polar map `jPolMap q = (q₀ cos q₁, q₀ sin q₁, q₂, q₃)` (`Work.RTOwed.jTransCore.Basic`) is
smooth, and away from the axis `q 0 = 0` its derivative is invertible: this is what makes the
junction→core transition an isometry of the warped/flat pair and its inverse a smooth map (by the
inverse function theorem).
-/
import Mathlib
import Submission.Work.RTOwed.jTransCore.Basic
import Submission.Work.RTInstance.Models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real RealInnerProductSpace

namespace Work.RTOwed

open Work.RTInstance

/-- **The polar map is smooth.** -/
theorem contDiff_jPolMap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) jPolMap := by
  rw [show jPolMap = fun q : Work.Cusp.E4 =>
      !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3] from rfl]
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- **The polar map is continuous.** -/
theorem continuous_jPolMap : Continuous jPolMap :=
  contDiff_jPolMap.continuous

/-- The polar map has the derivative `fderiv ℝ jPolMap q` at every point. -/
theorem hasFDerivAt_jPolMap (q : Work.Cusp.E4) :
    HasFDerivAt jPolMap (fderiv ℝ jPolMap q) q :=
  ((contDiff_jPolMap.contDiffAt).differentiableAt (by simp)).hasFDerivAt

/-- **The derivative of the polar map is injective off the axis `q 0 = 0`.**  Indeed, pulling the
flat model back along the polar map gives the positive definite form
`diagQuad ![1, q₀², h₀², h₀²]` (`Work.RTOwed.flatModel_polar_change`), so the derivative can only
kill vectors on which that form vanishes. -/
theorem fderiv_jPolMap_injective (q : Work.Cusp.E4) (hq : q 0 ≠ 0) :
    Function.Injective (fderiv ℝ jPolMap q) := by
  intro a b hab
  by_contra hne
  have hab' : (fderiv ℝ (fun q : Work.Cusp.E4 =>
      !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]) q) a
      = (fderiv ℝ (fun q : Work.Cusp.E4 =>
      !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]) q) b := hab
  have h := flatModel_polar_change (1:ℝ) q (a - b) (a - b)
  have hd : fderiv ℝ (fun q : Work.Cusp.E4 =>
      !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]) q (a - b) = 0 := by
    simp only [map_sub, hab', sub_self]
  rw [hd] at h
  simp only [one_pow] at h
  have h' : ((flatModel (1:ℝ) (jPolMap q)) 0) 0
      = ((diagQuad ![1, q 0 ^ 2, 1, 1]) (a - b)) (a - b) := h
  have h0 : ((diagQuad ![1, q 0 ^ 2, 1, 1]) (a - b)) (a - b) = 0 := by
    rw [← h', flatModel_apply]
    simp
  have hpos : 0 < ((diagQuad ![1, q 0 ^ 2, 1, 1]) (a - b)) (a - b) := by
    refine diagQuad_pos (c := ![1, q 0 ^ 2, 1, 1]) ?_ (a - b) (sub_ne_zero.mpr hne)
    intro i
    fin_cases i <;> simp [sq, mul_self_pos, hq]
  linarith [h0, hpos]

/-- **The derivative of the polar map, as a continuous linear equivalence**, off the axis. -/
noncomputable def jPolDerivEquiv (q : Work.Cusp.E4) (hq : q 0 ≠ 0) :
    Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4 :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ jPolMap q)
    (LinearMap.ker_eq_bot.mpr (fderiv_jPolMap_injective q hq))
    (LinearMap.range_eq_top.mpr
      (LinearMap.injective_iff_surjective.mp (fderiv_jPolMap_injective q hq)))

theorem jPolDerivEquiv_coe (q : Work.Cusp.E4) (hq : q 0 ≠ 0) :
    ((jPolDerivEquiv q hq : Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4) :
      Work.Cusp.E4 →L[ℝ] Work.Cusp.E4) = fderiv ℝ jPolMap q :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

/-- The polar map has derivative `jPolDerivEquiv q hq` at `q`. -/
theorem hasFDerivAt_jPolMap_equiv (q : Work.Cusp.E4) (hq : q 0 ≠ 0) :
    HasFDerivAt jPolMap ((jPolDerivEquiv q hq : Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4) :
      Work.Cusp.E4 →L[ℝ] Work.Cusp.E4) q := by
  rw [jPolDerivEquiv_coe]
  exact hasFDerivAt_jPolMap q

end Work.RTOwed
