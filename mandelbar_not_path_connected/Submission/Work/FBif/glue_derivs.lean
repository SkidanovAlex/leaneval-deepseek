import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.antipoly_wirtinger
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.AhlforsBers.Affine
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Wirtinger derivatives of the glued map

This file proves `Work.FBif.glue_derivs`: the glued map
`glueMap c q ε χ z = T_c z + ε · χ z · q z` is `C¹` and its Wirtinger derivatives are

* `∂ (glueMap) = ε · q · ∂χ` (the `∂` of `T_c` vanishes since `T_c` is antiholomorphic, and the
  `∂` of the antipolynomial `q` vanishes as well);
* `∂̄ (glueMap) = 2 z̄ + ε · χ · ∂̄q + ε · q · ∂̄χ` (with `∂̄ T_c = 2 z̄`).

The ingredients are the general `∂`, `∂̄` rules (`Work.MRMT.QC.dz_mul`, `dzbar_mul`,
`dz_add_of_diff`, `dzbar_add_of_diff`, `Work.MRMT.AhlforsBers.dz_const_mul_add`), the
antiholomorphy of `q` (`Work.FBif.antipoly_wirtinger`) and the explicit computation of the
Wirtinger derivatives of the model `T_c`.
-/

open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The model map `T_c` -/

theorem contDiff_tantibar (c : ℂ) (n : WithTop ℕ∞) : ContDiff ℝ n (Tantibar c) := by
  have h : Tantibar c = fun z : ℂ => (star z) ^ 2 + c := rfl
  rw [h]
  have hstar : ContDiff ℝ n (star : ℂ → ℂ) := by
    have h' : (star : ℂ → ℂ) = ⇑(Complex.conjCLE) := by
      ext x; rw [Complex.star_def]; rfl
    rw [h']; exact Complex.conjCLE.contDiff
  exact (hstar.pow 2).add contDiff_const

/-- The star function is real differentiable (stated for the explicit `starRingEnd` form). -/
theorem differentiableAt_starRingEnd (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => starRingEnd ℂ w) z := by
  simpa only [Complex.star_def] using Work.MRMT.Wirtinger.differentiableAt_star z

/-- `T_c` is antiholomorphic, so its `∂`-derivative vanishes. -/
theorem dz_tantibar (c : ℂ) (z : ℂ) : Work.MRMT.dz (Tantibar c) z = 0 := by
  have hstar : DifferentiableAt ℝ (fun w : ℂ => starRingEnd ℂ w) z :=
    differentiableAt_starRingEnd z
  have h : Tantibar c = fun w : ℂ => starRingEnd ℂ w * starRingEnd ℂ w + c := by
    funext w; rw [show Tantibar c w = (starRingEnd ℂ w) ^ 2 + c from rfl, pow_two]
  rw [h, Work.MRMT.QC.dz_add_of_diff
      (F := fun w : ℂ => starRingEnd ℂ w * starRingEnd ℂ w) (G := fun _ : ℂ => c)
      (hstar.mul hstar) (differentiableAt_const c),
    Work.MRMT.QC.dz_mul (F := fun w : ℂ => starRingEnd ℂ w) (G := fun w : ℂ => starRingEnd ℂ w)
      hstar hstar]
  have hz : Work.MRMT.dz (fun w : ℂ => starRingEnd ℂ w) z = 0 := by
    simpa only [Complex.star_def] using Work.MRMT.Wirtinger.dz_star z
  rw [hz, show Work.MRMT.dz (fun _ : ℂ => c) z = 0 from by simp [Work.MRMT.dz]]
  ring

/-- The `∂̄`-derivative of the antiholomorphic model: `∂̄ T_c = 2 z̄`. -/
theorem dzbar_tantibar (c : ℂ) (z : ℂ) : Work.MRMT.dzbar (Tantibar c) z = 2 * star z := by
  have hstar : DifferentiableAt ℝ (fun w : ℂ => starRingEnd ℂ w) z :=
    differentiableAt_starRingEnd z
  have h : Tantibar c = fun w : ℂ => starRingEnd ℂ w * starRingEnd ℂ w + c := by
    funext w; rw [show Tantibar c w = (starRingEnd ℂ w) ^ 2 + c from rfl, pow_two]
  rw [h, Work.MRMT.QC.dzbar_add_of_diff
      (F := fun w : ℂ => starRingEnd ℂ w * starRingEnd ℂ w) (G := fun _ : ℂ => c)
      (hstar.mul hstar) (differentiableAt_const c),
    Work.MRMT.QC.dzbar_mul (F := fun w : ℂ => starRingEnd ℂ w)
      (G := fun w : ℂ => starRingEnd ℂ w) hstar hstar]
  have hz : Work.MRMT.dzbar (fun w : ℂ => starRingEnd ℂ w) z = 1 := by
    simpa only [Complex.star_def] using Work.MRMT.Wirtinger.dzbar_star z
  rw [hz, show Work.MRMT.dzbar (fun _ : ℂ => c) z = 0 from by simp [Work.MRMT.dzbar]]
  simp only [Complex.star_def]
  ring

/-! ## Multiplication of a scalar -/

theorem dz_const_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    Work.MRMT.dz (fun w : ℂ => a * f w) z = a * Work.MRMT.dz f z := by
  have h : (fun w : ℂ => a * f w) = (fun w : ℂ => a * f w + 0) := by
    funext w; rw [add_zero]
  rw [h, Work.MRMT.AhlforsBers.dz_const_mul_add]

theorem dzbar_const_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    Work.MRMT.dzbar (fun w : ℂ => a * f w) z = a * Work.MRMT.dzbar f z := by
  have h : (fun w : ℂ => a * f w) = (fun w : ℂ => a * f w + 0) := by
    funext w; rw [add_zero]
  rw [h, Work.MRMT.AhlforsBers.dzbar_const_mul_add]

/-! ## The statement -/

theorem glue_derivs (c : ℂ) {q : ℂ → ℂ} {P : Polynomial ℂ}
    (hP : ∀ z : ℂ, q z = P.eval (star z)) (ε : ℝ) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    ContDiff ℝ 1 (Work.FBif.glueMap c q ε χ) ∧
      (∀ z : ℂ, Work.MRMT.dz (Work.FBif.glueMap c q ε χ) z =
        (ε : ℂ) * q z * Work.MRMT.dz (Work.FBif.realCoe χ) z) ∧
      (∀ z : ℂ, Work.MRMT.dzbar (Work.FBif.glueMap c q ε χ) z =
        2 * star z + (ε : ℂ) * ((χ z : ℝ) : ℂ) * Work.MRMT.dzbar q z +
          (ε : ℂ) * q z * Work.MRMT.dzbar (Work.FBif.realCoe χ) z) := by
  obtain ⟨hq_diff, hq_dz, hq_dzbar⟩ := antipoly_wirtinger hP
  have hχ_diff : ContDiff ℝ 1 (realCoe χ) := by
    change ContDiff ℝ 1 (fun z : ℂ => ((χ z : ℝ) : ℂ))
    exact Complex.ofRealCLM.contDiff.comp hχ
  have hT_diff : ContDiff ℝ 1 (Tantibar c) := contDiff_tantibar c 1
  have hglue : glueMap c q ε χ
      = fun w : ℂ => Tantibar c w + (ε : ℂ) * realCoe χ w * q w := by
    funext w; rw [glueMap_apply]; rfl
  have key : ContDiff ℝ 1
      (fun w : ℂ => Tantibar c w + (ε : ℂ) * realCoe χ w * q w) :=
    hT_diff.add (((contDiff_const (c := (ε : ℂ))).mul hχ_diff).mul hq_diff)
  refine ⟨by rw [hglue]; exact key, ?_, ?_⟩
  · intro z
    have hT : DifferentiableAt ℝ (Tantibar c) z :=
      (hT_diff.differentiable (by norm_num)).differentiableAt
    have hχ_d : DifferentiableAt ℝ (realCoe χ) z :=
      (hχ_diff.differentiable (by norm_num)).differentiableAt
    have hq_d : DifferentiableAt ℝ q z :=
      (hq_diff.differentiable (by norm_num)).differentiableAt
    have hE : DifferentiableAt ℝ (fun w : ℂ => (ε : ℂ) * realCoe χ w) z :=
      hχ_d.const_mul (ε : ℂ)
    have h2 : DifferentiableAt ℝ (fun w : ℂ => (ε : ℂ) * realCoe χ w * q w) z := hE.mul hq_d
    rw [hglue,
      Work.MRMT.QC.dz_add_of_diff (F := Tantibar c)
        (G := fun w : ℂ => (ε : ℂ) * realCoe χ w * q w) hT h2,
      Work.MRMT.QC.dz_mul (F := fun w : ℂ => (ε : ℂ) * realCoe χ w) (G := q) hE hq_d,
      dz_const_mul (ε : ℂ) (realCoe χ) z, dz_tantibar c z, hq_dz]
    ring
  · intro z
    have hT : DifferentiableAt ℝ (Tantibar c) z :=
      (hT_diff.differentiable (by norm_num)).differentiableAt
    have hχ_d : DifferentiableAt ℝ (realCoe χ) z :=
      (hχ_diff.differentiable (by norm_num)).differentiableAt
    have hq_d : DifferentiableAt ℝ q z :=
      (hq_diff.differentiable (by norm_num)).differentiableAt
    have hE : DifferentiableAt ℝ (fun w : ℂ => (ε : ℂ) * realCoe χ w) z :=
      hχ_d.const_mul (ε : ℂ)
    have h2 : DifferentiableAt ℝ (fun w : ℂ => (ε : ℂ) * realCoe χ w * q w) z := hE.mul hq_d
    have hcoe : realCoe χ z = ((χ z : ℝ) : ℂ) := rfl
    rw [hglue,
      Work.MRMT.QC.dzbar_add_of_diff (F := Tantibar c)
        (G := fun w : ℂ => (ε : ℂ) * realCoe χ w * q w) hT h2,
      Work.MRMT.QC.dzbar_mul (F := fun w : ℂ => (ε : ℂ) * realCoe χ w) (G := q) hE hq_d,
      dzbar_const_mul (ε : ℂ) (realCoe χ) z, dzbar_tantibar c z, hq_dzbar, hcoe]
    ring

end Work.FBif

end
