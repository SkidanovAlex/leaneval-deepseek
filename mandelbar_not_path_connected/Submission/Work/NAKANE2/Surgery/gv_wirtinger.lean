import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.Surgery.gv_basic
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.FBif.norm_deriv_glueMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Differentiability of the bump -/

theorem chiC_differentiableAt {c₀ : ℂ} (χ : ContDiffBump c₀) (w : ℂ) :
    DifferentiableAt ℝ (Work.NAKANE2.chiC c₀ χ) w :=
  ((gv_chiC_contDiff χ).differentiable (by norm_num)).differentiableAt

/-! ## The Wirtinger derivatives of the deformation `σ_v w = w + χ w · v` -/

theorem dz_chiC_mul_const {c₀ : ℂ} (χ : ContDiffBump c₀) (v : ℂ) (w : ℂ) :
    Work.MRMT.dz (fun u : ℂ => Work.NAKANE2.chiC c₀ χ u * v) w
      = v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ χ) w := by
  have hfun : (fun u : ℂ => Work.NAKANE2.chiC c₀ χ u * v)
      = fun u : ℂ => v * Work.NAKANE2.chiC c₀ χ u := by funext u; ring
  rw [hfun, Work.FBif.dz_const_mul_of_diff (chiC_differentiableAt χ w)]

theorem dzbar_chiC_mul_const {c₀ : ℂ} (χ : ContDiffBump c₀) (v : ℂ) (w : ℂ) :
    Work.MRMT.dzbar (fun u : ℂ => Work.NAKANE2.chiC c₀ χ u * v) w
      = v * Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ χ) w := by
  have hfun : (fun u : ℂ => Work.NAKANE2.chiC c₀ χ u * v)
      = fun u : ℂ => v * Work.NAKANE2.chiC c₀ χ u := by funext u; ring
  rw [hfun, Work.FBif.dzbar_const_mul_of_diff (chiC_differentiableAt χ w)]

theorem sig_differentiableAt {c₀ : ℂ} (χ : ContDiffBump c₀) (v w : ℂ) :
    DifferentiableAt ℝ (Work.NAKANE2.sig c₀ χ v) w := by
  have hG : DifferentiableAt ℝ (fun u : ℂ => Work.NAKANE2.chiC c₀ χ u * v) w :=
    (chiC_differentiableAt χ w).mul (differentiableAt_const v)
  have hsig : Work.NAKANE2.sig c₀ χ v
      = fun u : ℂ => (id : ℂ → ℂ) u + (fun t : ℂ => Work.NAKANE2.chiC c₀ χ t * v) u := by
    funext u; rfl
  rw [hsig]
  exact differentiableAt_id.add hG

theorem dz_sig {c₀ : ℂ} (χ : ContDiffBump c₀) (v : ℂ) (w : ℂ) :
    Work.MRMT.dz (Work.NAKANE2.sig c₀ χ v) w
      = 1 + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ χ) w := by
  have hG : DifferentiableAt ℝ (fun u : ℂ => Work.NAKANE2.chiC c₀ χ u * v) w :=
    (chiC_differentiableAt χ w).mul (differentiableAt_const v)
  have hsig : Work.NAKANE2.sig c₀ χ v
      = fun u : ℂ => (id : ℂ → ℂ) u + (fun t : ℂ => Work.NAKANE2.chiC c₀ χ t * v) u := by
    funext u; rfl
  rw [hsig, Work.MRMT.QC.dz_add_of_diff differentiableAt_id hG,
    Work.MRMT.dz_id, dz_chiC_mul_const]

theorem dzbar_sig {c₀ : ℂ} (χ : ContDiffBump c₀) (v : ℂ) (w : ℂ) :
    Work.MRMT.dzbar (Work.NAKANE2.sig c₀ χ v) w
      = v * Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ χ) w := by
  have hG : DifferentiableAt ℝ (fun u : ℂ => Work.NAKANE2.chiC c₀ χ u * v) w :=
    (chiC_differentiableAt χ w).mul (differentiableAt_const v)
  have hsig : Work.NAKANE2.sig c₀ χ v
      = fun u : ℂ => (id : ℂ → ℂ) u + (fun t : ℂ => Work.NAKANE2.chiC c₀ χ t * v) u := by
    funext u; rfl
  rw [hsig, Work.MRMT.QC.dzbar_add_of_diff differentiableAt_id hG,
    Work.MRMT.dzbar_id, dzbar_chiC_mul_const]
  ring

theorem gv_wirtinger {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) (v z : ℂ) :
    Work.MRMT.dz (Work.NAKANE2.gv c₀ D.χ v) z
        = (v * Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ D.χ) (LeanEval.ComplexAnalysis.Tantibar c₀ z)) * (2 * z)
      ∧ Work.MRMT.dzbar (Work.NAKANE2.gv c₀ D.χ v) z
        = (1 + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) (LeanEval.ComplexAnalysis.Tantibar c₀ z)) * (2 * star z) := by
  obtain ⟨hTcd, hdzT, hdzbarT⟩ := Work.FBif.tantibar_wirtinger c₀
  have hTdiff : DifferentiableAt ℝ (fun z : ℂ => Tantibar c₀ z) z :=
    (hTcd.differentiable (by norm_num)).differentiableAt
  have hSdiff : DifferentiableAt ℝ (Work.NAKANE2.sig c₀ D.χ v) (Tantibar c₀ z) :=
    sig_differentiableAt D.χ v _
  have hgv : Work.NAKANE2.gv c₀ D.χ v
      = Work.NAKANE2.sig c₀ D.χ v ∘ (fun z : ℂ => Tantibar c₀ z) := rfl
  have hstar : star (2 * star z) = 2 * z := by
    simp [star_mul]
    ring
  constructor
  · rw [hgv, Work.MRMT.Wirtinger.dz_comp hSdiff hTdiff, hdzT z, hdzbarT z, dzbar_sig,
      hstar]
    ring
  · rw [hgv, Work.MRMT.Wirtinger.dzbar_comp hSdiff hTdiff, hdzT z, hdzbarT z, dz_sig]
    simp

end Work.NAKANE2.Surgery
