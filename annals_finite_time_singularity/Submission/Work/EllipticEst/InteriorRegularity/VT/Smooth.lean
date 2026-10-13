/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): smoothness of the source on the strip.

If `F` is `C^∞` on the open quadrant `Q0` (`Work.FTS.EllipticEst.SmoothOpen F`), then the
transported source `Gc α F` is `C^∞` on the strip `stripE`, and consequently `χ · Gc α F` is
`C^∞` on the whole plane whenever the smooth cut-off `χ` has `tsupport χ ⊆ stripE`.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic
import Submission.Work.EllipticEst.InteriorRegularity.contDiff_mul_of_tsupport_subset

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem uncurry_contDiffOn_stripE {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (n : ℕ) :
    ContDiffOn ℝ n (fun x : E2 => Function.uncurry F (Real.exp (α * x 0), x 1)) stripE := by
  refine (hF.forall n).comp ?_ ?_
  · fun_prop
  · intro x hx
    exact ⟨Real.exp_pos _, hx.1, hx.2⟩

theorem Gs_contDiffOn {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hα : α ≠ 0) (n : ℕ) :
    ContDiffOn ℝ n (Gs α F) stripE := by
  have hcomp : ContDiffOn ℝ n
      (fun x : E2 => Function.uncurry F (Real.exp (α * x 0), x 1)) stripE :=
    uncurry_contDiffOn_stripE hF n
  have hmul : ContDiffOn ℝ n
      (fun x : E2 => wt α x * Function.uncurry F (Real.exp (α * x 0), x 1)) stripE :=
    ((wt_contDiff hα n).contDiffOn).mul hcomp
  have hc : ContDiffOn ℝ n
      (fun x : E2 =>
        ((wt α x * Function.uncurry F (Real.exp (α * x 0), x 1) : ℝ) : ℂ)) stripE :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hmul
  refine hc.congr ?_
  intro x _
  simp [Gs, Function.uncurry]

theorem Gc_contDiffOn {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hα : α ≠ 0) (n : ℕ) :
    ContDiffOn ℝ n (Gc α F) stripE := by
  refine (Gs_contDiffOn (α := α) (F := F) hF hα n).congr ?_
  intro x hx
  exact Gc_of_mem hx

/-- A smooth cut-off supported in the strip times the transported source is `C^∞` on the plane. -/
theorem contDiff_mul_Gc {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hα : α ≠ 0) {χ : E2 → ℂ}
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχsub : tsupport χ ⊆ stripE) (n : ℕ) :
    ContDiff ℝ n (fun x => χ x * Gc α F x) :=
  contDiff_mul_of_tsupport_subset (Gc_contDiffOn hF hα n) isOpen_stripE hχs hχsub

/-- A compactly supported `C^∞` function is integrable. -/
theorem integrable_of_smooth_compact {f : E2 → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : Integrable f := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have h : Integrable (⇑(hc.toSchwartzMap hfs)) volume := (hc.toSchwartzMap hfs).integrable
  rwa [hcoe] at h

end Work.EllipticEst.InteriorRegularity.VT
