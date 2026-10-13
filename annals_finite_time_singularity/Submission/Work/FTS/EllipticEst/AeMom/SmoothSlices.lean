/-
# `AeMom.SmoothSlices` — smoothness of a datum of the a.e.-moment class on the open quadrant

A verbatim port of `Work.FTS.EllipticEst.remov.smoothOpen_slices_weak`
(`remov/smoothOpen_slices_weak.lean`, proved, axiom-clean) from the pointwise-moment class
`TT.EllWeakPos` to the a.e.-moment class `AeMom.EllWeakPosAe` (`AeMom/Defs.lean`).  The port is
immediate: the proof uses only the *smoothness* and *equation* fields of the class (identical in
both classes) and the class-free items `smoothOpen_bslOp_of_smoothOpen`,
`Cert.smoothOpen_congr_bsl`, `SmoothOpen.DzIter`, …; the two moment conditions are untouched.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.AeMom.Defs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeMom

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **`bslOp α Ψ` is `C^∞` on the open quadrant as soon as `Ψ` is** (class-free). -/
theorem smoothOpen_bslOp_of_smoothOpen (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hzsq
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hz
          (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
            (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

/-- All the fields attached to a datum of the **a.e.-moment** class (`F`, `Ψ`, `z²∂_zzΨ`,
`∂_θθΨ`) and all their `D_z`-iterates are smooth on the open quadrant. -/
theorem smoothOpen_slices_weak {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j F)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ)
      ∧ Work.FTS.EllipticEst.SmoothOpen
          (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ∧ Work.FTS.EllipticEst.SmoothOpen
          (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (smoothOpen_bslOp_of_smoothOpen α hΨso)
      (fun z θ hz hθ0 hθ1 => h.eq z hz θ hθ0 hθ1)
  refine ⟨hFso.DzIter j, hΨso.DzIter j, ?_, ?_⟩
  · exact (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)).DzIter j
  · exact (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter j

end Work.FTS.EllipticEst.AeMom
