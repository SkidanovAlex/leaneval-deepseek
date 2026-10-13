/-
Copyright: work module for the Elgindi finite-time singularity project.

# `L₁₂(F)` is `C^k` on `(0,∞)` for `RegQ α k F`

`UopHk/GsingFactsInterior.lean` proves that `L₁₂(F)` is `C^{k-1}` on `(0,∞)` for a source in
the interior class (`SmoothQuad F` + `HkMem α k F`).  Its derivative there is the explicitly
smooth function `z ↦ -3 F_*(F)(z)/z`, which is itself `C^{k-1}` (because `F_*(F)` is `C^{k-1}`).
Hence `L₁₂(F)` is in fact `C^k`, and every `D_z`-iterate of it of order `≤ k` is honest.  This
is the smoothness input used by the certificates of the residual
`EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)` (whose `z`-smoothness is exactly that of
`L₁₂(F)`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false

/-- **`L₁₂(F)` is `C^k` on `(0,∞)`** for `F` smooth on the open quadrant with `HkMem α k F`,
`k ≥ 2`, `0 < α`.  (`GsingFactsInterior` supplies the `C^{k-1}` statement together with the
derivative `-3F_*(F)(z)/z`, which is `C^{k-1}`; one order is gained.) -/
theorem contDiffOn_L12_k (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (hk : 2 ≤ k) :
    ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi 0) := by
  obtain ⟨_, hderiv⟩ := contDiffOn_L12_of_smoothOpen_Hk α k F hF hmem hk
  have hFstar : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem (by omega)
  have hg : ContDiffOn ℝ (k - 1) (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) :=
    ((contDiffOn_const.mul hFstar).div contDiffOn_id fun z hz => ne_of_gt hz).neg
  have h := contDiffOn_succ_of_hasDerivAt
    (f := Work.Elliptic.L12 F) (g := fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
    (m := k - 1)
    (fun z hz => by
      have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
      have h1 := hderiv z hz'
      refine h1.congr_deriv ?_
      ring)
    hg
  have hcast : ((k - 1 : ℕ) : ℕ∞ω) + 1 = ((k : ℕ) : ℕ∞ω) := by
    calc ((k - 1 : ℕ) : ℕ∞ω) + 1 = ((k - 1 + 1 : ℕ) : ℕ∞ω) := by
          rw [Nat.cast_add, Nat.cast_one]
      _ = ((k : ℕ) : ℕ∞ω) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  simpa only [hcast] using h

/-- The `EllHypQ` form: for a datum of the interior class the source `F` is smooth on the open
quadrant with `HkMem α k F`, so `L₁₂(F)` is `C^k` on `(0,∞)`. -/
theorem EllHypQ.contDiffOn_L12 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.EllHypQ α k F Ψ) :
    ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi 0) :=
  contDiffOn_L12_k α k F hα hα1 (smoothOpen_of_smoothQuad h.regF.1) h.regF.2.1 hk

end Work.FTS.EllipticEst.UopHk
