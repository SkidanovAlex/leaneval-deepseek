import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.RXVPMain
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_RegExport.RXT.jc3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

theorem jc3 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) :
    ∀ j i : ℕ, j + i ≤ 3 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) T) :=
  jc3_of_pieces hOK T hT
    (fun {a b c d} ha hab hc hcd hd => slice_space_lip hα hα13 hOK T hT ha hab hc hcd hd)
    (lim_mixed_lip (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13)
      hOK.2 T hT)
    (fun {V W} {x₀ δc L K} hδc hL hK hV hcont hW hderiv =>
      tau_lip_sqrt_of_primitive_self hδc hL hK hV hcont hW hderiv)

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.st1_of_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

theorem st1_of_weighted {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    {S K : ℝ} (hS : 0 < S)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) := by
  have hK0 : 0 ≤ K := st1_K_nonneg (α := α) (g := g) (S := S) (K := K) hα hS hw
  exact ⟨⟨st1_dthvan (α := α) (g := g) (S := S) (K := K) hα hmin hS hw,
      st1_quad (α := α) (g := g) (S := S) (K := K) hα hmin hS hK0 hw⟩,
    ⟨st1_quad2 (α := α) (g := g) (S := S) (K := K) hα hmin hS hK0 hw⟩,
    st1_hhθ (α := α) (g := g) (S := S) (K := K) hα hα13 hmin hS hK0 hw,
    st1_hhθp (α := α) (g := g) (S := S) (K := K) hα hα13 hmin hS hK0 hw⟩

end Work.FTS_RegExport.RXT
end
end
