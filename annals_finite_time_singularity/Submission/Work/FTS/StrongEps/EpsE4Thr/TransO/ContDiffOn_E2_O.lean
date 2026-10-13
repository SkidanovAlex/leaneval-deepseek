import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2_pkg
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSBase
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.E2hat_mem_contDiff_O
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **`E₂ α f` is `C³` on the open quadrant in the *open* class.**

`E₂ α f = Ê₂ f + Γ(θ)·radS α f z` splits into a clean defect `Ê₂ f`, whose `C³`-regularity on
the open quadrant only needs `SmoothOpen f` (`E2hat_mem_contDiff_O`), and a product of the
angular factor `Γ α` (`C^∞` on `(0,π/2)`) with the radial profile `radS α f`, which is `C³` on
`(0,∞)` as soon as `L₁₂ f ∈ C⁴` there (`radS_contDiffOn_three` + `contDiffOn_four_L12f`, the
open-class replacement of `L12_contDiffOn_four_of_five`). -/
theorem ContDiffOn_E2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.Transfer.E2 α f))
      Work.Construction.Qd := by
  -- the class data
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  -- `L₁₂ f` is `C⁴` on `(0,∞)`, hence `radS α f` is `C³` there
  have hA : ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0) :=
    E2O.contDiffOn_four_L12f α hα hα1 hO hmem5
  have hradS : ContDiffOn ℝ 3 (fun z => Work.FTS.CoercivityFix.Transfer.radS α f z)
      (Set.Ioi 0) :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1 hA
  -- the clean defect `Ê₂ f` is `C³` on the open quadrant
  have hmem3 : Work.Spaces.HkMem α 3 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 3 (by norm_num) hmem5
  have hmemd3 : Work.Spaces.HkMem α 3 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 3) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5)
  have hE2hat : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
      Work.Construction.Qd :=
    (E2O.E2hat_mem_contDiff_O α hα (by norm_num : 3 ≤ 4) hO hmem3 hmemd3).2
  -- the separated summand `Γ(θ)·radS α f z`
  have hGam : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.Construction.Qd :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_Gam_Qd α 3
  have hR : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Transfer.radS α f p.1) Work.Construction.Qd :=
    hradS.comp contDiffOn_fst (fun p hp => hp.1)
  have hsum : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2
      + Work.Spaces.Gam α p.2 * Work.FTS.CoercivityFix.Transfer.radS α f p.1)
      Work.Construction.Qd := hE2hat.add (hGam.mul hR)
  refine hsum.congr ?_
  intro p hp
  simp only [Function.uncurry, Work.FTS.CoercivityFix.Transfer.E2]

end Work.FTS.StrongEps.EpsE4Thr.TransO
