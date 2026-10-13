import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS_RegExport.RXT.L12_Fstar_add_c4
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-
The difference of the `Theta`-parts of the profiles `f` and `F_* + f`:
`Theta α F z θ = (1/(4α)) * sin (2θ) * L12 F z` and
`L12 (fun z θ => Fstar α z θ + f z θ) z = L12 (Fstar α) z + L12 f z`
(`Work.FTS_RegExport.RXT.L12_Fstar_add_c4`, whose hypotheses are exactly
`ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0` and `Work.Spaces.HkMem α 4 f`,
both available from `ClassC α f` via `hf.reg.forall 4` and
`Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem`), together with
`Work.Construction.L12_Fstar_eq hα hα1 hz.le : L12 (Fstar α) z = 2 * α / (1 + z)`.
-/
theorem ThetaDiff {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.ClassC.ClassC α f) :
    ∀ z θ : ℝ, 0 < z →
      Work.Construction.Theta α f z θ
        - Work.Construction.Theta α (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = -Real.sin (2 * θ) / (2 * (1 + z)) := by
  intro z θ hz
  -- `f` is `C^4` on the open quadrant and honestly in `ℋ⁴`
  have hcd : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.reg.forall 4
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem
  -- additivity of `L₁₂` over `F_* + f`
  have hadd : Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z :=
    Work.FTS_RegExport.RXT.L12_Fstar_add_c4 hα hα1 hcd hmem hz.le
  -- the reference value `L₁₂(F_*) = 2α/(1+z)`
  have hF : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hα hα1 hz.le
  simp only [Work.Construction.Theta, Work.Construction.s2, hadd, hF]
  field_simp
  ring

end Work.FTS.StrongEps.E5Aux2
