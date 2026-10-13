import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

/-- `F_*(z,θ) = α (Γ(θ)/c) 2z/(1+z)²` is `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)`.

The factors are separate: `Γ(θ) = (sin θ cos²θ)^{α/3}` is `C^n` on the open quadrant for
every `n` (`contDiffOn_Gam_Q0`, via `ContDiffOn.rpow_const_of_ne` — on `Q0` the base
`sin θ cos²θ` is strictly positive), the normalisation `c α` is a nonzero constant
(`c_bounds`, using `0 < α ≤ 1`), and `2z/(1+z)²` is `C^n` on `Ioi 0`
(`contDiffOn_FM_Fstar`).  `ContDiffOn` is closed under constants, products and quotients by a
nowhere-zero function, which is all the statement needs. -/
theorem Fstar_Q0_c4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Fstar α)) Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.contDiffOn_Gam_Q0 α 4
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h1 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 :=
    hGam.div contDiffOn_const (fun _ _ => hc)
  have h2 : ContDiffOn ℝ 4
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_fst_of (Work.FTS_RegExport.RXT.contDiffOn_FM_Fstar 4)
  exact (h2.mul h3).congr (fun _ _ => rfl)

end Work.FTS_RegExport.RXT.Sys.GdotAux
