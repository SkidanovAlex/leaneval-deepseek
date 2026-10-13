import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.GammaW_Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-- The angular derivative `∂_θ F_*` of the model profile is `C^∞` on the open quadrant.
`SmoothQuad` is preserved by `Work.Spaces.pth` on any open set
(`LocData.contDiffOn_pth`), and `F_*` itself is `SmoothQuad` for every real `α`
(`LocData.SmoothQuad_Fstar`, i.e. `LocData.Fstar_smoothQuad`). -/
theorem row15_SmoothQuadPthFstar (α : ℝ) : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth (Work.Construction.Fstar α)) :=
  Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
    (Work.FTS.LocData.contDiffOn_pth Work.FTS.LocData.isOpen_quadU
      (Work.FTS.LocData.SmoothQuad_Fstar α))

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
