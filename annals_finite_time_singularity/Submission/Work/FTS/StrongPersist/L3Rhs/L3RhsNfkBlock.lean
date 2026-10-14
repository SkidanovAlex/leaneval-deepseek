import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkTerms
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkAsm
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS_MuLamOK.Rows.Rl0Open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

theorem L3RhsNfkBlock : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NFkSum α f)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NFkSum α f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NFkSum α f)
        ≤ C * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
  NfkAux.nfk_assembly NfkAux.N4gg_mem NfkAux.N5gg_mem NfkAux.NfkFstarBlock
    NfkAux.N4sg_mem NfkAux.N5sg_mem Work.FTS.OpenPkg.fkH_field

end Work.FTS.StrongPersist.L3Rhs
