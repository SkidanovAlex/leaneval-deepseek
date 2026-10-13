import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegPkgGal.PartsAssembly
import Submission.Work.FTS.RegPkgGal.GalMinConv
import Submission.Work.FTS.RegPkgGal.GalMinAssembly
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS_RegExport.RX0.RecutAux
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RX0.hzmodp_ext_c4
import Submission.Work.FTS_RegExport.RX0.MainRecut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RX0

theorem forallRegPkgOfParts {α : ℝ} {g Φ : Work.FTS.Galerkin.Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, Work.FTS.RegExportIface.GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S g Φ) :
    ∀ S > 0, Work.FTS.RegPkgGal.RegPkg' α S (Work.FTS.RegPkgGal.Avort m)
      (Work.FTS.RegPkgGal.Bdyn m) (Work.FTS.RegPkgGal.extG g) := by
  exact forall_regPkg_of_parts' H H5

end Work.FTS_RegExport.RX0
