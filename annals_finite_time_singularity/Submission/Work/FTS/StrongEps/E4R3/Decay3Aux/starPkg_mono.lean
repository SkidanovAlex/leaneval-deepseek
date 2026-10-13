import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Decay3Aux

theorem starPkg_mono {α Cs Cs' : ℝ} (hα : 0 < α) (h : Cs ≤ Cs') {Φs : Work.FTS.Galerkin.Fn}
    (hp : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) : Work.FTS.VocabO2.StarPkgo2 α Cs' Φs := by
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hmul : ∀ x : ℝ, x ≤ Cs * α → x ≤ Cs' * α := fun x hx =>
    le_trans hx (mul_le_mul_of_nonneg_right h hα0)
  exact ⟨{ sol := hp.sol
           smooth := hp.smooth
           R := ⟨hp.R.1, hmul _ hp.R.2⟩
           dU := ⟨hp.dU.1, hmul _ hp.dU.2⟩
           V := ⟨hp.V.1, hmul _ hp.V.2⟩
           vanishU := hp.vanishU
           Vth := ⟨hp.Vth.1, hmul _ hp.Vth.2⟩ },
    ⟨hp.RW.1, hmul _ hp.RW.2⟩,
    ⟨hp.VW.1, hmul _ hp.VW.2⟩,
    ⟨hp.VzW.1, hmul _ hp.VzW.2⟩,
    ⟨hp.UsW.1, hmul _ hp.UsW.2⟩,
    ⟨hp.UszW.1, hmul _ hp.UszW.2⟩⟩

end Work.FTS.StrongEps.E4R3.Decay3Aux
