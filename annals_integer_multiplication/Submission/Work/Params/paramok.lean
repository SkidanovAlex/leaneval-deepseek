import Mathlib
import Submission.Work.Params.basic
import Submission.Work.Params.defs
import Submission.Work.Params.qall
import Submission.Work.Params.nt1
import Submission.Work.Params.tsfacts
import Submission.Work.Params.uparfacts
import Submission.Work.Params.sswindow
import Submission.Work.Params.sscoprime
import Submission.Work.Params.rparbig

/-! Assembly: the explicitly constructed lists `tsPar n`, `ssPar n` satisfy `ParamOK n`. -/

set_option autoImplicit false

namespace Work.Params

open HvdH

theorem ParamOK_tsPar_ssPar (n : ℕ) (hn : n1 ≤ n) : ParamOK n (tsPar n) (ssPar n) := by
  obtain ⟨hr1, hr2, hkr, hkT, hd⟩ := rparbig n hn
  obtain ⟨hlen, hpair, hprod, hmem, _hgetD⟩ := tsfacts n hkr hd
  obtain ⟨hcop, hodd⟩ := sscoprime n
  refine ⟨hlen, ?_, hpair, hprod, hmem, sswindow n hr1 hr2, hcop, hodd⟩
  unfold ssPar
  rw [List.length_map, List.length_range]

end Work.Params
