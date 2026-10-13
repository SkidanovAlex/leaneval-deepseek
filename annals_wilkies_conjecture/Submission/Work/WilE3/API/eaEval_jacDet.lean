import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

theorem eaEval_jacDet {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (x : Fin k → ℝ) :
    eaEval c (Work.WilE3.jacDet c h ι) x =
      (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x).det := by
  rw [Work.WilE3.jacDet, eaEval, RingHom.map_det]
  congr 1

end Work.WilE3.API
