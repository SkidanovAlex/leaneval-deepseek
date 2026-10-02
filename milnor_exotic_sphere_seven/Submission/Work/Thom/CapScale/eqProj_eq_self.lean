import Mathlib
import Submission.Work.Thom.CapGeomDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom.CapScale

theorem eqProj_eq_self (n : ℕ) (v : MSph (n + 1)) (h : Work.Morse.strip v.1 ≠ 0)
    (hv : lastC n v.1 = 0) : eqProj n v h = v := by
  apply Subtype.ext
  rw [eqProj_val]
  have hv' : v.1.ofLp (Fin.last n) = 0 := hv
  have hval : scaleV n 0 v.1 = v.1 := by
    rw [scaleV, hv, mul_zero, ← hv']
    exact Work.Morse.snocLp_strip v.1
  rw [hval, v.2, inv_one, one_smul]

end Work.Thom.CapScale
