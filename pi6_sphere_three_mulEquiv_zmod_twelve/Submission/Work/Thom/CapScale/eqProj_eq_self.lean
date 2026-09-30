import Mathlib
import Submission.Work.Thom.CapGeomDefs

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
