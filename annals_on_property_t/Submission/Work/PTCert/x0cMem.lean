import Mathlib
import Submission.Work.PTCert.rowHelp
import Submission.Work.PTCert.nSem

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.D

/-- From the kernel check `rowself_ok`, for `r < 18` the row code `cG rowT r` is `< 10368` and its
`eM`-value is nonzero. -/
theorem x0c_val_lt (r : ℕ) (hr : r < 18) :
    cG rowT r < 10368 ∧ eG eM (cG rowT r) ≠ 0 := by
  have h := (allR_eq_true 18
    (fun r => Nat.beq (lab0 eM repInfoT (cG rowT r)) r && Nat.blt (cG rowT r) 10368 &&
      !(Nat.beq (eG eM (cG rowT r)) 0))).mp C.rowself_ok r hr
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, hlt⟩, hne⟩ := h
  exact ⟨Nat.blt_eq.mp hlt, NSemAux.not_beq_zero_eq_true.mp hne⟩

theorem x0cMem : ∀ r < 18, cG rowT r ∈ eAll := by
  intro r hr
  obtain ⟨hlt, hne⟩ := x0c_val_lt r hr
  exact NSemAux.mem_eAll_of_em_ne_zero hlt hne

end Work.PTCert
