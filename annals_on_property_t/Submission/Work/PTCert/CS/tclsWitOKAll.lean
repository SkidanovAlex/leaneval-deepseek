import Mathlib
import Submission.Work.PTCert.CSAux

namespace Work.PTCert.CS

open Submission.PTCert

/-- Pointwise form of one kernel chunk `tclsOK … (List.range' s n) = true`:
every `q ∈ [s, s+n)` satisfies the class-witness check. -/
lemma chunk_ptwise (s n : ℕ)
    (h : tclsOK Submission.PTCert.D.canonT Submission.PTCert.D.tclT (List.range' s n) = true) :
    ∀ q, s ≤ q → q < s + n →
      clsWitOK Submission.PTCert.D.canonT [invLk (q / 81), q % 81, 0, 0]
        (w34 Submission.PTCert.D.tclT q) = true := by
  intro q h1 h2
  refine (Work.PTCert.allL_iff_CSAux _ _).mp h q ?_
  rw [List.mem_range']
  exact ⟨q - s, by omega, by omega⟩

/-- The twelve `decide +kernel` chunks in `Checks/TC*.lean` cover `[0, 6561)`
contiguously, and each chunk's pointwise statement is the target check (with the
kernel letter form `invLk` in place of `invL`). -/
theorem tclsWitOKAll : ∀ p < 6561,
    Submission.PTCert.clsWitOK Submission.PTCert.D.canonT [Submission.PTCert.invL (p / 81), p % 81, 0, 0]
      (Submission.PTCert.w34 Submission.PTCert.D.tclT p) = true := by
  have h1 := chunk_ptwise 0 550 Submission.PTCert.C.tcl_ok0_0
  have h2 := chunk_ptwise 550 550 Submission.PTCert.C.tcl_ok0_1
  have h3 := chunk_ptwise 1100 550 Submission.PTCert.C.tcl_ok1_0
  have h4 := chunk_ptwise 1650 550 Submission.PTCert.C.tcl_ok1_1
  have h5 := chunk_ptwise 2200 550 Submission.PTCert.C.tcl_ok2_0
  have h6 := chunk_ptwise 2750 550 Submission.PTCert.C.tcl_ok2_1
  have h7 := chunk_ptwise 3300 550 Submission.PTCert.C.tcl_ok3_0
  have h8 := chunk_ptwise 3850 550 Submission.PTCert.C.tcl_ok3_1
  have h9 := chunk_ptwise 4400 550 Submission.PTCert.C.tcl_ok4_0
  have h10 := chunk_ptwise 4950 550 Submission.PTCert.C.tcl_ok4_1
  have h11 := chunk_ptwise 5500 550 Submission.PTCert.C.tcl_ok5_0
  have h12 := chunk_ptwise 6050 511 Submission.PTCert.C.tcl_ok5_1
  intro p hp
  rcases Nat.lt_or_ge p 550 with hp1 | hp1
  · simpa only [Work.PTCert.invLk_eq_invL] using h1 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 1100 with hp2 | hp2
  · simpa only [Work.PTCert.invLk_eq_invL] using h2 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 1650 with hp3 | hp3
  · simpa only [Work.PTCert.invLk_eq_invL] using h3 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 2200 with hp4 | hp4
  · simpa only [Work.PTCert.invLk_eq_invL] using h4 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 2750 with hp5 | hp5
  · simpa only [Work.PTCert.invLk_eq_invL] using h5 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 3300 with hp6 | hp6
  · simpa only [Work.PTCert.invLk_eq_invL] using h6 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 3850 with hp7 | hp7
  · simpa only [Work.PTCert.invLk_eq_invL] using h7 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 4400 with hp8 | hp8
  · simpa only [Work.PTCert.invLk_eq_invL] using h8 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 4950 with hp9 | hp9
  · simpa only [Work.PTCert.invLk_eq_invL] using h9 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 5500 with hp10 | hp10
  · simpa only [Work.PTCert.invLk_eq_invL] using h10 p (by omega) (by omega)
  rcases Nat.lt_or_ge p 6050 with hp11 | hp11
  · simpa only [Work.PTCert.invLk_eq_invL] using h11 p (by omega) (by omega)
  · simpa only [Work.PTCert.invLk_eq_invL] using h12 p (by omega) (by omega)

end Work.PTCert.CS
