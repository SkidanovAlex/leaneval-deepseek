import Submission.CertJData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

/-!
# The flat `J`-data: signature positions

`wTab` is the flat list of `(position, ã, W)` triples of `cJTrips`, where `position` is the
index of `β` in `certGroupSigs`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The position of a signature in the table `certGroupSigs`. -/
def sigPosOf (β : List ℕ) : ℕ := certGroupSigs.idxOf β

/-- The flat `(position, ã, W)` data of the `J`-form. -/
def wTab : List (ℕ × ℕ × ℤ) := cJTrips.map (fun w => (sigPosOf w.1, w.2.1, w.2.2))

/-- Every signature that occurs in the `J`-data is one of the certificate's signatures. -/
theorem cJTrips_sig_mem : cJTrips.all (fun w => decide (w.1 ∈ certGroupSigs)) = true := by decide

theorem cJTrips_sig_mem' {w : List ℕ × ℕ × ℤ} (h : w ∈ cJTrips) : w.1 ∈ certGroupSigs :=
  of_decide_eq_true (List.all_eq_true.mp cJTrips_sig_mem w h)

/-- Every position that occurs is valid. -/
theorem cJTrips_pos_lt : cJTrips.all (fun w => decide (sigPosOf w.1 < 272)) = true := by decide

theorem cJTrips_pos_lt' {w : List ℕ × ℕ × ℤ} (h : w ∈ cJTrips) : sigPosOf w.1 < 272 :=
  of_decide_eq_true (List.all_eq_true.mp cJTrips_pos_lt w h)

/-- The position really is the position. -/
theorem sigPosOf_getD {w : List ℕ × ℕ × ℤ} (h : w ∈ cJTrips) :
    certGroupSigs.getD (sigPosOf w.1) [] = w.1 := by
  have hmem := cJTrips_sig_mem' h
  have hidx' : certGroupSigs.idxOf w.1 < certGroupSigs.length :=
    (List.idxOf_lt_length_iff).mpr hmem
  rw [sigPosOf]
  rw [List.getD_eq_getElem certGroupSigs [] hidx']
  exact List.getElem_idxOf hidx'

end Commons.NumberTheory.MaynardSieve
