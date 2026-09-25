import Submission.CertJData
import Submission.CertJPosData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

/-!
# The flat `J`-data: signature positions

`wTab` is the flat list of `(position, ã, W)` triples of `cJTrips`, where `position` is the
index of `β` in `certGroupSigs`.

The positions are not computed by searching `certGroupSigs` (a list-equality search per entry,
which is expensive for the kernel).  Instead the literal `wPosL` (`Submission/CertJPosData.lean`)
records them, and one pass checks that `certGroupSigs.getD p [] = β` at each recorded `p`
(`wPos_check`); since `certGroupSigs` has no duplicates, `p` is then the index of `β`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The position of a signature in the table `certGroupSigs`. -/
def sigPosOf (β : List ℕ) : ℕ := certGroupSigs.idxOf β

/-- The flat `(position, ã, W)` data of the `J`-form. -/
def wTab : List (ℕ × ℕ × ℤ) := cJTrips.map (fun w => (sigPosOf w.1, w.2.1, w.2.2))

theorem certGroupSigs_nodup : certGroupSigs.Nodup := by decide +kernel

theorem wPosL_length : wPosL.length = cJTrips.length := by decide +kernel

/-- **The recorded positions are correct**: each is `< 272` and indexes the entry's signature. -/
theorem wPos_check : (cJTrips.zip wPosL).all (fun q =>
    decide (q.2 < 272) && (certGroupSigs.getD q.2 [] == q.1.1)) = true := by
  decide +kernel

theorem wPos_getElem (k : ℕ) (hk : k < cJTrips.length) :
    wPosL[k]'(wPosL_length ▸ hk) < 272
      ∧ certGroupSigs.getD (wPosL[k]'(wPosL_length ▸ hk)) [] = (cJTrips[k]'hk).1 := by
  have hk' : k < (cJTrips.zip wPosL).length := by
    rw [List.length_zip, wPosL_length, Nat.min_self]; exact hk
  have hmem : (cJTrips.zip wPosL)[k]'hk' ∈ cJTrips.zip wPosL := List.getElem_mem hk'
  have h := List.all_eq_true.mp wPos_check _ hmem
  rw [List.getElem_zip] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem sigPosOf_getElem (k : ℕ) (hk : k < cJTrips.length) :
    sigPosOf (cJTrips[k]'hk).1 = wPosL[k]'(wPosL_length ▸ hk) := by
  obtain ⟨hlt, hget⟩ := wPos_getElem k hk
  have hlen : wPosL[k]'(wPosL_length ▸ hk) < certGroupSigs.length := by
    rw [certGroupSigs_length]; exact hlt
  rw [sigPosOf, ← hget, List.getD_eq_getElem _ _ hlen]
  exact certGroupSigs_nodup.idxOf_getElem _ hlen

/-- Every signature that occurs in the `J`-data is one of the certificate's signatures. -/
theorem cJTrips_sig_mem' {w : List ℕ × ℕ × ℤ} (h : w ∈ cJTrips) : w.1 ∈ certGroupSigs := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  obtain ⟨hlt, hget⟩ := wPos_getElem k hk
  have hlen : wPosL[k]'(wPosL_length ▸ hk) < certGroupSigs.length := by
    rw [certGroupSigs_length]; exact hlt
  rw [← hget, List.getD_eq_getElem _ _ hlen]
  exact List.getElem_mem hlen

/-- Every position that occurs is valid. -/
theorem cJTrips_pos_lt' {w : List ℕ × ℕ × ℤ} (h : w ∈ cJTrips) : sigPosOf w.1 < 272 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  rw [sigPosOf_getElem k hk]
  exact (wPos_getElem k hk).1

/-- The position really is the position. -/
theorem sigPosOf_getD {w : List ℕ × ℕ × ℤ} (h : w ∈ cJTrips) :
    certGroupSigs.getD (sigPosOf w.1) [] = w.1 := by
  have hmem := cJTrips_sig_mem' h
  have hidx' : certGroupSigs.idxOf w.1 < certGroupSigs.length :=
    (List.idxOf_lt_length_iff).mpr hmem
  rw [sigPosOf]
  rw [List.getD_eq_getElem certGroupSigs [] hidx']
  exact List.getElem_idxOf hidx'

/-- The flat table with the recorded positions. -/
def wTabP : List (ℕ × ℕ × ℤ) := (cJTrips.zip wPosL).map (fun q => (q.2, q.1.2.1, q.1.2.2))

theorem wTab_eq : wTab = wTabP := by
  apply List.ext_getElem
  · simp [wTab, wTabP, List.length_zip, wPosL_length]
  · intro k h1 h2
    have hk : k < cJTrips.length := by simpa [wTab] using h1
    simp only [wTab, wTabP, List.getElem_map, List.getElem_zip, sigPosOf_getElem k hk]
    rfl

/-- The entries of `wTabP` whose position lies in the window `[off, off + 34)`. -/
def wWin (off : ℕ) : List (ℕ × ℕ × ℤ) :=
  wTabP.filter (fun t => decide (off ≤ t.1) && decide (t.1 < off + 34))

end Commons.NumberTheory.MaynardSieve
