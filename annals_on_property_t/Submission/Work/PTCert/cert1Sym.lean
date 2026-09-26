import Mathlib
import Submission.Work.PTCert.cert1Aux

/-!
# PTCert — `Work.PTCert.cert1Sym`

The transpose consistency (`SymHyp cert1pv`) of the certificate-1 value table, in the pointwise
form of `cert1SymCond`.  The kernel checks `Submission.PTCert.C1K.sym_ok{r}_{j}` say that
`symOK cmT eM nT rowT repInfoT piIT valT grepT{r} labTs r gs = true` for a chunk `gs` of group
keys; `symOK` computes exactly the equality of the two `p8 valT` fields that `cert1SymCond`
expresses after transporting along `sv`.  The chunks are consecutive intervals of `[0, ngE r)`
(`List.range n` from `0`, `List.range' lo n` in general), so they cover every `g < ngE r`.
-/

set_option maxRecDepth 400000
set_option maxHeartbeats 0

noncomputable section

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K

/-- **The meaning of one entry of the kernel check `symOK`.**  If the chunk `gs` of group keys is
checked for row `r` with the row's group-code tree `grepT0 = grepTs.getD r (NT.leaf 0)`, then
`symOK … = true` gives the transpose consistency `cert1SymCond r g` at every `g ∈ gs`. -/
lemma cert1SymOK_mem_eq {r g : ℕ} {gs : List ℕ} {grepT0 : NT}
    (h : symOK cmT eM nT rowT repInfoT piIT valT grepT0 labTs r gs = true)
    (hg : g ∈ gs) (hgr : grepT0 = grepTs.getD r (NT.leaf 0)) :
    cert1SymCond r g := by
  subst hgr
  unfold symOK at h
  rw [allL_iff] at h
  have hh := h g hg
  rw [Nat.beq_eq] at hh
  exact congrArg sv hh

/-- `symOK` over the chunk `List.range n` gives `cert1SymCond r g` for every `g < n`. -/
lemma cert1Sym_of_range (r n : ℕ) {gs : List ℕ} {grepT0 : NT}
    (h : symOK cmT eM nT rowT repInfoT piIT valT grepT0 labTs r gs = true)
    (hgs : gs = List.range n) (hgr : grepT0 = grepTs.getD r (NT.leaf 0)) :
    ∀ g < n, cert1SymCond r g :=
  fun g hg => cert1SymOK_mem_eq h (by rw [hgs]; exact List.mem_range.mpr hg) hgr

/-- `symOK` over the chunk `List.range' lo n` gives `cert1SymCond r (lo + i)` for every `i < n`. -/
lemma cert1Sym_of_range' (r lo n : ℕ) {gs : List ℕ} {grepT0 : NT}
    (h : symOK cmT eM nT rowT repInfoT piIT valT grepT0 labTs r gs = true)
    (hgs : gs = List.range' lo n) (hgr : grepT0 = grepTs.getD r (NT.leaf 0)) :
    ∀ i < n, cert1SymCond r (lo + i) :=
  fun i hi => cert1SymOK_mem_eq h (by rw [hgs]; exact List.mem_range'.mpr ⟨i, hi, by omega⟩) hgr

theorem cert1Sym : ∀ r < 18, ∀ g < Submission.PTCert.G.ngE r, Work.PTCert.cert1SymCond r g := by
  intro r hr g hg
  interval_cases r
  · -- row 0: `[0, 18)`
    have hng : ngE 0 = 18 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 0 18 sym_ok0_0 (by decide +kernel) rfl g hg
  · -- row 1: `[0, 399)`
    have hng : ngE 1 = 399 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 1 399 sym_ok1_0 (by decide +kernel) rfl g hg
  · -- row 2: `[0, 399)`
    have hng : ngE 2 = 399 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 2 399 sym_ok2_0 (by decide +kernel) rfl g hg
  · -- row 3: `[0, 215)`
    have hng : ngE 3 = 215 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 3 215 sym_ok3_0 (by decide +kernel) rfl g hg
  · -- row 4: `[0, 248)`
    have hng : ngE 4 = 248 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 4 248 sym_ok4_0 (by decide +kernel) rfl g hg
  · -- row 5: `[0, 700)`, `[700, 1332)`
    have hng : ngE 5 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact cert1Sym_of_range 5 700 sym_ok5_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact cert1Sym_of_range' 5 700 632 sym_ok5_1 (by decide +kernel) rfl j hj
  · -- row 6: `[0, 682)`
    have hng : ngE 6 = 682 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 6 682 sym_ok6_0 (by decide +kernel) rfl g hg
  · -- row 7: `[0, 399)`
    have hng : ngE 7 = 399 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 7 399 sym_ok7_0 (by decide +kernel) rfl g hg
  · -- row 8: `[0, 399)`
    have hng : ngE 8 = 399 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 8 399 sym_ok8_0 (by decide +kernel) rfl g hg
  · -- row 9: `[0, 399)`
    have hng : ngE 9 = 399 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 9 399 sym_ok9_0 (by decide +kernel) rfl g hg
  · -- row 10: `[0, 399)`
    have hng : ngE 10 = 399 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 10 399 sym_ok10_0 (by decide +kernel) rfl g hg
  · -- row 11: `[0, 700)`, `[700, 1332)`
    have hng : ngE 11 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact cert1Sym_of_range 11 700 sym_ok11_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact cert1Sym_of_range' 11 700 632 sym_ok11_1 (by decide +kernel) rfl j hj
  · -- row 12: `[0, 700)`, `[700, 1332)`
    have hng : ngE 12 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact cert1Sym_of_range 12 700 sym_ok12_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact cert1Sym_of_range' 12 700 632 sym_ok12_1 (by decide +kernel) rfl j hj
  · -- row 13: `[0, 700)`, `[700, 1332)`
    have hng : ngE 13 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact cert1Sym_of_range 13 700 sym_ok13_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact cert1Sym_of_range' 13 700 632 sym_ok13_1 (by decide +kernel) rfl j hj
  · -- row 14: `[0, 700)`, `[700, 1332)`
    have hng : ngE 14 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact cert1Sym_of_range 14 700 sym_ok14_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact cert1Sym_of_range' 14 700 632 sym_ok14_1 (by decide +kernel) rfl j hj
  · -- row 15: `[0, 700)`, `[700, 712)`
    have hng : ngE 15 = 700 + 12 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact cert1Sym_of_range 15 700 sym_ok15_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 12 := by omega
      exact cert1Sym_of_range' 15 700 12 sym_ok15_1 (by decide +kernel) rfl j hj
  · -- row 16: `[0, 682)`
    have hng : ngE 16 = 682 := by decide +kernel
    rw [hng] at hg
    exact cert1Sym_of_range 16 682 sym_ok16_0 (by decide +kernel) rfl g hg
  · -- row 17: `[0, 700)`, `[700, 1400)`, `[1400, 1621)`
    have hng : ngE 17 = 700 + 700 + 221 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 1400 with h | h
    · rcases lt_or_ge g 700 with h' | h'
      · exact cert1Sym_of_range 17 700 sym_ok17_0 (by decide +kernel) rfl g h'
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
        have hj : j < 700 := by omega
        exact cert1Sym_of_range' 17 700 700 sym_ok17_1 (by decide +kernel) rfl j hj
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 221 := by omega
      exact cert1Sym_of_range' 17 1400 221 sym_ok17_2 (by decide +kernel) rfl j hj

end Work.PTCert

end
