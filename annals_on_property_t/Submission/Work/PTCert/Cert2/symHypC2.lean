import Mathlib
import Submission.Work.PTCert.Cert2.Setup

set_option maxRecDepth 400000

noncomputable section

namespace Work.PTCert.Cert2

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D2
open Submission.PTCert.C2K
open scoped BigOperators

/-- The symmetry condition of the key `(r, g)` of the `C2` value table: the transpose
consistency of `valZ`, read off the kernel check `symOK`. -/
def symCond (r g : ℕ) : Prop :=
  valZ (keyOf r g) =
    valZ (keyOf (rinfo ((Submission.PTCert.G.em (grepE r g) - 1) / 32) / 128)
      (labE (rinfo ((Submission.PTCert.G.em (grepE r g) - 1) / 32) / 128)
        (actC cmT (piIT.get (rinfo ((Submission.PTCert.G.em (grepE r g) - 1) / 32) % 128))
          (actC cmT (ntab ((Submission.PTCert.G.em (grepE r g) - 1) % 32)) (x0c r)))))

/-- `SymHyp valZ` is exactly the pointwise condition `symCond`. -/
lemma symHyp_valZ_iff : SymHyp valZ ↔ ∀ r < 18, ∀ g < ngE r, symCond r g := Iff.rfl

/-- **The meaning of one entry of the kernel check `symOK`.**  For the row `r` with group code tree
`grepT0 = grepTs.getD r (NT.leaf 0)` and a chunk `gs` of group keys, the check `symOK … gs = true`
gives the transpose consistency `symCond r g` at every `g ∈ gs`. -/
lemma symOK_mem_eq {r g : ℕ} {gs : List ℕ} {grepT0 : NT}
    (h : symOK cmT eM nT rowT repInfoT piIT valT grepT0 labTs r gs = true)
    (hg : g ∈ gs) (hgr : grepT0 = grepTs.getD r (NT.leaf 0)) :
    symCond r g := by
  subst hgr
  unfold symOK at h
  rw [allL_eq_true] at h
  have hh := h g hg
  rw [Nat.beq_eq] at hh
  exact congrArg sv hh

/-- `symOK` over the chunk `List.range n` gives `symCond r g` for every `g < n`. -/
lemma symCond_of_range (r n : ℕ) {gs : List ℕ} {grepT0 : NT}
    (h : symOK cmT eM nT rowT repInfoT piIT valT grepT0 labTs r gs = true)
    (hgs : gs = List.range n) (hgr : grepT0 = grepTs.getD r (NT.leaf 0)) :
    ∀ g < n, symCond r g :=
  fun g hg => symOK_mem_eq h (by rw [hgs]; exact List.mem_range.mpr hg) hgr

/-- `symOK` over the chunk `List.range' lo n` gives `symCond r (lo + i)` for every `i < n`. -/
lemma symCond_of_range' (r lo n : ℕ) {gs : List ℕ} {grepT0 : NT}
    (h : symOK cmT eM nT rowT repInfoT piIT valT grepT0 labTs r gs = true)
    (hgs : gs = List.range' lo n) (hgr : grepT0 = grepTs.getD r (NT.leaf 0)) :
    ∀ i < n, symCond r (lo + i) :=
  fun i hi => symOK_mem_eq h (by rw [hgs]; exact List.mem_range'.mpr ⟨i, hi, by omega⟩) hgr

theorem symHypC2 : Submission.PTCert.G.SymHyp Work.PTCert.Cert2.valZ := by
  rw [symHyp_valZ_iff]
  intro r hr g hg
  interval_cases r
  · -- row 0
    have hng : ngE 0 = 18 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 0 18 sym_ok0_0 (by decide +kernel) rfl g hg
  · -- row 1
    have hng : ngE 1 = 399 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 1 399 sym_ok1_0 (by decide +kernel) rfl g hg
  · -- row 2
    have hng : ngE 2 = 399 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 2 399 sym_ok2_0 (by decide +kernel) rfl g hg
  · -- row 3
    have hng : ngE 3 = 215 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 3 215 sym_ok3_0 (by decide +kernel) rfl g hg
  · -- row 4
    have hng : ngE 4 = 248 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 4 248 sym_ok4_0 (by decide +kernel) rfl g hg
  · -- row 5
    have hng : ngE 5 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact symCond_of_range 5 700 sym_ok5_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact symCond_of_range' 5 700 632 sym_ok5_1 (by decide +kernel) rfl j hj
  · -- row 6
    have hng : ngE 6 = 682 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 6 682 sym_ok6_0 (by decide +kernel) rfl g hg
  · -- row 7
    have hng : ngE 7 = 399 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 7 399 sym_ok7_0 (by decide +kernel) rfl g hg
  · -- row 8
    have hng : ngE 8 = 399 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 8 399 sym_ok8_0 (by decide +kernel) rfl g hg
  · -- row 9
    have hng : ngE 9 = 399 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 9 399 sym_ok9_0 (by decide +kernel) rfl g hg
  · -- row 10
    have hng : ngE 10 = 399 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 10 399 sym_ok10_0 (by decide +kernel) rfl g hg
  · -- row 11
    have hng : ngE 11 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact symCond_of_range 11 700 sym_ok11_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact symCond_of_range' 11 700 632 sym_ok11_1 (by decide +kernel) rfl j hj
  · -- row 12
    have hng : ngE 12 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact symCond_of_range 12 700 sym_ok12_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact symCond_of_range' 12 700 632 sym_ok12_1 (by decide +kernel) rfl j hj
  · -- row 13
    have hng : ngE 13 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact symCond_of_range 13 700 sym_ok13_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact symCond_of_range' 13 700 632 sym_ok13_1 (by decide +kernel) rfl j hj
  · -- row 14
    have hng : ngE 14 = 700 + 632 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact symCond_of_range 14 700 sym_ok14_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 632 := by omega
      exact symCond_of_range' 14 700 632 sym_ok14_1 (by decide +kernel) rfl j hj
  · -- row 15
    have hng : ngE 15 = 700 + 12 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 700 with h | h
    · exact symCond_of_range 15 700 sym_ok15_0 (by decide +kernel) rfl g h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 12 := by omega
      exact symCond_of_range' 15 700 12 sym_ok15_1 (by decide +kernel) rfl j hj
  · -- row 16
    have hng : ngE 16 = 682 := by decide +kernel
    rw [hng] at hg
    exact symCond_of_range 16 682 sym_ok16_0 (by decide +kernel) rfl g hg
  · -- row 17
    have hng : ngE 17 = 700 + 700 + 221 := by decide +kernel
    rw [hng] at hg
    rcases lt_or_ge g 1400 with h | h
    · rcases lt_or_ge g 700 with h' | h'
      · exact symCond_of_range 17 700 sym_ok17_0 (by decide +kernel) rfl g h'
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
        have hj : j < 700 := by omega
        exact symCond_of_range' 17 700 700 sym_ok17_1 (by decide +kernel) rfl j hj
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hj : j < 221 := by omega
      exact symCond_of_range' 17 1400 221 sym_ok17_2 (by decide +kernel) rfl j hj

end Work.PTCert.Cert2

end
