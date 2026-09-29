import Mathlib
import Submission.Work.Resample.sliceB1defs

/-!
# `Work.Resample.buQWhs`: the shift list `egHs m` is exactly the window `egHset m`

The word `q` of the one-dimensional `B̃` map reads its shift list off `egHs m`, while the
mathematics of paper Lemmas 4.8--4.12 is indexed by the window `egHset m = {h | 0 < |h| ≤ m}`.
This module collects the (purely combinatorial) list facts that identify the two:
`egHs m` is the ascending enumeration `[-m,…,-1] ++ [1,…,m]` of `egHset m`.
-/

namespace Work.Resample

open HvdH

/-- Membership in the retained window: `h ∈ egHset m ↔ h ≠ 0 ∧ |h| ≤ m`. -/
lemma buQWhs_egHset_mem_iff (m : ℕ) (h : ℤ) : h ∈ egHset m ↔ h ≠ 0 ∧ h.natAbs ≤ m := by
  simp only [egHset, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, ?_⟩
    have h3 : |h| ≤ ((m : ℕ) : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h3
    exact_mod_cast h3
  · rintro ⟨h0, h1⟩
    have h2 : |h| ≤ ((m : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h1
    exact ⟨h0, (abs_le.mp h2).1, (abs_le.mp h2).2⟩

/-- Membership in the shift list: `h ∈ egHs m ↔ h ≠ 0 ∧ |h| ≤ m`. -/
lemma buQWhs_egHs_mem_iff (m : ℕ) (h : ℤ) : h ∈ egHs m ↔ h ≠ 0 ∧ h.natAbs ≤ m := by
  unfold egHs
  rw [List.mem_append]
  constructor
  · rintro (hh | hh)
    · simp only [List.mem_map, List.mem_range] at hh
      obtain ⟨i, hi, hih⟩ := hh
      refine ⟨?_, ?_⟩
      · omega
      · rw [← hih]
        exact Int.natAbs_coe_sub_coe_le_of_le (le_of_lt hi) le_rfl
    · simp only [List.mem_map, List.mem_range] at hh
      obtain ⟨i, hi, hih⟩ := hh
      refine ⟨?_, ?_⟩
      · omega
      · rw [← hih]
        have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast (show i + 1 ≤ m by omega)
  · rintro ⟨h0, hle⟩
    rcases lt_trichotomy h 0 with hlt | heq | hgt
    · left
      have hneg : (h.natAbs : ℤ) = -h := by
        rw [← Int.natAbs_neg h, Int.natAbs_of_nonneg (by omega)]
      have hm : -h ≤ (m : ℤ) := by
        have h2 : ((h.natAbs : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast hle
        omega
      simp only [List.mem_map, List.mem_range]
      refine ⟨(m + h).toNat, ?_, ?_⟩
      · have hc : (((m + h).toNat : ℕ) : ℤ) = m + h := Int.toNat_of_nonneg (by omega)
        omega
      · rw [Int.toNat_of_nonneg (by omega)]
        ring
    · omega
    · right
      have hpos : (h.natAbs : ℤ) = h := Int.natAbs_of_nonneg (le_of_lt hgt)
      have hm : h ≤ (m : ℤ) := by
        have h2 : ((h.natAbs : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast hle
        omega
      simp only [List.mem_map, List.mem_range]
      refine ⟨(h - 1).toNat, ?_, ?_⟩
      · have hc : (((h - 1).toNat : ℕ) : ℤ) = h - 1 := Int.toNat_of_nonneg (by omega)
        omega
      · rw [Int.toNat_of_nonneg (by omega)]
        ring

/-- The shift list has no repetitions. -/
lemma buQWhs_nodup (m : ℕ) : (egHs m).Nodup := by
  unfold egHs
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.map ?_ (List.nodup_range)
    intro a b hab
    have h : (a : ℤ) = (b : ℤ) := by linarith
    exact_mod_cast h
  · refine List.Nodup.map ?_ (List.nodup_range)
    intro a b hab
    have h : (a : ℤ) = (b : ℤ) := by linarith
    exact_mod_cast h
  · intro a ha b hb
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨i, hi, hia⟩ := ha
    obtain ⟨j, hj, hjb⟩ := hb
    omega

/-- The shift list has exactly `2m` entries. -/
lemma buQWhs_length (m : ℕ) : (egHs m).length = 2 * m := by
  unfold egHs
  simp
  omega

theorem buQWhs (m : ℕ) :
    (Work.Resample.egHs m).toFinset = Work.Resample.egHset m ∧ (Work.Resample.egHs m).Nodup ∧
    (Work.Resample.egHs m).length = 2 * m ∧
    (∀ h ∈ Work.Resample.egHs m, h ≠ 0) ∧ (∀ h ∈ Work.Resample.egHs m, h.natAbs ≤ m) ∧
    (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ m → h ∈ Work.Resample.egHs m) := by
  refine ⟨?_, buQWhs_nodup m, buQWhs_length m, ?_, ?_, ?_⟩
  · ext h
    rw [List.mem_toFinset, buQWhs_egHs_mem_iff, buQWhs_egHset_mem_iff]
  · intro h hh
    exact (buQWhs_egHs_mem_iff m h).mp hh |>.1
  · intro h hh
    exact (buQWhs_egHs_mem_iff m h).mp hh |>.2
  · intro h h0 hle
    exact (buQWhs_egHs_mem_iff m h).mpr ⟨h0, hle⟩

end Work.Resample
