import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs

namespace Work.FIArea2.R6

open Finset

/-- The number of non-zero multiples of `E` in `[-X, X]`, times `E`, is at most `2X`.
Indeed the non-zero multiples of `E` in `[-X,X]` are exactly the `±E·k` with `1 ≤ k ≤ X/E`,
and there are at most `X/E` of each sign. -/
theorem card_zPz_filter_dvd (E X : ℕ) (hE : 1 ≤ E) :
    ((Work.FIArea2.R6.zPz X).filter (fun h => (E : ℤ) ∣ h)).card * E ≤ 2 * X := by
  set N : ℕ := X / E with hN
  have hEpos : 0 < E := by omega
  have hNE : N * E ≤ X := by
    rw [hN]; exact Nat.div_mul_le_self X E
  set T : Finset ℤ := (zPz X).filter (fun h => (E : ℤ) ∣ h) with hT
  set Spos : Finset ℤ := (Finset.Icc (1 : ℤ) (N : ℤ)).image (fun k => (E : ℤ) * k) with hSpos
  set Sneg : Finset ℤ := (Finset.Icc (1 : ℤ) (N : ℤ)).image (fun k => -((E : ℤ) * k)) with hSneg
  have hcardIcc : (Finset.Icc (1 : ℤ) (N : ℤ)).card = N := by
    rw [Int.card_Icc]; simp
  have hcard_pos : Spos.card ≤ N := by
    rw [hSpos]
    calc ((Finset.Icc (1 : ℤ) (N : ℤ)).image (fun k => (E : ℤ) * k)).card
        ≤ (Finset.Icc (1 : ℤ) (N : ℤ)).card := Finset.card_image_le
      _ = N := hcardIcc
  have hcard_neg : Sneg.card ≤ N := by
    rw [hSneg]
    calc ((Finset.Icc (1 : ℤ) (N : ℤ)).image (fun k => -((E : ℤ) * k))).card
        ≤ (Finset.Icc (1 : ℤ) (N : ℤ)).card := Finset.card_image_le
      _ = N := hcardIcc
  have hsub : T ⊆ Spos ∪ Sneg := by
    intro h hh
    rw [hT, Finset.mem_filter] at hh
    obtain ⟨hhz, hhdvd⟩ := hh
    rw [zPz, Finset.mem_filter] at hhz
    obtain ⟨hhmem, hhne⟩ := hhz
    rw [Finset.mem_Icc] at hhmem
    obtain ⟨hlow, hhigh⟩ := hhmem
    have hnatabs : h.natAbs ≤ X := by omega
    obtain ⟨c, hc⟩ := hhdvd
    have hcne : c ≠ 0 := by
      intro hc0
      rw [hc0, mul_zero] at hc
      exact hhne hc
    have hcnat : c.natAbs ≤ N := by
      have h1 : ((E : ℤ) * c).natAbs ≤ X := by rw [← hc]; exact hnatabs
      rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
      rw [hN, Nat.le_div_iff_mul_le hEpos, Nat.mul_comm c.natAbs E]
      exact h1
    rw [Finset.mem_union]
    rcases lt_trichotomy c 0 with hclt | hceq | hcgt
    · right
      rw [hSneg, Finset.mem_image]
      refine ⟨-c, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        have hcn : (-c).natAbs ≤ N := by rw [Int.natAbs_neg]; exact hcnat
        omega
      · rw [hc]; ring
    · exfalso
      rw [hceq, mul_zero] at hc
      exact hhne hc
    · left
      rw [hSpos, Finset.mem_image]
      refine ⟨c, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · rw [hc]
  have hcardT : T.card ≤ 2 * N := by
    calc T.card ≤ (Spos ∪ Sneg).card := Finset.card_le_card hsub
      _ ≤ Spos.card + Sneg.card := Finset.card_union_le Spos Sneg
      _ ≤ N + N := add_le_add hcard_pos hcard_neg
      _ = 2 * N := by ring
  calc T.card * E ≤ (2 * N) * E := Nat.mul_le_mul_right E hcardT
    _ = 2 * (N * E) := by ring
    _ ≤ 2 * X := Nat.mul_le_mul_left 2 hNE

end Work.FIArea2.R6
