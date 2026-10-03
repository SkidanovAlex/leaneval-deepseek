import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Elementary facts about the sets `κ[L]` and `[-N,N]`

The bookkeeping facts used by the diagonal mass lower bounds
(`Work.Peluse.UControl.diagMassGen` and its pieces) on Peluse's Gowers box norms:

* the arithmetic-progression set `κ[L] = {κ, 2κ, …, Lκ}` has exactly `L` elements when `κ ≠ 0`;
* the symmetric interval `[-N,N]` has `2N+1` elements;
* membership in `[-N,N]` is `|x| ≤ N`;
* every element of `κ[L]` has `|a| ≤ |κ| L`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.UControl

/-- The arithmetic-progression set `κ[L]` has exactly `L` elements, for `κ ≠ 0`. -/
lemma card_arithIcc_of_ne {κ : ℤ} (hκ : κ ≠ 0) (L : ℕ) :
    (Work.Peluse.arithIcc κ L).card = L := by
  rw [Work.Peluse.arithIcc, Finset.card_image_of_injOn]
  · simp
  · rintro a - b - hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hκ hab
    exact_mod_cast h

/-- The symmetric interval `[-N,N]` has `2N+1` elements. -/
lemma card_symIcc_of (N : ℕ) : (Work.Peluse.symIcc N).card = 2 * N + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- Membership in the symmetric interval: `x ∈ [-N,N] ↔ |x| ≤ N`. -/
lemma mem_symIcc_iff {N : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc N ↔ |x| ≤ (N : ℤ) := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  exact abs_le.symm

/-- The set `κ[L]` is nonempty when `κ ≠ 0` and `1 ≤ L`. -/
lemma arithIcc_nonempty {κ : ℤ} (hκ : κ ≠ 0) {L : ℕ} (hL : 1 ≤ L) :
    (Work.Peluse.arithIcc κ L).Nonempty := by
  refine ⟨κ * 1, ?_⟩
  rw [Work.Peluse.arithIcc]
  exact Finset.mem_image.mpr ⟨1, by simp [hL], by simp⟩

/-- Every element of `κ[L]` satisfies `|a| ≤ |κ| L`. -/
lemma natAbs_le_of_mem_arithIcc {κ : ℤ} {L : ℕ} {a : ℤ}
    (ha : a ∈ Work.Peluse.arithIcc κ L) : a.natAbs ≤ κ.natAbs * L := by
  rw [Work.Peluse.arithIcc] at ha
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
  rw [Finset.mem_Icc] at hn
  rw [Int.natAbs_mul]
  have h1 : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
  rw [h1]
  exact Nat.mul_le_mul_left _ hn.2

/-- The cardinality of `symIcc` as a real number. -/
lemma card_symIcc_real (N : ℕ) : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
  rw [card_symIcc_of]; push_cast; ring

end Work.Peluse.UControl
