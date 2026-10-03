import Mathlib
import Submission.Work.OROneRel.bandLoopsDefs

/-!
# The levels of the powers of the reversed word

Let `T` be a word whose walk, started at level `0`, stays in the window `[0,L]` and whose total
weight is `lsig c T = 1`.  Then the walk of `FreeGroup.invRev T` runs from level `0` down to level
`-1`, staying inside `[-1, L - 1]`; its `n`-th power therefore stays inside `[-n, L]`.

The computation is the exact reverse of the one for `lpow T n` (`band_lpow_levels`): a prefix of
length `k` of `FreeGroup.invRev T` is the reversal-with-flipped-letters of the complementary suffix
`T.drop (T.length - k)`, so its weight is the weight of that suffix with the sign changed (and the
global weight `lsig c T` subtracted).
-/

namespace Work.OROneRel

universe u

/-- **The running levels of `invRev L` are the complemented running levels of `L`.**

A prefix of length `k` of `FreeGroup.invRev L` is the reversal-with-flip of the complementary
*suffix* `L.drop (L.length - k)`, so its weight is `-lsig c (L.drop (L.length - k))`; splitting
`L = L.take (L.length - k) ++ L.drop (L.length - k)` turns that into
`lsig c (L.take (L.length - k)) - lsig c L`. -/
private theorem lsig_take_invRev {α : Type u} (c : α → ℤ) (L : List (α × Bool)) (k : ℕ) :
    lsig c ((FreeGroup.invRev L).take k) =
      lsig c (L.take (L.length - k)) - lsig c L := by
  have h1 : (FreeGroup.invRev L).take k = FreeGroup.invRev (L.drop (L.length - k)) := by
    simp only [FreeGroup.invRev]
    rw [List.take_reverse, List.length_map, List.map_drop]
  rw [h1, CoedgeBase.lsig_invRev]
  have h3 : lsig c (L.drop (L.length - k)) = lsig c L - lsig c (L.take (L.length - k)) := by
    have h := CoedgeBase.lsig_append c (L.take (L.length - k)) (L.drop (L.length - k))
    rw [List.take_append_drop] at h
    linarith
  rw [h3]; ring

/-- **The levels of the `n`-fold power of a word of weight `-1`.**  If every level of the walk of
`W` lies in `[A,B]` and `lsig c W = -1`, then every level of the walk of `lpow W n` lies in
`[A + 1 - n, B]`: copy number `r` starts at level `-r`, so inside it the level stays in
`[A - r, B - r]`. -/
private theorem lpow_levels {α : Type u} {c : α → ℤ} {W : List (α × Bool)} {A B : ℤ}
    (hW : lsig c W = -1) (hlo : levGe c A W) (hhi : levLe c B W) (n : ℕ) :
    levLe c B (lpow W n) ∧ levGe c (A + 1 - (n : ℤ)) (lpow W n) := by
  induction n with
  | zero =>
    rw [lpow_zero]
    exact ⟨levLe_nil.mpr (by simpa [lsig] using hhi 0 (Nat.zero_le _)),
      levGe_nil.mpr (by
        have h := hlo W.length le_rfl
        rw [List.take_length, hW] at h
        push_cast
        linarith)⟩
  | succ n ih =>
    obtain ⟨ihLe, ihGe⟩ := ih
    rw [lpow_succ]
    constructor
    · refine levLe_append hhi ?_
      have : B - lsig c W = B + 1 := by rw [hW]; ring
      rw [this]
      exact levLe_mono ihLe (by linarith)
    · have h1 : levGe c (A + 1 - ((n : ℤ) + 1)) W :=
        levGe_mono hlo (by linarith)
      have h2 : levGe c (A + 1 - ((n : ℤ) + 1) - lsig c W) (lpow W n) := by
        have : A + 1 - ((n : ℤ) + 1) - lsig c W = A + 1 - (n : ℤ) := by rw [hW]; ring
        rw [this]
        exact ihGe
      exact levGe_append h1 h2

theorem invRev_lpow_levels {α : Type u} {c : α → ℤ} {T : List (α × Bool)} {L : ℤ}
    (h : band c 0 L T) (h1 : lsig c T = 1) (n : ℕ) :
    levLe c L (lpow (FreeGroup.invRev T) n) ∧ levGe c (-(n : ℤ)) (lpow (FreeGroup.invRev T) n) := by
  have hW : lsig c (FreeGroup.invRev T) = -1 := by
    rw [CoedgeBase.lsig_invRev, h1]
  -- every level of `invRev T` is in `[-1, L - 1]`
  have hhi : levLe c (L - 1) (FreeGroup.invRev T) := by
    intro k _
    rw [lsig_take_invRev c T k]
    have hk' := h (T.length - k) (Nat.sub_le _ _)
    linarith
  have hlo : levGe c (-1) (FreeGroup.invRev T) := by
    intro k _
    rw [lsig_take_invRev c T k]
    have hk' := h (T.length - k) (Nat.sub_le _ _)
    linarith
  obtain ⟨hLe, hGe⟩ := lpow_levels hW hlo hhi n
  refine ⟨levLe_mono hLe (by linarith), ?_⟩
  have heq : (-1 : ℤ) + 1 - (n : ℤ) = -(n : ℤ) := by ring
  rwa [heq] at hGe

end Work.OROneRel
