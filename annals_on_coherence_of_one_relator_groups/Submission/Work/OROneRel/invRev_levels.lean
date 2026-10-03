import Mathlib
import Submission.Work.OROneRel.bandLoopsDefs

namespace Work.OROneRel

universe u

/-- **The running levels of `invRev L` are the complemented running levels of `L`.**

A prefix of length `k` of `FreeGroup.invRev L` is the reversal-with-flip of the complementary
*suffix* `L.drop (L.length - k)` of `L`, so its weight is `-lsig c (L.drop (L.length - k))`; splitting
`L = L.take (L.length - k) ++ L.drop (L.length - k)` turns that into
`lsig c (L.take (L.length - k)) - lsig c L`. -/
theorem lsig_take_invRev {α : Type u} (c : α → ℤ) (L : List (α × Bool)) (k : ℕ) :
    lsig c ((FreeGroup.invRev L).take k) =
      lsig c (L.take (L.length - k)) - lsig c L := by
  have h1 : (FreeGroup.invRev L).take k = FreeGroup.invRev (L.drop (L.length - k)) := by
    simp only [FreeGroup.invRev]
    rw [List.take_reverse, List.length_map, List.map_drop]
  rw [h1, lsig_invRev]
  have h3 : lsig c (L.drop (L.length - k)) = lsig c L - lsig c (L.take (L.length - k)) := by
    have h := lsig_append c (L.take (L.length - k)) (L.drop (L.length - k))
    rw [List.take_append_drop] at h
    linarith
  rw [h3]; ring

theorem invRev_levels {α : Type u} (c : α → ℤ) (L : List (α × Bool)) :
    (∀ M : ℤ, levLe c M L → levLe c (M - lsig c L) (FreeGroup.invRev L)) ∧
      (∀ M : ℤ, levGe c M L → levGe c (M - lsig c L) (FreeGroup.invRev L)) := by
  have key : ∀ k : ℕ, lsig c ((FreeGroup.invRev L).take k) =
      lsig c (L.take (L.length - k)) - lsig c L := lsig_take_invRev c L
  constructor
  · intro M hM k _
    rw [key k]
    have := hM (L.length - k) (Nat.sub_le _ _)
    linarith
  · intro M hM k _
    rw [key k]
    have := hM (L.length - k) (Nat.sub_le _ _)
    linarith

end Work.OROneRel
