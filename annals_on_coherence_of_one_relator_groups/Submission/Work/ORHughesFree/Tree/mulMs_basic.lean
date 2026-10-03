import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs

/-!
# Elementary properties of the multiset product `mulMs`

`mulMs M N = {a + b | a ∈ M, b ∈ N}` is the operation on families induced by multiplication of
trees.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

theorem mulMs_zero_left (N : Multiset Tree) : mulMs 0 N = 0 := by
  simp [mulMs]

theorem mulMs_zero_right (M : Multiset Tree) : mulMs M 0 = 0 := by
  simp [mulMs]

/-- `mulMs` distributes over addition in the first argument. -/
theorem mulMs_add_left (X Y M : Multiset Tree) :
    mulMs (X + Y) M = mulMs X M + mulMs Y M := by
  simp only [mulMs, Multiset.add_bind]

/-- `mulMs` distributes over addition in the second argument. -/
theorem mulMs_add_right (X M N : Multiset Tree) :
    mulMs X (M + N) = mulMs X M + mulMs X N := by
  show X.bind (fun a => (M + N).map (fun b => a + b)) =
    X.bind (fun a => M.map (fun b => a + b)) + X.bind (fun a => N.map (fun b => a + b))
  rw [show (fun a : Tree => (M + N).map (fun b => a + b)) =
      (fun a : Tree => M.map (fun b => a + b) + N.map (fun b => a + b)) from
      funext (fun a => Multiset.map_add (fun b => a + b) M N)]
  rw [Multiset.bind_add]

/-- Membership in `mulMs`. -/
theorem mem_mulMs {M N : Multiset Tree} {t : Tree} :
    t ∈ mulMs M N ↔ ∃ a ∈ M, ∃ b ∈ N, a + b = t := by
  simp only [mulMs, Multiset.mem_bind, Multiset.mem_map]

/-- `mulMs M N` is empty if and only if a factor is empty. -/
theorem mulMs_ne_zero {M N : Multiset Tree} : mulMs M N ≠ 0 ↔ M ≠ 0 ∧ N ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun hM => h (by rw [hM, mulMs_zero_left]),
      fun hN => h (by rw [hN, mulMs_zero_right])⟩
  · rintro ⟨hM, hN⟩ h0
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hM
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hN
    have hmem : a + b ∈ mulMs M N := mem_mulMs.mpr ⟨a, ha, b, hb, rfl⟩
    rw [h0] at hmem
    exact absurd hmem (by simp)

end Work.ORHughesFree.Tree
