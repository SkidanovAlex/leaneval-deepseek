import Mathlib
import Submission.Work.OROneRel.MagnusRewrite

namespace Work.OROneRel

universe u

/-- The recursion step of `magRew` at a letter different from `t`: the letter is kept (decorated with
the current exponent sum `acc` of `t`) and the exponent sum is left unchanged for the tail. -/
lemma magRew_cons_of_ne {α : Type u} (t : α) (acc : ℤ) (hd : α × Bool)
    (tl : List (α × Bool)) (h : hd.1 ≠ t) :
    magRew t acc (hd :: tl) = ((⟨hd.1, h⟩, acc), hd.2) :: magRew t acc tl := by
  classical
  dsimp only [magRew]
  simp [h]

theorem magRew_attach_of_notMem {α : Type u} (t : α) (i : ℤ) (L : List (α × Bool))
    (hL : ∀ p ∈ L, p.1 ≠ t) :
    magRew t i L = L.attach.map
      (fun q => (((⟨q.1.1, hL q.1 q.2⟩, i) : {x : α // x ≠ t} × ℤ), q.1.2)) := by
  classical
  induction L with
  | nil => simp [magRew]
  | cons hd tl ih =>
    have hhd : hd.1 ≠ t := hL hd List.mem_cons_self
    have htl : ∀ p ∈ tl, p.1 ≠ t := fun p hp => hL p (List.mem_cons_of_mem hd hp)
    rw [magRew_cons_of_ne t i hd tl hhd, List.attach_cons, List.map_cons]
    congr 1
    rw [ih htl, List.map_map]
    apply List.map_congr_left
    intro a _
    rfl

end Work.OROneRel
