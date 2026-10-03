import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

/-- Two blocks of letters with *distinct* first components concatenate to a reduced word.
Concretely: if `c.1 ≠ d.1` then `List.replicate p c ++ List.replicate q d` is reduced, because
within each block all letters are equal (so no cancellation can occur) and across the boundary the
two letters have different generators. -/
theorem isReduced_replicate_append_replicate_ne_fst {α : Type*} {c d : α × Bool}
    (h : c.1 ≠ d.1) (p q : ℕ) :
    FreeGroup.IsReduced (List.replicate p c ++ List.replicate q d) := by
  -- the last letter of the first block is `c`
  have hlast : ∀ {p : ℕ} {x : α × Bool}, x ∈ (List.replicate p c).getLast? → x = c := by
    intro p x hx
    rw [List.getLast?_replicate] at hx
    split_ifs at hx with hp
    · exact absurd hx (by simp)
    · exact (Option.some.inj (Option.mem_def.mp hx)).symm
  -- the first letter of the second block is `d`
  have hhead : ∀ {q : ℕ} {y : α × Bool}, y ∈ (List.replicate q d).head? → y = d := by
    intro q y hy
    rw [List.head?_replicate] at hy
    split_ifs at hy with hq
    · exact absurd hy (by simp)
    · exact (Option.some.inj (Option.mem_def.mp hy)).symm
  show List.IsChain (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) _
  refine List.IsChain.append ?_ ?_ ?_
  · exact List.isChain_replicate_of_rel p (by simp)
  · exact List.isChain_replicate_of_rel q (by simp)
  · intro x hx y hy
    rw [hlast hx, hhead hy]
    exact fun hcd => absurd hcd h

theorem relatorNorm_letterPow_mul_letterPow {α : Type*} {a b : α} (hab : a ≠ b) (p q : ℕ) :
    Work.OROneRel.relatorNorm ((FreeGroup.of a)^p * (FreeGroup.of b)^q) = p + q := by
  classical
  have hred : FreeGroup.IsReduced
      (List.replicate p ((a, true) : α × Bool) ++ List.replicate q (b, true)) :=
    isReduced_replicate_append_replicate_ne_fst (by simpa using hab) p q
  -- the word of the product is the expected reduced word, so its length is `p + q`
  have hword : FreeGroup.toWord ((FreeGroup.of a)^p * (FreeGroup.of b)^q)
      = List.replicate p (a, true) ++ List.replicate q (b, true) := by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_of_pow, FreeGroup.toWord_of_pow,
      FreeGroup.IsReduced.reduce_eq hred]
  have h : Work.OROneRel.relatorNorm ((FreeGroup.of a)^p * (FreeGroup.of b)^q)
      = FreeGroup.norm ((FreeGroup.of a)^p * (FreeGroup.of b)^q) := rfl
  rw [h, FreeGroup.norm, hword, List.length_append, List.length_replicate,
    List.length_replicate]

end Work.OROneRel
