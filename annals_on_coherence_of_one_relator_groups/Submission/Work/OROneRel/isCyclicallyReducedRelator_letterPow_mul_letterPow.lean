import Mathlib
import Submission.Work.OROneRel.Basic

-- The hypotheses `hab`, `hp`, `hq` are not needed by the argument below (which shows that any
-- concatenation of two constant blocks with equal second components is cyclically reduced), but the
-- statement is used as requested.
set_option linter.unusedVariables false

/-!
# `of a ^ p * of b ^ q` is a cyclically reduced relator

For two distinct generators `a ≠ b` and exponents `p, q ≥ 1`, the relator
`(of a) ^ p * (of b) ^ q` is cyclically reduced.

The reason is purely combinatorial.  By `FreeGroup.toWord_of_pow` the reduced words of the two
factors are `List.replicate p (a, true)` and `List.replicate q (b, true)`, so

* the concatenation `List.replicate p (a, true) ++ List.replicate q (b, true)` is already reduced:
  all its letters have second component `true`, so no two consecutive letters cancel (cancellation
  would need second components `true` and `false`), and
* its last letter is `(b, true)` while its first letter is `(a, true)`, which likewise do not
  cancel.

Hence `toWord ((of a) ^ p * (of b) ^ q)` is that concatenation, and it is cyclically reduced.

In fact the argument never uses `a ≠ b` nor `p, q ≥ 1`: any word whose letters all have the same
second component is cyclically reduced.  The statement is proved as requested.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- A concatenation of two constant blocks `List.replicate p x ++ List.replicate q y` is reduced as
soon as the two letters `x, y` have the same second component: consecutive letters never cancel,
and at the junction the condition `x.1 = y.1 → x.2 = y.2` reduces to `x.2 = y.2`. -/
lemma isReduced_replicate_append_replicate {x y : α × Bool} (hxy : x.2 = y.2) (p q : ℕ) :
    FreeGroup.IsReduced (List.replicate p x ++ List.replicate q y) := by
  unfold FreeGroup.IsReduced
  rw [List.isChain_append]
  refine ⟨List.isChain_replicate_of_rel p (by simp), List.isChain_replicate_of_rel q (by simp), ?_⟩
  intro u hu v hv
  rw [List.getLast?_replicate] at hu
  rw [List.head?_replicate] at hv
  by_cases hp : p = 0
  · rw [if_pos hp] at hu; exact absurd hu (by simp)
  rw [if_neg hp] at hu
  by_cases hq : q = 0
  · rw [if_pos hq] at hv; exact absurd hv (by simp)
  rw [if_neg hq] at hv
  obtain hu' : x = u := Option.mem_some_iff.mp hu
  obtain hv' : y = v := Option.mem_some_iff.mp hv
  subst hu'; subst hv'
  exact fun _ => hxy

theorem isCyclicallyReducedRelator_letterPow_mul_letterPow {α : Type*} {a b : α} (hab : a ≠ b)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Work.OROneRel.IsCyclicallyReducedRelator ((FreeGroup.of a)^p * (FreeGroup.of b)^q) := by
  classical
  unfold Work.OROneRel.IsCyclicallyReducedRelator
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of_pow, FreeGroup.toWord_of_pow]
  have hred : FreeGroup.IsReduced
      (List.replicate p (a, true) ++ List.replicate q (b, true)) :=
    isReduced_replicate_append_replicate (x := (a, true)) (y := (b, true)) rfl p q
  rw [hred.reduce_eq, FreeGroup.isCyclicallyReduced_iff]
  refine ⟨hred, ?_⟩
  intro u hu v hv _
  rw [List.getLast?_append] at hu
  rw [List.head?_append] at hv
  rw [List.getLast?_replicate] at hu
  rw [List.head?_replicate] at hv
  have hp0 : p ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  rw [if_neg hq0] at hu
  rw [if_neg hp0] at hv
  obtain hu' : (b, true) = u := Option.mem_some_iff.mp hu
  obtain hv' : (a, true) = v := Option.mem_some_iff.mp hv
  subst hu'; subst hv'
  rfl

end Work.OROneRel
