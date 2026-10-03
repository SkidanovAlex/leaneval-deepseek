import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decor_pow_flatMap

/-!
# The root of the window decomposition of a power

Since `cohom c u = 1` means that the weight of `u` is *zero*, every copy of `u` in the walk of
`u ^ l` starts afresh at the same level (`Work.OROneRel.decor_pow_flatMap`).  Hence the deleted walk
word of `u ^ l` is the `l`-th power of the deleted walk word of `u`:

  `winRootList Wt c lo hi (u ^ l) = (List.replicate l (winRootList Wt c lo hi u)).flatten`,
  `winRoot Wt c lo hi (u ^ l) = winRoot Wt c lo hi u ^ l`.

This is the statement that the *domain* of the one-relator complex of `u ^ l` has relator `v ^ l`
with `v = winRoot Wt c lo hi u`, i.e. that the vertex group of the residual decomposition really is
`⟨winBeta | winRoot ^ l⟩` for the complex of `u ^ l`; it is what makes the target's `⟨β | v ^ l⟩`
(with the *same* `l`) the correct shape.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- `filterMap` commutes with flattening a repetition. -/
private theorem filterMap_flatten_replicate {γ : Type*} (F : (α × ℤ) × Bool → Option γ)
    (M : List ((α × ℤ) × Bool)) (n : ℕ) :
    (List.flatten (List.replicate n M)).filterMap F =
      List.flatten (List.replicate n (M.filterMap F)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.filterMap_append, ih]
    rw [← List.flatten_cons, ← List.replicate_succ]

/-- The deleted walk word of `u ^ l` is the `l`-th power of the deleted walk word of `u`. -/
theorem winRootList_pow (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) (l : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) (hcu : Work.OROneRel.cohom c u = 1) :
    Work.OROneRel.winRootList Wt c lo hi (u ^ l) =
      (List.replicate l (Work.OROneRel.winRootList Wt c lo hi u)).flatten := by
  classical
  rw [Work.OROneRel.winRootList, Work.OROneRel.decor_pow_flatMap c u l hcyc hcu,
    Work.OROneRel.winRootList]
  exact filterMap_flatten_replicate _ _ l

/-- `FreeGroup.mk` of a flattened repetition is a power. -/
private theorem mk_flatten_replicate_pow (M : List (α × Bool)) (l : ℕ) :
    FreeGroup.mk (List.flatten (List.replicate l M)) = (FreeGroup.mk M) ^ l := by
  induction l with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero, FreeGroup.one_eq_mk]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

/-- The root of the window decomposition of `u ^ l` is the `l`-th power of the root of `u`. -/
theorem winRoot_pow (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) (l : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) (hcu : Work.OROneRel.cohom c u = 1) :
    Work.OROneRel.winRoot Wt c lo hi (u ^ l) = (Work.OROneRel.winRoot Wt c lo hi u) ^ l := by
  classical
  rw [Work.OROneRel.winRoot, winRootList_pow Wt c lo hi u l hcyc hcu, Work.OROneRel.winRoot]
  exact mk_flatten_replicate_pow _ l

end Work.OROneRel
