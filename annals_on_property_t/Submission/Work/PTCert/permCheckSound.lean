import Mathlib
import Submission.Work.PTCert.Checkers

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions in `Submission/Work/PTCert/Checkers.lean`: `mergeL`, `splitL`, `msortF` (fuel), `isPermRange`.

# Soundness of the permutation check

`msortF f l` is always a permutation of `l`: `mergeL s t` is a permutation of `s ++ t`, `splitL l`
splits `l` into two lists whose concatenation is a permutation of `l`, and merging preserves this by
induction on the fuel.  Hence `msortF 40 l = List.range n` forces `l ~ List.range n`.  Sortedness is
never used.
-/

namespace Work.PTCert

open Submission.PTCert

/-- Merging two lists yields a permutation of their concatenation. -/
theorem mergeL_perm (s t : List ℕ) : (mergeL s t).Perm (s ++ t) := by
  induction s, t using mergeL.induct with
  | case1 l => simp [mergeL]
  | case2 l hl =>
    cases l with
    | nil => exact (hl rfl).elim
    | cons a s => simp [mergeL]
  | case3 a s b t h ih =>
    simp only [mergeL, h, cond_true, List.cons_append]
    exact List.Perm.cons a ih
  | case4 a s b t h ih =>
    simp only [mergeL, h, cond_false]
    exact (List.Perm.cons b ih).trans (List.perm_middle (l₁ := a :: s) (l₂ := t)).symm

/-- `splitL` splits a list into two lists whose concatenation is a permutation of it. -/
theorem splitL_perm (l : List ℕ) : ((splitL l).1 ++ (splitL l).2).Perm l := by
  induction l using splitL.induct with
  | case1 => simp [splitL]
  | case2 d t ih =>
    simp only [splitL]
    exact List.Perm.cons d (List.perm_append_comm.symm.trans ih)

/-- Merge sort with fuel never loses or duplicates elements. -/
theorem msortF_perm : ∀ (f : ℕ) (l : List ℕ), (msortF f l).Perm l := by
  intro f
  induction f with
  | zero => intro l; simp [msortF]
  | succ f ih =>
    intro l
    cases l with
    | nil => simp [msortF]
    | cons a t =>
      cases t with
      | nil => simp [msortF]
      | cons b t' =>
        simp only [msortF]
        exact (mergeL_perm _ _).trans
          ((List.Perm.append (ih (splitL (a :: b :: t')).1)
            (ih (splitL (a :: b :: t')).2)).trans (splitL_perm (a :: b :: t')))

theorem permCheckSound : PermCheckSound := by
  intro l n h
  have hsort : (msortF 40 l).Perm l := msortF_perm 40 l
  have heq : msortF 40 l = List.range n := by
    have h' := h
    simp only [isPermRange] at h'
    exact beq_iff_eq.mp h'
  rw [heq] at hsort
  exact hsort.symm

end Work.PTCert
