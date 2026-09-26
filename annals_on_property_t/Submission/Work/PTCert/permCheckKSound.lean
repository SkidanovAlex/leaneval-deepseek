import Mathlib
import Submission.Work.PTCert.Checkers
import Submission.Work.PTCert.permCheckSound

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
Definitions at the end of `Submission/Work/PTCert/Checkers.lean`: `mergeF` (fuel), `msortK`, `isPermOf`.
Prove `PermCheckKSound`: `mergeF f s t ~ s ++ t` for every fuel (induction on fuel), `splitL l` gives
`p.1 ++ p.2 ~ l` (already proved for the sibling `PermCheckSound` in `Submission/Work/PTCert/permCheckSound.lean`
— reuse its `splitL` lemma), hence `msortK f l ~ l`; `==` on `List ℕ` true ⇒ equal lists.  ~60 lines.
-/

/-!
# Soundness of the kernel-evaluable permutation check

`mergeF` (merging with fuel) yields a permutation of the concatenation of its two arguments: with
fuel `0` it literally *is* that concatenation, and each recursive step conses one of the two heads
onto a merge with strictly smaller fuel, which is exactly the insertion of that head at the front of
the concatenation (`List.perm_middle` in the second case).  `splitL` splits a list into two lists
whose concatenation is a permutation of it (proved in `permCheckSound.lean`), so induction on the
fuel gives `msortK f l ~ l`.  Finally `msortK 40 l == e` forces `msortK 40 l = e`, whence
`isPermOf l e = true` implies `l ~ e`.  Sortedness is never used.
-/

namespace Work.PTCert

open Submission.PTCert

/-- Merging two lists with fuel `f` yields a permutation of their concatenation. -/
theorem mergeF_perm : ∀ (f : ℕ) (s t : List ℕ), (mergeF f s t).Perm (s ++ t) := by
  intro f
  induction f with
  | zero => intro s t; exact List.Perm.refl _
  | succ f ih =>
    intro s t
    cases s with
    | nil => simp [mergeF]
    | cons a s' =>
      cases t with
      | nil => simp [mergeF]
      | cons b t' =>
        simp only [mergeF]
        -- `bif` is `Bool.cond`, so `split` does not apply; both branches are closed by `exact`
        -- since `cond true _ _` and `cond false _ _` are definitionally the two branches.
        cases h : Nat.ble a b
        · exact (List.Perm.cons b (ih (a :: s') t')).trans
            (List.perm_middle (l₁ := a :: s') (l₂ := t')).symm
        · exact List.Perm.cons a (ih s' (b :: t'))

/-- Kernel-evaluable merge sort never loses or duplicates elements. -/
theorem msortK_perm : ∀ (f : ℕ) (l : List ℕ), (msortK f l).Perm l := by
  intro f
  induction f with
  | zero => intro l; exact List.Perm.refl _
  | succ f ih =>
    intro l
    cases l with
    | nil => simp [msortK]
    | cons a t =>
      cases t with
      | nil => simp [msortK]
      | cons b t' =>
        simp only [msortK]
        exact (mergeF_perm _ (msortK f (splitL (a :: b :: t')).1)
            (msortK f (splitL (a :: b :: t')).2)).trans
          ((List.Perm.append (ih (splitL (a :: b :: t')).1)
            (ih (splitL (a :: b :: t')).2)).trans (splitL_perm (a :: b :: t')))

theorem permCheckKSound : PermCheckKSound := by
  intro l e h
  have hsort : (msortK 40 l).Perm l := msortK_perm 40 l
  have heq : msortK 40 l = e := by
    have h' := h
    simp only [isPermOf] at h'
    exact beq_iff_eq.mp h'
  rw [heq] at hsort
  exact hsort.symm

end Work.PTCert
