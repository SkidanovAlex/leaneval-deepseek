/-
  WilG4c / BadLocusThin — generic smoothness for definable functions `ℝⁿ → ℝ`.

  The `§5.3`/`§5.5` cell dispatch of the BNZ development has to know that the *bad locus* of a
  definable family member — the set of points where it is not `C^k` — has empty interior.

  `Work.WilG1.Cell.smooth_k_cover` exhibits the non-`C^k` locus of a definable function
  `f : ℝⁿ → ℝ` inside a finite union of `Ω`-sets of empty interior, and
  `Work.WilG1.Cell.thin_union` kills such a finite union.  This file packages the two into the
  single statement that the reductions consume, both in the general spelling on `ℝⁿ` and in the
  `famFun` / `badLoc` vocabulary of `WilG4c`:

  * `interior_compl_contDiffAt` — the general form on `ℝⁿ`;
  * `famFun_compl_contDiffAt` — the `famFun` spelling;
  * `badLoc_thin` — `interior (Work.WilG4c.badLoc f m) = ∅` for an `Ω`-bounded family member.

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG4c.StepCleanDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Generic smoothness in general dimension -/

/-- The set of points at which a function on `ℝⁿ` is `C^k` is open: `C^k` is a local property
(`ContDiffAt.eventually`). -/
theorem isOpen_contDiffAt_set {n k : ℕ} (f : (Fin n → ℝ) → ℝ) :
    IsOpen {x : Fin n → ℝ | ContDiffAt ℝ k f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  exact hx.eventually (by simp)

/-- **Generic smoothness.**  The non-`C^k` locus of a definable function on `ℝⁿ` has empty
interior (`smooth_k_cover` covers it by finitely many thin `Ω`-sets, `thin_union` kills the
union). -/
theorem interior_compl_contDiffAt (S : SOMin) (hcd : S.SharpCD) {n F D k : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : graphOf f ∈ S.Ω F D (n + 1)) :
    interior {x : Fin n → ℝ | ¬ ContDiffAt ℝ k f x} = ∅ := by
  obtain ⟨m, a, b, A, hA, hint, hsub⟩ :=
    Work.WilG1.Cell.smooth_k_cover (S := S) hcd f hf (k := k)
  have hthin : interior (⋃ i : Fin m, A i) = ∅ :=
    Work.WilG1.Cell.thin_union hcd m a b D A hA hint
  refine Set.eq_empty_of_subset_empty ?_
  calc interior {x : Fin n → ℝ | ¬ ContDiffAt ℝ k f x}
      ⊆ interior (⋃ i : Fin m, A i) := interior_mono hsub
    _ = ∅ := hthin

/-! ## 2. The `famFun` and `badLoc` spellings -/

/-- Generic smoothness for a definable family member, read through `famFun`. -/
theorem FamFunComplContDiffAt {S : SOMin} (hcd : S.SharpCD) {p N F D m : ℕ}
    {f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ}
    (hf : famGraph f ∈ S.Ω F D (p + N + 1)) :
    interior {z : Fin (p + N) → ℝ | ¬ ContDiffAt ℝ m (Work.WilG4c.famFun f) z} = ∅ :=
  interior_compl_contDiffAt S hcd (Work.WilG4c.famFun f) (by rw [Work.WilG4c.graphOf_famFun]; exact hf)

/-- `cLoc` is the `C^m`-locus (which is open). -/
theorem cLoc_eq {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (m : ℕ) :
    Work.WilG4c.cLoc f m = {z : Fin (p + N) → ℝ | ContDiffAt ℝ m (Work.WilG4c.famFun f) z} :=
  (isOpen_contDiffAt_set (Work.WilG4c.famFun f)).interior_eq

/-- **The bad locus of a definable family member is thin.**  `badLoc f m` is the complement of
the interior of the `C^m`-locus, which is the `C^m`-locus itself; the claim is then
`interior_compl_contDiffAt`. -/
theorem badLoc_thin {S : SOMin} (hcd : S.SharpCD) {p N F D m : ℕ}
    {f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ}
    (hf : famGraph f ∈ S.Ω F D (p + N + 1)) :
    interior (Work.WilG4c.badLoc f m) = ∅ := by
  rw [Work.WilG4c.badLoc, cLoc_eq f m]
  exact FamFunComplContDiffAt hcd (m := m) hf

end Work.WilkG4c
