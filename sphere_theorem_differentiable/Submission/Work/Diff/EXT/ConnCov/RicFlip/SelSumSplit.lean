import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.ShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ConnCov.RicTr
open scoped BigOperators

/-!
# The selection-sum split

`SelSum F (j+1) (m+1)` sums `sel (F (j+1)) f` over all strictly monotone maps
`f : Fin (j+1) → Fin (m+1)`.  Splitting that index set according to the value of `f` at `0` gives
the two components `SelSumIns` (the case `f 0 = 0`, i.e. `f` is the image of `insF`) and `SelSumSh`
(the case `f 0 ≠ 0`, i.e. `f` is the image of `shiftF`), both landing in arity `m+1`:

`SelSum F (j+1) (m+1) = SelSumIns F j m + SelSumSh F (j+1) m`.

The two index bijections are `insF : Hom j m ≃ {g | g 0 = 0}` (inverse `tailF`) and
`shiftF : Hom (j+1) m ≃ {g | g 0 ≠ 0}` (inverse `shiftInvF`), from
`Submission.Work.Diff.EXT.ConnCov.RicTr.ShiftDefs`.
-/

theorem SelSumSplit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (F : (k : ℕ) → Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k) (j m : ℕ) :
    Work.Diff.EXT.ConnCov.RicTr.SelSum F (j + 1) (m + 1)
      = Work.Diff.EXT.ConnCov.RicTr.SelSumIns F j m
        + Work.Diff.EXT.ConnCov.RicTr.SelSumSh F (j + 1) m := by
  classical
  -- Split the sum over `Hom (j+1) (m+1)` according to the value at `0`.
  have hsplit : (∑ g : Hom (j + 1) (m + 1), sel (F (j + 1)) g.val)
      = (∑ g ∈ Finset.univ.filter (fun g : Hom (j + 1) (m + 1) => g.val 0 = 0),
            sel (F (j + 1)) g.val)
        + (∑ g ∈ Finset.univ.filter (fun g : Hom (j + 1) (m + 1) => ¬ (g.val 0 = 0)),
            sel (F (j + 1)) g.val) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  -- The `0`-case: reindex by `insF : Hom j m → Hom (j+1) (m+1)`.
  have h1 : (∑ f : Hom j m, sel (F (j + 1)) (insF f).val)
      = ∑ g ∈ Finset.univ.filter (fun g : Hom (j + 1) (m + 1) => g.val 0 = 0),
            sel (F (j + 1)) g.val := by
    refine Finset.sum_bij (fun (a : Hom j m) (_ : a ∈ (Finset.univ : Finset (Hom j m))) => insF a)
      ?_ ?_ ?_ ?_
    · intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact insF_val_zero a
    · intro a₁ _ a₂ _ heq
      exact insF_injective heq
    · intro b hb
      obtain ⟨_, hb0⟩ := Finset.mem_filter.mp hb
      exact ⟨tailF b hb0, Finset.mem_univ _, insF_tailF b hb0⟩
    · intro a _
      rfl
  -- The nonzero case: reindex by `shiftF : Hom (j+1) m → Hom (j+1) (m+1)`.
  have h2 : (∑ f : Hom (j + 1) m, sel (F (j + 1)) (shiftF f).val)
      = ∑ g ∈ Finset.univ.filter (fun g : Hom (j + 1) (m + 1) => ¬ (g.val 0 = 0)),
            sel (F (j + 1)) g.val := by
    refine Finset.sum_bij
      (fun (a : Hom (j + 1) m) (_ : a ∈ (Finset.univ : Finset (Hom (j + 1) m))) => shiftF a)
      ?_ ?_ ?_ ?_
    · intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact shiftF_val_ne_zero a
    · intro a₁ _ a₂ _ heq
      exact shiftF_injective heq
    · intro b hb
      obtain ⟨_, hb0⟩ := Finset.mem_filter.mp hb
      exact ⟨shiftInvF b hb0, Finset.mem_univ _, shiftF_shiftInvF b hb0⟩
    · intro a _
      rfl
  simp only [SelSum, SelSumIns, SelSumSh]
  rw [hsplit, h1, h2]

end Work.Diff.EXT.ConnCov.RicFlip
