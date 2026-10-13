/-
Copyright: work module for the Elgindi finite-time singularity project.

# `BumpSlotFour` — the level-`4` mixed slots of `bump` lie in the `ε`-scheme's weighted space

`bump_mixed_EpsSq_le` (`EpsSqTools/LinAux/bump_mixed_EpsSq_le.lean`) records the uniform bound
for the slots `j + i ≤ 1` of the explicit bump profile `Work.FTS.StrongEps.bump`.  The present
module extends it to **all** mixed slots with `j + i ≤ 4`:

  `EpsMem α (D_z^j D_θ^i bump)` and `EpsSq α (D_z^j D_θ^i bump) ≤ K` for every `α ∈ (0,1]`.

The mechanism is the general Lemma `exists_K_epsSq_of_supported` of that file: *any* function
which is `C^∞` on the open quadrant and vanishes off the fixed compact box
`[1/2,1] × [π/4,3π/8]` has `EpsMem α g` and `EpsSq α g ≤ 1024·(C+1)²` uniformly in `α ∈ (0,1]`,
where `C` is the sup of `|g|` on the box.  Both hypotheses are available for every iterated mixed
derivative of `bump`:

* `SmoothOpen.mixed` (`OpenQDefs`): the iterated operators `D_z`, `D_θ` preserve `C^∞` on the
  open quadrant (`bump` is in fact `C^∞` everywhere, `contDiff_bump`);
* `bump_iter_eq_zero_of_not_mem` (`BumpDefs`): every iterated mixed derivative of `bump` vanishes
  outside the closed box.

What is left is only the *uniformity in the slot*: `j + i ≤ 4` leaves the 15 slots
`(0,0), (1,0), (0,1), …, (0,4)`, and the constants delivered slot by slot must be merged.  The
constants are extracted once and for all as `mixedBumpK j i` (a `Classical.choose` of the
slotwise existence statement, which needs no hypothesis on `j`, `i`), and merged by a finite sum,
which is positive because every slot constant is strictly positive.  The condition `j + i ≤ 4`
is used only to place `j` and `i` inside `Finset.range 5`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.bump_mixed_EpsSq_le
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.EpsSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.StrongEps.EpsSqTools.LinAux

/-! ## The slotwise constants -/

/-- **A single mixed slot of `bump`.**  For every `j i : ℕ` the function `D_z^j D_θ^i bump` lies
in the weighted space `X` of the `ε`-scheme, with a bound on `EpsSq` which is uniform in
`α ∈ (0,1]` (no condition relating `j` and `i` is needed). -/
theorem exists_K_epsSq_mixed_bump (j i : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1,
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ≤ K :=
  exists_K_epsSq_of_supported (Work.FTS.StrongEps.smoothOpen_bump.mixed j i)
    (fun _ _ h => Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem
      (lt_disj_of_not_mem_bumpBox h) j i)

/-- The uniform `EpsSq`-bound of the slot `(j,i)`, chosen once and for all. -/
noncomputable def mixedBumpK (j i : ℕ) : ℝ :=
  Classical.choose (exists_K_epsSq_mixed_bump j i)

theorem mixedBumpK_pos (j i : ℕ) : 0 < mixedBumpK j i :=
  (Classical.choose_spec (exists_K_epsSq_mixed_bump j i)).1

theorem mixedBumpK_spec (j i : ℕ) (α : ℝ) (hα : α ∈ Set.Ioc 0 1) :
    Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ∧
    Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ≤
      mixedBumpK j i :=
  (Classical.choose_spec (exists_K_epsSq_mixed_bump j i)).2 α hα

/-! ## The target -/

theorem BumpSlotFour :
    ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1, ∀ j i : ℕ, j + i ≤ 4 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ≤ K := by
  refine ⟨(∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, mixedBumpK j i) + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun i _ => le_of_lt (mixedBumpK_pos j i)) zero_lt_one
  · intro α hα j i hji
    have hj : j ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have hi : i ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have h1 : mixedBumpK j i ≤ ∑ i' ∈ Finset.range 5, mixedBumpK j i' :=
      Finset.single_le_sum (fun i' _ => le_of_lt (mixedBumpK_pos j i')) hi
    have h2 : (∑ i' ∈ Finset.range 5, mixedBumpK j i')
        ≤ ∑ j' ∈ Finset.range 5, ∑ i' ∈ Finset.range 5, mixedBumpK j' i' :=
      Finset.single_le_sum
        (fun j' _ => Finset.sum_nonneg fun i' _ => le_of_lt (mixedBumpK_pos j' i')) hj
    exact ⟨(mixedBumpK_spec j i α hα).1,
      le_trans (mixedBumpK_spec j i α hα).2 (by linarith)⟩

end Work.FTS.StrongEps.EpsRLX
