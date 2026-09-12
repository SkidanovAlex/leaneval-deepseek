import Mathlib
import Submission.Fold
import Submission.DirSet
import Submission.DirCycle

/-!
# Gap cells between consecutive spike directions (end-to-end instantiation)

This module instantiates the whole verified chain for one angular gap of the
hedgehog direction spine:

    DirCycle.no_dir_between_get (no direction strictly between consecutive
      dirList entries) + DirSet.endpoints_no_arg_of_dirSet_free
      (no direction in [c,d] ⟹ the `hno` gap hypothesis)
      + Fold.gap_cell_zero (gap hypothesis ⟹ the per-cell Cauchy identity
      in `cellExpr` form)

to obtain: for any two consecutive directions `x := (dirList S).get i`,
`y := (dirList S).get (i+1)` and any angular range `[c,d]` strictly inside
the open gap `(x, y)` (hence automatically inside `(-π, π]`), the cell over
`[[a,b]] ×ℂ [[c,d]]` of the pulled-back integrand
`w ↦ h (exp w) · exp w` has zero boundary integral for every `h`
holomorphic off the hedgehog `star S`.

This is the per-gap cell family that the E2b fold
(`Submission.Fold.cellExpr_sum_range`, `cellExpr_sum_zero`) sums over the
spine; the wrap-around gap after the last direction is handled separately
via `exp`-periodicity (future session).
-/

noncomputable section

open scoped Complex Real Interval
open Complex

namespace Submission.SpineGaps

open Submission.DirSet
open Submission.DirCycle
open Submission.Fold

/-- A direction (argument of a spike endpoint) lies in `(-π, π]`. -/
lemma arg_mem_Ioc (S : Finset ℂ) (θ : ℝ) (hθ : θ ∈ dirSet S) :
    θ ∈ Set.Ioc (-Real.pi) Real.pi := by
  classical
  rcases (mem_dirSet_iff S θ).mp hθ with ⟨z, hz, hzθ | hzθ⟩
  · rw [← hzθ]
    exact Complex.arg_mem_Ioc (z ^ 2)
  · rw [← hzθ]
    exact Complex.arg_mem_Ioc (z ^ 4)

/-- Every dirList entry lies in `(-π, π]`. -/
lemma dirList_get_mem_Ioc (S : Finset ℂ) (i : Fin (dirList S).length) :
    (dirList S).get i ∈ Set.Ioc (-Real.pi) Real.pi := by
  exact arg_mem_Ioc S ((dirList S).get i)
    ((dirList_mem_iff S ((dirList S).get i)).mp (by
      simpa using (List.get_mem (dirList S) i.isLt)))

/-- **Gap-cell Cauchy between consecutive directions.**  If `[c,d]` lies
strictly inside the gap between consecutive dirList entries `x < y`, then
the pulled-back cell over `[[a,b]] ×ℂ [[c,d]]` has zero boundary integral
for every `h` holomorphic off the hedgehog. -/
lemma gap_cell_between_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (a b : ℝ) (i : Fin (dirList S).length) (hi : i.val + 1 < (dirList S).length)
    {c d : ℝ} (hxc : (dirList S).get i < c) (hcd : c < d)
    (hdy : d < (dirList S).get ⟨i.val + 1, hi⟩) :
    cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) a b c d = 0 := by
  classical
  let x : ℝ := (dirList S).get i
  let y : ℝ := (dirList S).get ⟨i.val + 1, hi⟩
  have hxy : x < y := by
    dsimp [x, y]
    exact dirList_get_strict S (i := i) (j := ⟨i.val + 1, hi⟩)
      (by simpa using Nat.lt_succ_self i.val)
  -- range conditions for the cell lemma: -π < c and d ≤ π
  have hxIoc : x ∈ Set.Ioc (-Real.pi) Real.pi := by
    dsimp [x]
    exact dirList_get_mem_Ioc S i
  have hyIoc : y ∈ Set.Ioc (-Real.pi) Real.pi := by
    dsimp [y]
    exact dirList_get_mem_Ioc S ⟨i.val + 1, hi⟩
  have hxc' : x < c := by simpa [x] using hxc
  have hdy' : d < y := by simpa [y] using hdy
  have hcl : -Real.pi < c := lt_trans hxIoc.1 hxc'
  have hdu : d ≤ Real.pi := le_of_lt (lt_of_lt_of_le hdy' hyIoc.2)
  -- no direction strictly inside (x, y): instantiate no_dir_between_get
  have hnoDir : ∀ θ ∈ dirSet S, θ ∉ Set.Icc c d := by
    intro θ hθ hθcd
    have hxθ : x < θ := lt_of_lt_of_le hxc' hθcd.1
    have hθy : θ < y := lt_of_le_of_lt hθcd.2 hdy'
    exact no_dir_between_get S i hi θ hθ ⟨hxθ, hθy⟩
  -- bridge to the hno hypothesis of the cell lemma
  have hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc c d ∧ Complex.arg (z ^ 4) ∉ Set.Icc c d :=
    endpoints_no_arg_of_dirSet_free (S := S) (c := c) (d := d) hnoDir
  exact gap_cell_zero (S := S) hS0 hh a b hcd hcl hdu hno

end Submission.SpineGaps

end
