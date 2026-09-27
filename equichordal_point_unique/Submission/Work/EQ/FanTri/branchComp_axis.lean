import Mathlib
import Submission.Work.EQ.FanTri.BranchCompDefs
import Submission.Work.EQ.FanSep.axis_walk

namespace Work.EQ.FanTri

open Work.EQ

/-- The real axis walk sends the grid `-1/2 + 2ℤ` into itself: `axStep a s x = -x ± 1` and
`-(-1/2 + 2k) ± 1 = -1/2 + 2(1-k)` or `-1/2 + 2(-k)`. -/
lemma axStep_axis_form {a : ℝ} {s : Bool} {x : ℝ}
    (hform : ∃ k : ℤ, x = -1 / 2 + 2 * (k : ℝ)) :
    ∃ k' : ℤ, axStep a s x = -1 / 2 + 2 * (k' : ℝ) := by
  obtain ⟨k, hk⟩ := hform
  rw [axStep]
  rcases sgnB_cases s with hs | hs <;> rcases sgnR_cases (x + a / 2) with hr | hr
  · exact ⟨1 - k, by rw [hs, hr, hk]; push_cast; ring⟩
  · exact ⟨-k, by rw [hs, hr, hk]; push_cast; ring⟩
  · exact ⟨-k, by rw [hs, hr, hk]; push_cast; ring⟩
  · exact ⟨1 - k, by rw [hs, hr, hk]; push_cast; ring⟩

/-- Every axis point `-1/2 + 2k` is off the isotropic point `x = -a/2` when `0 < a < 1`:
the equation `4k = 1 - a` has no integer solution with `0 < a < 1`. -/
lemma axis_pt_ne_singular {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℤ) :
    (-1 / 2 + 2 * (k : ℝ)) + a / 2 ≠ 0 := by
  intro hc
  have h4 : (4 : ℝ) * (k : ℝ) = 1 - a := by linarith
  rcases le_or_gt k 0 with hk0 | hk0
  · have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    nlinarith [ha0, ha1, hkr]
  · have hk1 : (1 : ℤ) ≤ k := by omega
    have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith [ha0, ha1, hkr]

/-- The image of `A₁ = (-1/2, 0)` under the composition of the inverse branches of a word `w` is an
axis point `(-1/2 + 2k, 0)` of the walk, and in particular is not the isotropic point
`x = -a/2` (where `invBranch a s` is singular).  (Route: induction on `w` using
`Work.EQ.FanSep.invBranch_axis`, which computes `invBranch a s ((x:ℂ),0) = ((axStep a s x : ℂ),0)`
when `x + a/2 ≠ 0`, and the arithmetic fact that `-1/2 + 2k + a/2 ≠ 0` for `0 < a < 1`.) -/
theorem branchComp_axis {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (w : List Bool) :
    ∃ k : ℤ, Work.EQ.FanTri.branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) =
        (((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ), (0 : ℂ)) ∧
      (-1 / 2 + 2 * (k : ℝ)) + a / 2 ≠ 0 := by
  induction w with
  | nil =>
      exact ⟨0, by simp, axis_pt_ne_singular ha0 ha1 0⟩
  | cons c w ih =>
      obtain ⟨k, hk, hne⟩ := ih
      rw [branchComp_cons, hk, FanSep.invBranch_axis a c hne]
      obtain ⟨k', hk'⟩ := axStep_axis_form (s := c) ⟨k, rfl⟩
      exact ⟨k', by rw [hk'], axis_pt_ne_singular ha0 ha1 k'⟩

end Work.EQ.FanTri
