import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.winVec_support_mRange`

The window vector `winVec p ψ m j = prof p (j - m) * ψ j` can only be nonzero if `ψ j ≠ 0`
(so `j ∈ iRange n` when `ψ` is supported there) and `prof p (j - m) ≠ 0`, i.e. `j - m` lies
in the support `[-p,p]` of the triangle profile.  Hence `m = j - (j - m)` is trapped in
`[0 - p, (n-1) + p] = mRange p n`: the finite range of translation parameters used
throughout the Lieb–Solovej localisation.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- The triangle profile vanishes outside `[-p,p]`: `tri p s ≠ 0` forces `|s| ≤ p`. -/
theorem abs_le_of_tri_ne_zero (p : ℕ) {s : ℤ} (h : Work.UBBInputs3.tri p s ≠ 0) :
    |s| ≤ (p : ℤ) := by
  unfold Work.UBBInputs3.tri at h
  have hlt : |(s : ℝ)| < (p : ℝ) + 1 := by
    by_contra hc
    push Not at hc
    rw [max_eq_left (by linarith)] at h
    exact h rfl
  have h1 : -((p : ℝ) + 1) < (s : ℝ) := (abs_lt.mp hlt).1
  have h2 : (s : ℝ) < (p : ℝ) + 1 := (abs_lt.mp hlt).2
  have h1' : ((-(p : ℤ) - 1 : ℤ) : ℝ) < ((s : ℤ) : ℝ) := by push_cast; linarith
  have h2' : ((s : ℤ) : ℝ) < (((p : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h1'' : (-(p : ℤ) - 1 : ℤ) < s := by exact_mod_cast h1'
  have h2'' : s < (p : ℤ) + 1 := by exact_mod_cast h2'
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- The normalised profile has the same support as `tri`: `prof p s ≠ 0` forces
`|s| ≤ p`. -/
theorem abs_le_of_prof_ne_zero (p : ℕ) {s : ℤ} (h : Work.UBBInputs3.prof p s ≠ 0) :
    |s| ≤ (p : ℤ) := by
  refine abs_le_of_tri_ne_zero p ?_
  intro h0
  exact h (by rw [Work.UBBInputs3.prof, h0, zero_div])

/-- **Support of the window vectors in the translation parameter.** If `ψ` is supported in
`iRange n` and `winVec p ψ m` does not vanish at `j`, then the translation parameter `m`
lies in `mRange p n = [-p, n-1+p]`. -/
theorem winVec_support_mRange (n p : ℕ) (ψ : ℤ → ℂ)
    (hψsupp : ∀ j, ψ j ≠ 0 → j ∈ Work.UBBInputs3.iRange n) (m j : ℤ)
    (h : Work.UBBInputs3.winVec p ψ m j ≠ 0) : m ∈ Work.UBBInputs3.mRange p n := by
  have hψ : ψ j ≠ 0 := by
    intro hj; exact h (by rw [Work.UBBInputs3.winVec, hj, mul_zero])
  have hprof : Work.UBBInputs3.prof p (j - m) ≠ 0 := by
    intro hp
    exact h (by rw [Work.UBBInputs3.winVec, hp, Complex.ofReal_zero, zero_mul])
  have habs : |j - m| ≤ (p : ℤ) := abs_le_of_prof_ne_zero p hprof
  have hjmem := hψsupp j hψ
  rw [Work.UBBInputs3.iRange, Finset.mem_Icc] at hjmem
  rw [Work.UBBInputs3.mRange, Finset.mem_Icc]
  obtain ⟨hj0, hjn⟩ := hjmem
  obtain ⟨hA, hB⟩ := abs_le.mp habs
  constructor <;> omega

end Work.UBBInputs3.MatLoc
