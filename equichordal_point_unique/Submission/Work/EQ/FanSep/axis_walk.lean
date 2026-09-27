import Mathlib
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.fan_base

namespace Work.EQ.FanSep

open Work.EQ

/-- **The backward branch on the real axis.** For a real axis point `Q = (x, 0)` off the
isotropic point `x = -a/2`, the principal square root `((x + a/2)^2)^{1/2}` is the modulus
`|x + a/2|`, so the branch `invBranch a s` acts as the real "axis walk"
`x ↦ -x + (sgnB s)·(sgnR (x + a/2)) = axStep a s x` and stays on the axis. -/
theorem invBranch_axis (a : ℝ) (s : Bool) {x : ℝ} (hx : x + a / 2 ≠ 0) :
    invBranch a s ((x : ℂ), 0) = (((axStep a s x : ℝ) : ℂ), 0) := by
  have hcp : (((x : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ)
      = ((|x + a / 2| : ℝ) : ℂ) := by
    have hz : ((x : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2
        = (((x + a / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hz, ofReal_cpow_half (by positivity), Real.sqrt_sq_eq_abs]
  have hcxe : ((x : ℂ) + ((a / 2 : ℝ) : ℂ)) = ((x + a / 2 : ℝ) : ℂ) := by push_cast; ring
  have hdiv : ((x : ℂ) + ((a / 2 : ℝ) : ℂ)) / ((|x + a / 2| : ℝ) : ℂ)
      = ((sgnR (x + a / 2) : ℝ) : ℂ) := by
    rw [hcxe, ← Complex.ofReal_div, div_abs_self hx]
  have hif : (if s then (1 : ℂ) else -1) = ((sgnB s : ℝ) : ℂ) := by
    cases s <;> simp [sgnB]
  simp only [invBranch, hcp]
  have hmul : (if s then (1 : ℂ) else -1) * ((x : ℂ) + ((a / 2 : ℝ) : ℂ))
      / ((|x + a / 2| : ℝ) : ℂ) = ((sgnB s * sgnR (x + a / 2) : ℝ) : ℂ) := by
    rw [hif, mul_div_assoc, hdiv, ← Complex.ofReal_mul]
  rw [hmul]
  refine Prod.ext ?_ ?_
  · rw [axStep]; push_cast; ring
  · simp

theorem axis_walk {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    (∀ (s : Bool) {x : ℝ}, x + a / 2 ≠ 0 →
        invBranch a s ((x : ℂ), 0) = (((axStep a s x : ℝ) : ℂ), 0)) ∧
      ∀ ε : List Bool, (fan a h ε 0).2 = 0 ∧ ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k := by
  refine ⟨fun s x hx => invBranch_axis a s hx, ?_⟩
  intro ε
  induction ε with
  | nil =>
      rw [fan, germC_value ha0 ha1 hh]
      exact ⟨rfl, ⟨0, by norm_num⟩⟩
  | cons s ε ih =>
      obtain ⟨h2, k, hk⟩ := ih
      -- the inductive centre is the axis point `x = -1/2 + 2k`
      set x : ℝ := -1 / 2 + 2 * (k : ℝ) with hxdef
      have hxc : (x : ℂ) = -1 / 2 + 2 * (k : ℂ) := by rw [hxdef]; push_cast; ring
      have hcentre : fan a h ε 0 = ((x : ℂ), 0) := by
        refine Prod.ext ?_ ?_
        · rw [hxc]; exact hk
        · exact h2
      -- `x + a/2 ≠ 0` because `4k + (a-1) = 0` has no integer solution for `0 < a < 1`
      have hxne : x + a / 2 ≠ 0 := by
        rw [hxdef] at *
        intro hc
        have h4 : (4 : ℝ) * (k : ℝ) = 1 - a := by linarith
        rcases le_or_gt k 0 with hk0 | hk0
        · have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
          nlinarith [ha0, ha1, hkr]
        · have hk1 : (1 : ℤ) ≤ k := by omega
          have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
          nlinarith [ha0, ha1, hkr]
      have hstep : fan a h (s :: ε) 0 = invBranch a s (fan a h ε 0) := by
        simp [fan]
      rw [hstep, hcentre, invBranch_axis a s hxne]
      refine ⟨rfl, ?_⟩
      -- the axis walk `-x + (sgnB s)(sgnR (x + a/2))` again lies in `-1/2 + 2ℤ`
      rcases sgnB_cases s with hsb | hsb <;> rcases sgnR_cases (x + a / 2) with hsr | hsr
      · refine ⟨1 - k, ?_⟩
        rw [axStep, hsb, hsr, hxdef]; push_cast; ring
      · refine ⟨-k, ?_⟩
        rw [axStep, hsb, hsr, hxdef]; push_cast; ring
      · refine ⟨-k, ?_⟩
        rw [axStep, hsb, hsr, hxdef]; push_cast; ring
      · refine ⟨1 - k, ?_⟩
        rw [axStep, hsb, hsr, hxdef]; push_cast; ring

end Work.EQ.FanSep
