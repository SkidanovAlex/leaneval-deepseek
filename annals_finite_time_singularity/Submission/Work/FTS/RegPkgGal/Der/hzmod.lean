import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.R1
import Submission.Work.FTS.RegPkgGal.R1b.extG_cont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

theorem hzmod {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤ M
        ∧ |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M) :
    ∃ Lz : ℝ, 0 ≤ Lz ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
          ≤ Lz * |z - z'| ^ α := by
  obtain ⟨M, hM0, hM⟩ := hsup
  -- The uniform bound `M` on `g̃` and on `∂_zg̃` makes every `z`-slice Lipschitz with constant `M`;
  -- a Lipschitz function is `α`-Hölder for every `0 < α ≤ 1` (with constant `2M`).
  refine ⟨2 * M, by linarith, ?_⟩
  intro τ hτ z z' hz hz' θ hθ
  have hτmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- The `z`-slice of the joint `C¹` function `(z,τ) ↦ g̃ z θ τ` is `C¹` on `Ioi (-1)`.
  have hmaps : Set.MapsTo (fun x : ℝ => (x, τ)) (Set.Ioi (-1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) := fun x hx => ⟨hx, hτmem⟩
  have hf : ContDiffOn ℝ 1 (fun x : ℝ => (x, τ)) (Set.Ioi (-1)) := by fun_prop
  have hslice : ContDiffOn ℝ 1 (fun x : ℝ => Work.FTS.RegPkgGal.extG g x θ τ)
      (Set.Ioi (-1)) := (hcont θ hθ).comp hf hmaps
  have hdiff : ∀ x ∈ Set.Icc 0 (max z z'),
      DifferentiableAt ℝ (fun x : ℝ => Work.FTS.RegPkgGal.extG g x θ τ) x := by
    intro x hx
    refine (hslice.differentiableOn (by norm_num)).differentiableAt ?_
    exact IsOpen.mem_nhds isOpen_Ioi (by simp only [Set.mem_Ioi]; linarith [hx.1])
  have hbnd : ∀ x ∈ Set.Icc 0 (max z z'),
      ‖deriv (fun x : ℝ => Work.FTS.RegPkgGal.extG g x θ τ) x‖ ≤ M := by
    intro x hx
    have hx' := (hM τ hτ x θ hx.1 hθ).2
    rw [Real.norm_eq_abs]
    simpa only [Work.Spaces.pz] using hx'
  have hzmem : z ∈ Set.Icc 0 (max z z') := ⟨hz, le_max_left _ _⟩
  have hz'mem : z' ∈ Set.Icc 0 (max z z') := ⟨hz', le_max_right _ _⟩
  -- Mean value theorem on the segment `[0, max z z']`.
  have hmvt : |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
      ≤ M * |z - z'| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd (convex_Icc 0 (max z z'))
      hz'mem hzmem
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h
  have hd : 0 ≤ |z - z'| := abs_nonneg _
  rcases le_or_gt |z - z'| 1 with hle | hlt
  · -- `|z - z'| ≤ 1`: use `|z - z'| ≤ |z - z'| ^ α` and the Lipschitz bound.
    have hdα : |z - z'| ≤ |z - z'| ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge' hd hle hα.le hα1
      simpa using this
    calc |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
        ≤ M * |z - z'| := hmvt
      _ ≤ M * |z - z'| ^ α := by gcongr
      _ ≤ 2 * M * |z - z'| ^ α := by nlinarith [Real.rpow_nonneg hd α, hM0]
  · -- `1 < |z - z'|`: use the two sup bounds and `1 ≤ |z - z'| ^ α`.
    have h1 : (1 : ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow hlt.le hα.le
    have hupper : |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
        ≤ 2 * M := by
      have hz1 := (hM τ hτ z θ hz hθ).1
      have hz2 := (hM τ hτ z' θ hz' hθ).1
      have := abs_sub (Work.FTS.RegPkgGal.extG g z θ τ) (Work.FTS.RegPkgGal.extG g z' θ τ)
      linarith
    calc |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
        ≤ 2 * M := hupper
      _ ≤ 2 * M * |z - z'| ^ α :=
          le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ 2 * M) h1

end Work.FTS.RegPkgGal.Der
