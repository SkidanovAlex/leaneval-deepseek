/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/SliceWrap.lean` — the `E1` commutation, slicewise for families

The scheme's right-hand side is built from the *family* `Jfam ρ ε g` (the mollified slices of a
solution), so the `E1` commutation is used in the slicewise form below: at every fake time `τ`,
`D_z^j D_θ^i` of the mollified slice is the mollification of `D_z^j D_θ^i` of the slice.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The slicewise commutation**: for every fake time `τ`, the mixed derivative `D_z^j D_θ^i` of
the mollified slice is the mollification of the mixed derivative of the slice. -/
theorem mixed_Jfam (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {g : Fam}
    (hsm : ∀ τ : ℝ, ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g τ)) Quad)
    {τ z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (slice (Jfam ρ ε g) τ) z θ
      = Jeps ρ ε (Work.Spaces.mixed j i (slice g τ)) z θ := by
  rw [slice_Jfam]
  exact mixed_Jeps ρ hρ hε (hsm τ) hz hθ j i

/-- **The slicewise weighted bound**: the `E1` `ℋ^k`-bound for the family of mollified slices. -/
theorem HkSq_Jfam_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ g : Fam, ∀ τ : ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g τ)) Quad) →
        Work.Spaces.HkMem α k (slice g τ) →
        Work.Spaces.HkMem α k (slice (Jfam ρ ε g) τ) →
        Work.Spaces.HkSq α k (slice (Jfam ρ ε g) τ)
          ≤ Real.exp (C * ε) * Work.Spaces.HkSq α k (slice g τ) := by
  obtain ⟨C, hCpos, hC⟩ := HkSq_Jeps_le ρ hρ
  refine ⟨C, hCpos, fun α hα k ε hε hε1 g τ hsm hm hm' => ?_⟩
  rw [slice_Jfam]
  exact hC α hα k ε hε hε1 (slice g τ) hsm hm hm'

end Work.FTS.StrongEps
