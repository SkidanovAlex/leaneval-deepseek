/-
# Joint bound for `z ↦ z (D_z f(z,θ) w(z))²` on `(0,R) × [0,π/2]`

The lemma `box_joint_bound` upgrades a *local* bound on the derivative of
`z ↦ z (D_z f(z,θ) w(z))²` (valid for `z` in some right-neighbourhood `(0,δ)` of the
origin, uniformly in `θ ∈ Iθ`) to a bound on the whole box `(0,R) × Iθ`.

This is a pure compactness statement: away from the origin the function
`(z,θ) ↦ ∂_z (z (D_z f(z,θ) w(z))²)` is smooth (hence continuous) on a neighbourhood
of the compact box `[δ,R] × Iθ` by `contDiffOn_uncurry_pz_BoxG` of
`Submission.Work.Coercivity.BoxAux`, so it is bounded there; below `δ` the assumed
bound applies.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.BoxAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- If `∂_z (z (D_z f(z,θ) w(z))²)` is bounded by `C` on `(0,δ) × Iθ`, then it is
bounded by some `M > 0` on all of `(0,R) × Iθ`. -/
theorem box_joint_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hC : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C)
    {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ M := by
  obtain ⟨C, δ, hCpos, hδpos, hCbd⟩ := hC
  -- `∂_z (z (D_z f · w)²)` is the partial derivative `pz` of `BoxG f`.
  have hpz : ∀ z θ : ℝ, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
      = Spaces.pz (BoxG f) z θ := fun z _ => rfl
  by_cases hRδ : R ≤ δ
  · -- The whole interval `(0,R)` lies in the range of the assumed bound.
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro z hz θ hθ
    rw [hpz]
    exact le_trans (hCbd z ⟨hz.1, lt_of_lt_of_le hz.2 hRδ⟩ θ hθ) (le_max_left _ _)
  · -- Otherwise `δ < R` and the compact box `[δ,R] × Iθ` lies in the smoothness range.
    simp only [not_le] at hRδ
    have hcont : ContinuousOn (Function.uncurry (Spaces.pz (BoxG f)))
        (Set.Icc δ R ×ˢ Spaces.Iθ) := by
      refine (contDiffOn_uncurry_pz_BoxG f hsm).continuousOn.mono ?_
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Spaces.Iθ, Set.mem_Icc] at hθ ⊢
      exact ⟨lt_of_lt_of_le hδpos hz.1, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    obtain ⟨M2, hM2⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
    refine ⟨max (max C M2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro z hz θ hθ
    rw [hpz]
    rcases lt_or_ge z δ with hzlt | hzge
    · have h2 := hCbd z ⟨hz.1, hzlt⟩ θ hθ
      rw [hpz] at h2
      exact le_trans h2 (le_trans (le_max_left C M2) (le_max_left _ _))
    · have h1 := hM2 (z, θ) ⟨⟨hzge, le_of_lt hz.2⟩, hθ⟩
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_trans (le_max_right C M2) (le_max_left _ _))

end Work.Coercivity
