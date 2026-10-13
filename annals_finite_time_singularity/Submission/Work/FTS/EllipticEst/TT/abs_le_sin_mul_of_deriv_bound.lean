/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise angular bound `|u θ| ≤ (π/4) sin (2θ) M`

For a `θ`-slice `u` that is smooth on a neighbourhood of `Iθ = [0, π/2]`, vanishes at both
endpoints and has `|u'| ≤ M` on `Iθ`, one has

  `|u θ| ≤ (π/4) · sin (2θ) · M`   for all `θ ∈ Iθ`.

The proof is the mean value theorem in the two endpoints directions:
`|u θ| ≤ M · min θ (π/2 - θ)`, together with the elementary sharp bound
`min θ (π/2 - θ) ≤ (π/4) sin (2θ)`, which follows from concavity of `sin`
(`sin x ≥ (2/π) x` on `[0, π/2]`) applied at `x = 2 min θ (π/2 - θ)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The elementary sine bound -/

/-- `s ≤ (π/4) sin (2s)` for `2s ∈ [0, π/2]`, from `sin x ≥ (2/π) x`. -/
private lemma self_le_quarter_pi_sin {s : ℝ} (hs0 : 0 ≤ s) (hs2 : 2 * s ≤ Real.pi / 2) :
    s ≤ (Real.pi / 4) * Real.sin (2 * s) := by
  have hsin : 2 / Real.pi * (2 * s) ≤ Real.sin (2 * s) :=
    Real.mul_le_sin (by linarith) hs2
  have hcoef : (Real.pi / 4) * (2 / Real.pi * (2 * s)) = s := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  calc s = (Real.pi / 4) * (2 / Real.pi * (2 * s)) := hcoef.symm
    _ ≤ (Real.pi / 4) * Real.sin (2 * s) :=
        mul_le_mul_of_nonneg_left hsin (by positivity)

/-- On `Iθ = [0, π/2]` the distance to the nearest endpoint is at most
`(π/4) sin (2θ)`.  The bound is sharp at `θ = π/4`. -/
private lemma min_le_quarter_pi_sin {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hsin : Real.sin (2 * min θ (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
    rcases le_total θ (Real.pi / 2 - θ) with hle | hle
    · rw [min_eq_left hle]
    · rw [min_eq_right hle]
      have heq : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
      rw [heq, Real.sin_pi_sub]
  have hs0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ0 (by linarith)
  have hs2 : 2 * min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 := by
    have h1 : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
    have h2 : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    linarith
  calc min θ (Real.pi / 2 - θ)
      ≤ (Real.pi / 4) * Real.sin (2 * min θ (Real.pi / 2 - θ)) :=
        self_le_quarter_pi_sin hs0 hs2
    _ = (Real.pi / 4) * Real.sin (2 * θ) := by rw [hsin]

/-! ## The mean value bound -/

/-- The two mean value theorem bounds in the two endpoint directions, combined with `min`:
`|u θ| ≤ M · min θ (π/2 - θ)` for `θ ∈ Iθ`. -/
private lemma abs_le_mul_min {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u)
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0) {M : ℝ}
    (hM : ∀ θ ∈ Work.Spaces.Iθ, |deriv u θ| ≤ M) :
    ∀ θ ∈ Work.Spaces.Iθ, |u θ| ≤ M * min θ (Real.pi / 2 - θ) := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hdiff : DifferentiableOn ℝ u (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hu.differentiableOn (by simp)
  have hdAt : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ u x := fun x hx =>
    hdiff.differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ‖deriv u x‖ ≤ M := fun x hx => by
    rw [Real.norm_eq_abs]
    exact hM x (by rw [Work.Spaces.Iθ]; exact hx)
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) (Real.pi / 2)) := convex_Icc _ _
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hhalf : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by positivity, le_rfl⟩
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hmemθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hleft : |u θ| ≤ M * θ := by
    have h : ‖u θ - u 0‖ ≤ M * ‖θ - 0‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le hdAt hbound hconv hzero hmemθ
    simpa [h0, Real.norm_eq_abs, abs_of_nonneg hθ0] using h
  have hright : |u θ| ≤ M * (Real.pi / 2 - θ) := by
    have h : ‖u (Real.pi / 2) - u θ‖ ≤ M * ‖Real.pi / 2 - θ‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le hdAt hbound hconv hmemθ hhalf
    simpa [h1, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ1)] using h
  rcases le_total θ (Real.pi / 2 - θ) with hle | hle
  · rw [min_eq_left hle]
    exact hleft
  · rw [min_eq_right hle]
    exact hright

/-! ## The target bound -/

theorem abs_le_sin_mul_of_deriv_bound {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u)
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ θ ∈ Work.Spaces.Iθ, |deriv u θ| ≤ M) :
    ∀ θ ∈ Work.Spaces.Iθ, |u θ| ≤ (Real.pi / 4) * Real.sin (2 * θ) * M := by
  intro θ hθ
  calc |u θ| ≤ M * min θ (Real.pi / 2 - θ) := abs_le_mul_min hu h0 h1 hM θ hθ
    _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) :=
        mul_le_mul_of_nonneg_left (min_le_quarter_pi_sin hθ) hM0
    _ = (Real.pi / 4) * Real.sin (2 * θ) * M := by ring

end Work.FTS.EllipticEst.TT
