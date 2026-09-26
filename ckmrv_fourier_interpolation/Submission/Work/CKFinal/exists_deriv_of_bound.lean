import Mathlib
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.CKFinal.mdifferentiable_of_scale_bound
import Submission.Work.CKFinal.exists_deriv_of_cauchy_bound

namespace Work.CKFinal

open UpperHalfPlane Filter Topology
open scoped Manifold

/-- If the `r`-difference quotients of a family `G : ℝ → ℍ → ℂ` of holomorphic functions are
uniformly close when the steps are close (quantitative form of the Cauchy property), then `G · τ`
is differentiable in `r` at `r`, the derivative `D` is holomorphic in `τ`, and the quantitative
bound persists in the limit. -/
lemma exists_deriv_of_bound {G : ℝ → UpperHalfPlane → ℂ}
    (hG : ∀ s : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (G s))
    {r D0 M : ℝ} (hD0 : 0 ≤ D0) (hM : 0 ≤ M)
    (hbd : ∀ (a b : ℝ) (τ : UpperHalfPlane), a ≠ 0 → b ≠ 0 →
      ‖(G (r + a) τ - G r τ) / a - (G (r + b) τ - G r τ) / b‖
        ≤ D0 * (|a| + |b|) * (Work.Kernels.scale τ) ^ M) :
    ∃ D : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, HasDerivAt (fun s : ℝ => G s τ) (D τ) r) ∧
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D ∧
      ∀ (a : ℝ) (τ : UpperHalfPlane), a ≠ 0 →
        ‖(G (r + a) τ - G r τ) / a - D τ‖ ≤ D0 * |a| * (Work.Kernels.scale τ) ^ M := by
  -- A strictly decreasing sequence of nonzero steps tending to `0`.
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hu
  have hu_pos : ∀ n : ℕ, 0 < u n := by intro n; rw [hu]; positivity
  have hu_ne : ∀ n : ℕ, u n ≠ 0 := fun n => ne_of_gt (hu_pos n)
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds 0) := by
    rw [hu]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- The pointwise quantitative Cauchy criterion gives, for each `τ`, a derivative `D τ` and the
  -- quantitative bound.
  have hii : ∀ τ : UpperHalfPlane, ∃ D : ℂ, HasDerivAt (fun s : ℝ => G s τ) D r ∧
      ∀ a : ℝ, a ≠ 0 →
        ‖(G (r + a) τ - G r τ) / a - D‖ ≤ D0 * |a| * (Work.Kernels.scale τ) ^ M := by
    intro τ
    exact exists_deriv_of_cauchy_bound hD0 (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le M)
      (fun a b ha hb => hbd a b τ ha hb)
  choose D hD using hii
  refine ⟨D, fun τ => (hD τ).1, ?_, fun a τ ha => (hD τ).2 a ha⟩
  -- Holomorphy of the limit, via the Weierstrass theorem for the sequence of difference quotients.
  refine mdifferentiable_of_scale_bound (F := fun n τ => (G (r + u n) τ - G r τ) / u n) hM ?_ ?_
  · intro n
    have h1 : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => G (r + u n) τ - G r τ) := (hG (r + u n)).sub (hG r)
    have h2 : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (((u n : ℂ))⁻¹ • (fun τ : UpperHalfPlane => G (r + u n) τ - G r τ)) :=
      h1.const_smul (((u n : ℂ))⁻¹)
    have key : (fun τ : UpperHalfPlane => (G (r + u n) τ - G r τ) / u n)
        = (((u n : ℂ))⁻¹ • (fun τ : UpperHalfPlane => G (r + u n) τ - G r τ)) := by
      funext τ; simp [Pi.smul_apply, div_eq_mul_inv, mul_comm]
    rw [key]; exact h2
  · refine ⟨fun n => D0 * |u n|, ?_, ?_⟩
    · have h1 : Filter.Tendsto (fun n : ℕ => |u n|) Filter.atTop (nhds 0) := by
        simpa using hu_tendsto.abs
      simpa using h1.const_mul D0
    · intro n τ
      exact (hD τ).2 (u n) (hu_ne n)

end Work.CKFinal
