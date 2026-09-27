import Mathlib
import Submission.Work.Whitney.BumpModel.Defs
import Submission.Work.Whitney.BumpModel.uhat_fderiv

namespace Work.Whitney.BumpModel

open scoped Manifold ContDiff
open Set Filter Topology

noncomputable section

/-- The derivative of `û = χ/(1 + ∑xᵢ²)` at `±e₀`, with the (correct, `C^∞`) smoothness hypothesis `ContDiff ℝ (⊤ : ℕ∞)`; this is `uhat_fderiv` with its analyticity hypothesis `ContDiff ℝ ⊤` replaced by smoothness. -/
theorem uhat_fderiv_infty (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ x, ‖x‖ ≤ 2 → χ x = 1) (v : Fin n → ℝ) :
    (fderiv ℝ (Work.Whitney.uhat n χ) (Work.Whitney.e0 n)) v = -(1 / 2) * v 0 ∧
      (fderiv ℝ (Work.Whitney.uhat n χ) (-(Work.Whitney.e0 n))) v = (1 / 2) * v 0 := by
  -- The proof only uses that `χ = 1` on a neighbourhood of `±e₀`; smoothness is irrelevant.
  constructor
  · have hlt : ∀ᶠ x in 𝓝 (Work.Whitney.e0 n), ‖x‖ < 2 := by
      have hcont : Tendsto (fun x : Fin n → ℝ => ‖x‖) (𝓝 (Work.Whitney.e0 n))
          (𝓝 ‖Work.Whitney.e0 n‖) := continuous_norm.continuousAt
      exact hcont.eventually (Iio_mem_nhds (by rw [Work.Whitney.norm_e0]; norm_num))
    have hfχ : χ =ᶠ[𝓝 (Work.Whitney.e0 n)] (fun _ => (1 : ℝ)) :=
      hlt.mono (fun x hx => hχ1 x (le_of_lt hx))
    have hu : Work.Whitney.uhat n χ =ᶠ[𝓝 (Work.Whitney.e0 n)]
        (fun y : Fin n → ℝ => (Work.Whitney.bumpU n y)⁻¹) :=
      hfχ.mono (fun y hy => by simp [Work.Whitney.uhat, hy])
    rw [hu.fderiv_eq, fderiv_inv_bumpU_apply n (Work.Whitney.e0 n) v, bumpU_e0 n,
      sum_e0 n v]
    norm_num
    ring
  · have hlt : ∀ᶠ x in 𝓝 (-(Work.Whitney.e0 n)), ‖x‖ < 2 := by
      have hcont : Tendsto (fun x : Fin n → ℝ => ‖x‖) (𝓝 (-(Work.Whitney.e0 n)))
          (𝓝 ‖-(Work.Whitney.e0 n)‖) := continuous_norm.continuousAt
      exact hcont.eventually
        (Iio_mem_nhds (by rw [norm_neg, Work.Whitney.norm_e0]; norm_num))
    have hfχ : χ =ᶠ[𝓝 (-(Work.Whitney.e0 n))] (fun _ => (1 : ℝ)) :=
      hlt.mono (fun x hx => hχ1 x (le_of_lt hx))
    have hu : Work.Whitney.uhat n χ =ᶠ[𝓝 (-(Work.Whitney.e0 n))]
        (fun y : Fin n → ℝ => (Work.Whitney.bumpU n y)⁻¹) :=
      hfχ.mono (fun y hy => by simp [Work.Whitney.uhat, hy])
    rw [hu.fderiv_eq, fderiv_inv_bumpU_apply n (-(Work.Whitney.e0 n)) v, bumpU_neg_e0 n,
      sum_neg_e0 n v]
    norm_num
    ring

end

end Work.Whitney.BumpModel
