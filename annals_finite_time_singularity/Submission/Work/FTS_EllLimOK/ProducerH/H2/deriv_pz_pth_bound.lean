import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The two second-order angular derivatives of `D_z Ψ` and `∂_z∂_θΨ` at an interior
point of the open quadrant.**

Since `D_z Ψ = z ∂_zΨ` with `z` a constant of the `θ`-differentiation, the `θ`-second
derivative of the `z`-slice of `D_z Ψ` is `z` times the `θ`-derivative of
`θ ↦ pth (pz Ψ) z θ`, and Clairaut's theorem (`Work.Spaces.pz_pth_comm`) identifies that
with the `θ`-derivative of `θ ↦ pz (pth Ψ) z θ`. -/
lemma deriv_second_DzIter_one {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ := by
  -- The `θ`-derivative of the `z`-slice of `D_z Ψ = z ∂_zΨ` is `z ∂_θ∂_zΨ`.
  have hpt : ∀ θ' : ℝ, deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ'
      = z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ' := by
    intro θ'
    have h1 : (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'')
        = fun θ'' => z * Work.Spaces.pz Ψ z θ'' := by
      funext θ''; rfl
    rw [h1, deriv_const_mul_field]
    rfl
  have hB : (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ')
      =ᶠ[𝓝 θ] (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') :=
    Filter.Eventually.of_forall hpt
  -- Clairaut: `∂_θ∂_zΨ = ∂_z∂_θΨ` on the open quadrant.
  have hC : (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    have hmem : (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩
    have hcd : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ') :=
      (hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    exact (Work.Spaces.pz_pth_comm hcd).symm
  calc deriv (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ') θ
      = deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ := hB.deriv_eq
    _ = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ := by
          rw [deriv_const_mul_field]
    _ = z * deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ := by
          rw [hC.deriv_eq]

theorem deriv_pz_pth_bound {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {A B M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (h : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ') θ| ≤ M) :
    ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ| ≤ M / A := by
  intro z hz θ hθ
  have hzA : A ≤ z := hz.1
  have hzpos : 0 < z := lt_of_lt_of_le hA hzA
  -- The hypothesis controls `z · ∂_θ(∂_z∂_θΨ)`; divide by `z ≥ A`.
  have hh := h z hz θ hθ
  rw [deriv_second_DzIter_one hsm hzpos hθ, abs_mul, abs_of_pos hzpos] at hh
  have h1 : |deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ| ≤ M / z :=
    (le_div_iff₀ hzpos).mpr (by rw [mul_comm]; exact hh)
  have h2 : M / z ≤ M / A := div_le_div_of_nonneg_left hM hA hzA
  linarith

end Work.FTS_EllLimOK.ProducerH.H2
