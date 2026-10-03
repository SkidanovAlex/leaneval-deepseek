import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.exists_local_inv

/-!
# The norm of the derivative of the perturbed Fatou coordinate

`Work.Repel.norm_deriv_phi_eq`: for `w` in the two small discs `Dsm η`, `Dsm (-η)`, the norm of
`deriv φ_f w` is recovered from the norm of the derivative of `τ₀ ∘ φ_f` by multiplying with
`‖φ_f w‖²`.

This is the chain rule for `τ₀(z) = -1/z`, whose derivative is `1/z²`:
`(τ₀ ∘ φ)'(w) = φ'(w)/(φ w)²`, so on taking norms
`‖(τ₀ ∘ φ)'(w)‖ = ‖φ'(w)‖ / ‖φ w‖²`, and `‖φ' w‖ = ‖(τ₀ ∘ φ)'(w)‖ · ‖φ w‖²`.

The only point needing a hypothesis is `φ_f w ≠ 0` (so that `τ₀` is differentiable at `φ_f w`):
it follows from `φ_star_close`, `‖τ₀ (φ_f w) - w‖ ≤ |η|/40`, together with the elementary bound
`3η/4 ≤ ‖w‖` for `w ∈ Dsm η ∪ Dsm (-η)`, `η > 0`.
-/

namespace Work.Repel

open MandelDim

/-- `τ₀(z) = -1/z` has derivative `1/z²` away from `0`. -/
lemma deriv_tau0 {z : ℂ} (hz : z ≠ 0) : deriv MandelDim.tau0 z = 1 / z ^ 2 := by
  rw [show MandelDim.tau0 = fun z : ℂ => (-1) / z from rfl]
  rw [deriv_const_div (-1) (d := fun z : ℂ => z) differentiableAt_id hz]
  simp

theorem norm_deriv_phi_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ) (hη : 0 < η) {w : ℂ}
    (hw : w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η)) :
    ‖deriv P.φ w‖ = ‖deriv (fun u => MandelDim.tau0 (P.φ u)) w‖ * ‖P.φ w‖ ^ 2 := by
  have hφmem : w ∈ P.Dφ := P.D_sub hw
  have hφd : DifferentiableAt ℂ P.φ w := P.φ_holo.differentiableAt (P.Dφ_open.mem_nhds hφmem)
  -- `φ_f w ≠ 0`, so that `τ₀` is differentiable at `φ_f w`
  have hφw_ne : P.φ w ≠ 0 := by
    intro h
    have hzero : MandelDim.tau0 (P.φ w) = 0 := by simp [MandelDim.tau0, h]
    have hclose := P.φ_star_close w hw
    rw [hzero, zero_sub, norm_neg, abs_of_pos hη] at hclose
    have hnorm := norm_ge_of_mem_Dsm_union hη hw
    linarith
  have hτd : DifferentiableAt ℂ MandelDim.tau0 (P.φ w) := by
    show DifferentiableAt ℂ (fun z : ℂ => -1 / z) (P.φ w)
    fun_prop (disch := assumption)
  -- chain rule
  have hcr : deriv (fun u => MandelDim.tau0 (P.φ u)) w
      = deriv MandelDim.tau0 (P.φ w) * deriv P.φ w := by
    have h := deriv_comp (𝕜 := ℂ) w (h₂ := MandelDim.tau0) (h := P.φ) hτd hφd
    rw [Function.comp_def] at h
    exact h
  rw [hcr, deriv_tau0 hφw_ne, norm_mul, norm_div, norm_one, norm_pow]
  have hC : ‖P.φ w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hφw_ne)
  field_simp

end Work.Repel
