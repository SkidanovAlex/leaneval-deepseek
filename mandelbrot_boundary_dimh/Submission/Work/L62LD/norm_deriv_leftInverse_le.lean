import Mathlib

open scoped Topology

namespace Work.L62LD

theorem norm_deriv_leftInverse_le {F Ψ : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hF : DifferentiableOn ℂ F U) (hΨd : DifferentiableOn ℂ Ψ V)
    (hΨU : ∀ u ∈ V, Ψ u ∈ U) (hΨinv : ∀ u ∈ V, F (Ψ u) = u)
    {C : ℝ} (hC : 1 ≤ C) (hratio : ∀ w ∈ U, C⁻¹ ≤ ‖deriv F w‖) :
    ∀ u ∈ V, ‖deriv Ψ u‖ ≤ C := by
  intro u hu
  have hFu : Ψ u ∈ U := hΨU u hu
  have hF' : DifferentiableAt ℂ F (Ψ u) := hF.differentiableAt (hU.mem_nhds hFu)
  have hΨ' : DifferentiableAt ℂ Ψ u := hΨd.differentiableAt (hV.mem_nhds hu)
  have hchain : deriv (F ∘ Ψ) u = deriv F (Ψ u) * deriv Ψ u := deriv_comp u hF' hΨ'
  have heq : (F ∘ Ψ) =ᶠ[𝓝 u] id := by
    filter_upwards [hV.mem_nhds hu] with w hw
    exact hΨinv w hw
  have hder : deriv F (Ψ u) * deriv Ψ u = 1 := by
    rw [← hchain, heq.deriv_eq, deriv_id]
  have hnorm : ‖deriv F (Ψ u)‖ * ‖deriv Ψ u‖ = 1 := by
    rw [← norm_mul, hder, norm_one]
  have hnorm' : ‖deriv Ψ u‖ * ‖deriv F (Ψ u)‖ = 1 := by rw [mul_comm, hnorm]
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hle : ‖deriv Ψ u‖ * C⁻¹ ≤ 1 := by
    rw [← hnorm']
    exact mul_le_mul_of_nonneg_left (hratio (Ψ u) hFu) (norm_nonneg (deriv Ψ u))
  calc ‖deriv Ψ u‖ = (‖deriv Ψ u‖ * C⁻¹) * C := by
        rw [mul_assoc, inv_mul_cancel₀ hCne, mul_one]
    _ ≤ 1 * C := mul_le_mul_of_nonneg_right hle hCpos.le
    _ = C := one_mul C

end Work.L62LD
