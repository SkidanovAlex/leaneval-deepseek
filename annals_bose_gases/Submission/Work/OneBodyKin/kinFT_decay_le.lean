import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Polynomial decay of the one-body kinetic Fourier transform

`Submission.BoseGases.kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` is Mathlib's Fourier transform
`𝓕 u` evaluated at the rescaled frequency `(2π)⁻¹ • p` (`kinFT_eq_fourier`).  For a smooth
compactly supported `u`, `𝓕 u` is a Schwartz function, hence decays faster than any power
of `‖p‖`: `‖kinFT u p‖ ≤ C / (1 + ‖p‖)^k`.

The Mathlib Schwarz-space machinery does all of the work: `HasCompactSupport.toSchwartzMap`
turns `u` into an element of `𝓢(ℝ³, ℂ)`, `SchwartzMap.fourierTransformCLM` keeps it in `𝓢`,
and `SchwartzMap.one_add_le_sup_seminorm_apply` converts the Schwarz seminorm bound into the
`(1 + ‖x‖)^k` estimate.  The only bookkeeping is the `(2π)⁻¹` rescaling of the frequency,
which is controlled by `(1 + ‖p‖) ≤ 2π (1 + ‖(2π)⁻¹ • p‖)`.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform Real

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Rescaling bookkeeping: `(1 + ‖p‖)^k ≤ (2π)^k (1 + ‖(2π)⁻¹ • p‖)^k`, i.e. the rescaled
frequency `(2π)⁻¹ • p` is smaller than `p` up to the fixed factor `2π`. -/
private lemma one_add_le_two_pi_mul_inv_smul (k : ℕ) (p : ℝ³) :
    (1 + ‖p‖) ^ k ≤ (2 * π) ^ k * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ k := by
  have hnorm : ‖((2 * π)⁻¹ : ℝ) • p‖ = (2 * π)⁻¹ * ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h2 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [hnorm]
  have : (2 * π) * (1 + (2 * π)⁻¹ * ‖p‖) = 2 * π + ‖p‖ := by field_simp
  rw [this]
  linarith

/-- **Polynomial decay of `kinFT`.**  For a smooth compactly supported `u`, the `p`-convention
Fourier transform `kinFT u` decays faster than any power of `‖p‖`. -/
theorem kinFT_decay_le (k : ℕ) {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : ContDiff ℝ (⊤ : ENat) u) (hcs : HasCompactSupport u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.kinFT u p‖ ≤ C / (1 + ‖p‖) ^ k := by
  -- `u` as a Schwartz function, and its Fourier transform (again a Schwartz function)
  set F : 𝓢(ℝ³, ℂ) := hcs.toSchwartzMap hu with hFdef
  have hFu : ⇑F = u := rfl
  set S : ℝ :=
    ((Finset.Iic ((k, 0) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)) (𝓕 F)
    with hSdef
  refine ⟨max ((2 * π) ^ k * 2 ^ k * S) 0, le_max_right _ _, ?_⟩
  intro p
  -- Schwarz bound for `𝓕 F` at the rescaled frequency `(2π)⁻¹ • p`
  have hb : (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ k * ‖(𝓕 F) (((2 * π)⁻¹ : ℝ) • p)‖
      ≤ 2 ^ k * S := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := ((k, 0) : ℕ × ℕ))
      (k := k) (n := 0) le_rfl le_rfl (𝓕 F) (((2 * π)⁻¹ : ℝ) • p)
    simpa only [norm_iteratedFDeriv_zero, hSdef] using this
  -- pass from the rescaled frequency to `p`
  have h1 := one_add_le_two_pi_mul_inv_smul k p
  have hKle : (1 + ‖p‖) ^ k * ‖(𝓕 F) (((2 * π)⁻¹ : ℝ) • p)‖
      ≤ (2 * π) ^ k * 2 ^ k * S := by
    calc (1 + ‖p‖) ^ k * ‖(𝓕 F) (((2 * π)⁻¹ : ℝ) • p)‖
        ≤ ((2 * π) ^ k * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ k) *
            ‖(𝓕 F) (((2 * π)⁻¹ : ℝ) • p)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (2 * π) ^ k *
            ((1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ k *
              ‖(𝓕 F) (((2 * π)⁻¹ : ℝ) • p)‖) := by ring
      _ ≤ (2 * π) ^ k * (2 ^ k * S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (2 * π) ^ k * 2 ^ k * S := by ring
  -- identify `kinFT u p` with the Schwartz Fourier transform
  have hkin : Submission.BoseGases.kinFT u p = (𝓕 F) (((2 * π)⁻¹ : ℝ) • p) := by
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hFu]
    exact congrFun (SchwartzMap.fourier_coe F).symm _
  rw [hkin, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ k)]
  exact le_trans (by simpa [mul_comm] using hKle) (le_max_left _ _)

end Work.OneBodyKin
