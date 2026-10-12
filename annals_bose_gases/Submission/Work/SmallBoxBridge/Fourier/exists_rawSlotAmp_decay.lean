import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxBridge.Defs
import Submission.Work.SmallBoxD1KinDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators FourierTransform
open Submission.BoseGases

namespace Work.SmallBoxBridge.Fourier

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The raw slot amplitude is a Mathlib Fourier transform.**  The corpus's
`rawSlotAmp s p Ψ i x = ∫_z χ_s(z)e^{−i⟪p,z⟫}Ψ(x_{i←z})dz` is the (Mathlib-normalised)
Fourier transform of the windowed substituted fibre `z ↦ χ_s(z)Ψ(x_{i←z})` at the frequency
`(2π)⁻¹p` (the two conventions differ by the `2π`). -/
lemma rawSlotAmp_eq_fourier {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Ψ : (Fin (n + 1) → ℝ³) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ³) (p : ℝ³) :
    Submission.BoseGases.rawSlotAmp s p Ψ i x =
      FourierTransform.fourier (fun z : ℝ³ =>
        ((Submission.BoseGases.chiScale s z * Ψ (Function.update x i z) : ℝ) : ℂ))
      ((2 * π)⁻¹ • p) := by
  set G : ℝ³ → ℂ := fun z => ((chiScale s z * Ψ (Function.update x i z) : ℝ) : ℂ) with hG
  have hsupp : ∀ v, v ∉ acube s → G v = 0 := by
    intro v hv
    have hχ : chiScale s v = 0 := not_ne_iff.mp (fun hh => hv (chiScale_mem_acube hs hh))
    simp only [hG, hχ, zero_mul, Complex.ofReal_zero]
  have hzero : ∀ v ∉ acube s,
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ((2 * π)⁻¹ • p)) * Complex.I) • G v = 0 :=
    fun v hv => by rw [hsupp v hv, smul_zero]
  rw [Real.fourier_eq',
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun v : ℝ³ =>
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ((2 * π)⁻¹ • p)) * Complex.I) • G v) hzero,
    show Submission.BoseGases.rawSlotAmp s p Ψ i x =
        ∫ z in acube s, (chiScale s z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Ψ (Function.update x i z) : ℂ) from rfl]
  refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
  have hin : inner ℝ z ((2 * π)⁻¹ • p) = (2 * π)⁻¹ * inner ℝ p z := by
    rw [real_inner_smul_right, real_inner_comm z p]
  have harg : (↑(-2 * Real.pi * inner ℝ z ((2 * π)⁻¹ • p)) : ℂ) * Complex.I
      = -(Complex.I * ((inner ℝ p z : ℝ) : ℂ)) := by
    have hreal : -2 * Real.pi * inner ℝ z ((2 * π)⁻¹ • p) = -inner ℝ p z := by
      rw [hin]
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hreal]
    push_cast
    ring
  rw [smul_eq_mul, harg, hG]
  push_cast
  ring

theorem exists_rawSlotAmp_decay {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΨ : ContDiff ℝ 3 Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin (n + 1) → EuclideanSpace ℝ (Fin 3)),
      x ∈ Submission.BoseGases.abox (n + 1) s → ∀ (i : Fin (n + 1))
      (p : EuclideanSpace ℝ (Fin 3)),
      ‖Submission.BoseGases.rawSlotAmp s p Ψ i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := exists_modeFourier_decay hs n Ψ hΨ
  refine ⟨C * (2 * π) ^ 3, by positivity, fun x hx i p => ?_⟩
  rw [rawSlotAmp_eq_fourier hs Ψ i x p]
  refine le_trans (hC x hx i ((2 * π)⁻¹ • p)) ?_
  have hle := one_add_norm_inv_smul p
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have h1 : (1 + ‖p‖) ^ 3 ≤ (2 * π) ^ 3 * (1 + ‖(2 * π)⁻¹ • p‖) ^ 3 := by
    have h6 : (2 * π) ^ 3 * ((2 * π)⁻¹ * (1 + ‖p‖)) ^ 3 = (1 + ‖p‖) ^ 3 := by
      rw [← mul_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    rw [← h6]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc C * (1 + ‖p‖) ^ 3 ≤ C * ((2 * π) ^ 3 * (1 + ‖(2 * π)⁻¹ • p‖) ^ 3) :=
        mul_le_mul_of_nonneg_left h1 hC0
    _ = C * (2 * π) ^ 3 * (1 + ‖(2 * π)⁻¹ • p‖) ^ 3 := by ring

end Work.SmallBoxBridge.Fourier
