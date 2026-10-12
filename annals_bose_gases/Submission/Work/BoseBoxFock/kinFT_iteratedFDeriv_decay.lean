import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.NormSymAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Rapid decay of *all* iterated derivatives of the one-body kinetic Fourier transform

`Submission.BoseGases.kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` is Mathlib's
`FourierTransform.fourier u` evaluated at the rescaled frequency `(2π)⁻¹ • p`
(`Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`).  For a smooth compactly supported
`u`, `u` is a Schwartz function (`HasCompactSupport.toSchwartzMap`), its Fourier transform is
again Schwartz (`SchwartzMap.fourierTransformCLM`), and the Schwartz seminorm bound
`SchwartzMap.one_add_le_sup_seminorm_apply` bounds simultaneously the `k`-th iterated derivative
and the polynomial weight `(1 + ‖p‖)^N`.

The passage from `𝓕 u` to `kinFT u = 𝓕 u ∘ ((2π)⁻¹ • ·)` is the only bookkeeping: the chain rule
for the constant rescaling is `iteratedFDeriv_comp_const_smul`, which multiplies the `k`-th
derivative by `((2π)⁻¹)^k`, and the rescaling of the frequency costs the fixed factor
`(1 + ‖p‖) ≤ 2π (1 + ‖(2π)⁻¹ • p‖)`.

The `k = 0` case (no derivative, only decay of `kinFT`) is
`Work.OneBodyKin.kinFT_decay_le`; this module is the version with derivatives, which the
`|z|⁻⁶` kernel-decay estimate of `Work.BoseBoxFock.NormSymAux` needs.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap Real FourierTransform BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem kinFT_iteratedFDeriv_decay {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : ContDiff ℝ (⊤ : ENat) u) (huc : HasCompactSupport u) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ k (fun p => Submission.BoseGases.kinFT u p) p‖ ≤ C / (1 + ‖p‖) ^ N := by
  -- `u` as a Schwartz function, and its Fourier transform (again a Schwartz function)
  set F : 𝓢(E3, ℂ) := huc.toSchwartzMap hu with hFdef
  have hFu : ⇑F = u := rfl
  let G : 𝓢(E3, ℂ) := 𝓕 F
  -- the identification of `kinFT u` with `G` at the rescaled frequency
  have hfun : (fun p : E3 => Submission.BoseGases.kinFT u p)
      = fun p : E3 => G (((2 * π)⁻¹ : ℝ) • p) := by
    funext p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hFu]
    exact congrFun (SchwartzMap.fourier_coe F).symm _
  set S : ℝ :=
    ((Finset.Iic ((N, k) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)) G
    with hSdef
  refine ⟨max ((2 * π) ^ N * ((2 * π)⁻¹) ^ k * (2 ^ N * S)) 0, le_max_right _ _, ?_⟩
  intro p
  -- the frequency rescaling
  have hnorm : ‖((2 * π)⁻¹ : ℝ) • p‖ = ((2 * π)⁻¹ : ℝ) * ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hone : (1 + ‖p‖) ^ N ≤ (2 * π) ^ N * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ N := by
    have h2 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    rw [hnorm, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : (2 * π) * (1 + (2 * π)⁻¹ * ‖p‖) = 2 * π + ‖p‖ := by field_simp
    rw [this]
    linarith
  -- the Schwarz bound for `G`, at derivative order `k` and decay power `N`
  have hsch : (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ N * ‖iteratedFDeriv ℝ k (⇑G) (((2 * π)⁻¹ : ℝ) • p)‖
      ≤ 2 ^ N * S := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := ((N, k) : ℕ × ℕ))
      (k := N) (n := k) le_rfl le_rfl G (((2 * π)⁻¹ : ℝ) • p)
    simpa only [hSdef] using h
  -- assemble: chain rule for the rescaling, then the two bounds above
  have hmain : (1 + ‖p‖) ^ N * ‖iteratedFDeriv ℝ k (fun p : E3 => G (((2 * π)⁻¹ : ℝ) • p)) p‖
      ≤ (2 * π) ^ N * ((2 * π)⁻¹) ^ k * (2 ^ N * S) := by
    rw [iteratedFDeriv_comp_const_smul ((2 * π)⁻¹ : ℝ) (G.smooth (k : ℕ∞))]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) k)]
    have hc : (0 : ℝ) ≤ ((2 * π)⁻¹) ^ k := pow_nonneg (by positivity) k
    have hA : (1 + ‖p‖) ^ N * ‖iteratedFDeriv ℝ k (⇑G) (((2 * π)⁻¹) • p)‖
        ≤ (2 * π) ^ N * ((1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ N
            * ‖iteratedFDeriv ℝ k (⇑G) (((2 * π)⁻¹) • p)‖) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hone (norm_nonneg _)
    calc (1 + ‖p‖) ^ N * (((2 * π)⁻¹) ^ k * ‖iteratedFDeriv ℝ k (⇑G) (((2 * π)⁻¹) • p)‖)
        = ((2 * π)⁻¹) ^ k
            * ((1 + ‖p‖) ^ N * ‖iteratedFDeriv ℝ k (⇑G) (((2 * π)⁻¹) • p)‖) := by ring
      _ ≤ ((2 * π)⁻¹) ^ k * ((2 * π) ^ N * ((1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ N
            * ‖iteratedFDeriv ℝ k (⇑G) (((2 * π)⁻¹) • p)‖)) :=
          mul_le_mul_of_nonneg_left hA hc
      _ ≤ ((2 * π)⁻¹) ^ k * ((2 * π) ^ N * (2 ^ N * S)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsch (by positivity)) hc
      _ = (2 * π) ^ N * ((2 * π)⁻¹) ^ k * (2 ^ N * S) := by ring
  rw [hfun]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ N)]
  exact le_trans (by simpa [mul_comm] using hmain) (le_max_left _ _)

end Work.BoseBoxFock
