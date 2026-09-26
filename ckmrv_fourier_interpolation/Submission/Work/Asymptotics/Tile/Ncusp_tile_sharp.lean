import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.mdiff_eta

/-!
# The Schwarz upgrade of the crude tile bound for `Ncusp`

This file contains the Schwarz-lemma step of the tile analysis: a *crude* bound
`‖Ncusp ℓ d τ z‖ ≤ C (scale w)^N e^{c Im (S • w)} e^{π Im z}` for the cusp-`±1` tiles
`τ = n +ᵥ w` (`n = ±1`, `w ∈ E`) upgrades to the *sharp* bound with `e^{-π Im z}`, the
constant in front keeping the same shape `C (scale w)^N e^{c Im (S • w)}`.

The proof is the same as that of `Work.Asymptotics.slash_bound_of_crude_E`, which does the
analogous step on `EReg`: the function `z ↦ Ecusp z · Ncusp ℓ d τ z` is `1`-periodic
(`Ecusp_vadd_one`, `Ncusp_vadd_one`), holomorphic (`mdiff_eta`) and vanishes at the cusp
(`KMinusCuspBallLimit`), so `periodic_zero_cusp_decay_uhp` applies.  None of these inputs
depends on the region in `τ`; only the crude bound does, and it is carried through verbatim.
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold

noncomputable section

theorem Ncusp_tile_sharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hcrude : ∃ c C N : ℝ, 0 ≤ c ∧ c < 2 * Real.pi ∧ 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ z : UpperHalfPlane, 1 ≤ z.im →
          ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
                * Real.exp (Real.pi * z.im)) :
    ∃ c C N : ℝ, 0 ≤ c ∧ c < 2 * Real.pi ∧ 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ z : UpperHalfPlane, 1 ≤ z.im →
          ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
                * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨c, C, N, hc0, hc2, hC, hN, hb⟩ := hcrude
  have hCpos : 0 < C * Real.exp (2 * Real.pi) + 1 := by
    have h := Real.exp_pos (2 * Real.pi)
    nlinarith [h, hC]
  refine ⟨c, C * Real.exp (2 * Real.pi) + 1, N, hc0, hc2, hCpos, hN,
    fun w n hn hw z hz => ?_⟩
  set B : ℝ := C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (mul_nonneg hC.le
      (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N)) (Real.exp_nonneg _)
  have hE1 : Real.exp (-(Real.pi * z.im)) * Real.exp (Real.pi * z.im) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hBbound : ∀ ζ : UpperHalfPlane, 1 ≤ ζ.im →
      ‖Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ‖ ≤ B := by
    intro ζ hζ
    rw [norm_mul, Work.Asymptotics.norm_Ecusp, hB]
    have h := hb w n hn hw ζ hζ
    have he1 : Real.exp (-(Real.pi * ζ.im)) * Real.exp (Real.pi * ζ.im) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-(Real.pi * ζ.im)) * ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ‖
        ≤ Real.exp (-(Real.pi * ζ.im))
            * (C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
                * Real.exp (Real.pi * ζ.im)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
      _ = C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
            * (Real.exp (-(Real.pi * ζ.im)) * Real.exp (Real.pi * ζ.im)) := by ring
      _ = C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) := by
          rw [he1, mul_one]
  have hper : ∀ ζ : UpperHalfPlane,
      (fun ζ : UpperHalfPlane =>
          Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ)
        ((1 : ℝ) +ᵥ ζ)
      = (fun ζ : UpperHalfPlane =>
          Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ) ζ := by
    intro ζ
    simp only [Work.Asymptotics.Ecusp_vadd_one, Work.Asymptotics.Ncusp_vadd_one]
    ring
  have hmd : MDiff (fun ζ : UpperHalfPlane =>
      Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ) :=
    (UpperHalfPlane.mdifferentiable_iff).mpr (Work.Asymptotics.mdiff_eta ℓ d ((n : ℝ) +ᵥ w))
  have hsh := Work.Asymptotics.periodic_zero_cusp_decay_uhp (f := fun ζ : UpperHalfPlane =>
      Work.Asymptotics.Ecusp ζ * Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) ζ)
    hB0 hper hmd hBbound (Work.Asymptotics.KMinusCuspBallLimit ℓ d hd ((n : ℝ) +ᵥ w)) z hz
  rw [norm_mul, Work.Asymptotics.norm_Ecusp] at hsh
  have hNc : ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
      ≤ Real.exp (Real.pi * z.im)
        * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im))) := by
    calc ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
        = Real.exp (Real.pi * z.im)
            * (Real.exp (-(Real.pi * z.im)) * ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (Real.pi * z.im)
            * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im))) :=
          mul_le_mul_of_nonneg_left hsh (Real.exp_nonneg _)
  have hexp : Real.exp (Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im))
      = Real.exp (-(Real.pi * z.im)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey : Real.exp (Real.pi * z.im)
        * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im)))
      = (C * Real.exp (2 * Real.pi) * (Work.Kernels.scale w) ^ N
          * Real.exp (c * (ModularGroup.S • w).im)) * Real.exp (-(Real.pi * z.im)) := by
    rw [hB, show Real.exp (Real.pi * z.im)
          * ((C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im))
              * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im)))
        = (C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im))
          * (Real.exp (Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im)))
          * Real.exp (2 * Real.pi) from by ring,
      hexp]
    ring
  have hmono : (C * Real.exp (2 * Real.pi) * (Work.Kernels.scale w) ^ N
        * Real.exp (c * (ModularGroup.S • w).im)) * Real.exp (-(Real.pi * z.im))
      ≤ ((C * Real.exp (2 * Real.pi) + 1) * (Work.Kernels.scale w) ^ N
          * Real.exp (c * (ModularGroup.S • w).im)) * Real.exp (-(Real.pi * z.im)) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    have h2 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) :=
      mul_nonneg (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N) (Real.exp_nonneg _)
    nlinarith [h2, Real.exp_pos (2 * Real.pi), hC.le]
  exact le_trans hNc (le_trans (le_of_eq hkey) hmono)

end

end Work.Asymptotics.Tile
