/-
# The low window `1 ≤ t ≤ 3` of the CKMRV deviation on the cusp-`±1` tiles

The statement `Work.Asymptotics.Tile.tile_dev_low` and its proof; the shared context is in
`Submission/Work/Asymptotics/Tile/tile_dev_aux.lean`, the two window halves in
`tile_Kfun_far.lean` / `tile_Kfun_near.lean`. -/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Gcusp_tile_bound
import Submission.Work.Asymptotics.EtailE.Assembly
import Submission.Work.Asymptotics.AfunFun_S_vadd_eq_zero
import Submission.Work.Asymptotics.Tile.tile_KfunClear_shift_vanish
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Tile.tile_Kfun_far
import Submission.Work.Asymptotics.Tile.tile_Kfun_near

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane
/-- **Polynomial bound for the CKMRV kernel `Kfun` on the cusp-`±1` tiles** (the two-regime
split of the compact/far sides). -/
theorem tile_Kfun_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ, (n = 1 ∨ n = -1) →
        ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t → t ≤ 3 →
          ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
            ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hfar⟩ := tile_Kfun_far ℓ d hd
  obtain ⟨C₂, hC₂, hnear⟩ := tile_Kfun_near ℓ d hd (KfunClear_shift_vanish_all ℓ d hd)
  refine ⟨C₁ + C₂, max N₁ 0, by positivity, le_max_of_le_left hN₁, ?_⟩
  intro w hw n hn t ht h1 h3
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hpow : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ (max N₁ 0) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hpow1 : (1 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₁ 0) :=
    Real.one_le_rpow hs1 (le_max_of_le_left hN₁)
  have hM0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₁ 0) := Real.rpow_nonneg hs0.le _
  by_cases h6 : 6 ≤ (ModularGroup.S • w).im
  · have h := hfar w hw h6 n hn t ht h1 h3
    refine le_trans h ?_
    have h2 := mul_le_mul_of_nonneg_left hpow hC₁.le
    nlinarith [h2, hC₁.le, hC₂.le, hM0, hpow1]
  · have hle : (ModularGroup.S • w).im ≤ 6 := le_of_lt (lt_of_not_ge h6)
    have h := hnear w hw hle n hn t ht h1 h3
    refine le_trans h ?_
    nlinarith [hC₂.le, hC₁.le, hM0, hpow1]

/-- **The CKMRV deviation on the cusp-`±1` tiles in the low window `1 ≤ t ≤ 3`.** -/
theorem tile_dev_low (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ, (n = 1 ∨ n = -1) →
        ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t → t ≤ 3 →
          ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hK⟩ := tile_Kfun_bound ℓ d hd
  obtain ⟨C₂, N₂, hC₂, hN₂, hG⟩ := tile_Gfun_bound ℓ d hd
  refine ⟨C₁ + C₂, max N₁ N₂, by positivity, le_max_of_le_left hN₁, ?_⟩
  intro w hw n hn t ht h1 h3
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hM0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) := Real.rpow_nonneg hs0.le _
  have hp1 : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hp2 : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hk := hK w hw n hn t ht h1 h3
  have hg := hG w hw n hn t ht h1 h3
  have hk' : ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
      ≤ C₁ * (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    le_trans hk (mul_le_mul_of_nonneg_left hp1 hC₁.le)
  have hg' : ‖Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
      ≤ C₂ * (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    le_trans hg (mul_le_mul_of_nonneg_left hp2 hC₂.le)
  calc ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
        + ‖Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ :=
        norm_sub_le _ _
    _ ≤ C₁ * (Work.Kernels.scale w) ^ (max N₁ N₂)
        + C₂ * (Work.Kernels.scale w) ^ (max N₁ N₂) := add_le_add hk' hg'
    _ = (C₁ + C₂) * (Work.Kernels.scale w) ^ (max N₁ N₂) := by ring

end Work.Asymptotics.Tile
