import Mathlib
import Submission.Work.Asymptotics.Tile.tileWinDefs
import Submission.Work.Asymptotics.Tile.tile_dev_low
import Submission.Work.Asymptotics.Tile.halfDevFar8High
import Submission.Work.Asymptotics.Tile.halfDevFar24High
import Submission.Work.Asymptotics.Tile.halfDevFarMinus
import Submission.Work.Asymptotics.Tile.tileFarTools
import Submission.Work.Asymptotics.Compact.gfun_eq

/-!
# The far regime of the below-pole window on the cusp-`±1` tiles

`Work.Asymptotics.Tile.tileWindowFar` is the far regime `1 ≤ t ≤ Im (S • w) - 1` of the tile
deviation `Kaxis (Kfun ℓ d) (n +ᵥ w) t - Aexp (Gcusp ℓ d) (n +ᵥ w) t` (`n = ±1`, `w ∈ E`).

## The proof

The kernel and its cusp model split into the two halves

  `Kaxis (Kfun ℓ d) (n +ᵥ w) t - Aexp (Gcusp ℓ d) (n +ᵥ w) t
      = (h₊ + h₋)/2`,

with `h± = K± - 𝒢±` the two half-deviations (`Work.Kernels.Kfun_eq`,
`Work.Asymptotics.Compact.gfun_eq`, `Aexp_Gcusp_eq_Gfun'`), and the far window
follows from the half-deviation bounds

* `Work.Asymptotics.Tile.halfDevFar8High` / `Work.Asymptotics.Tile.halfDevFar24High` for `h₊` on
  `3 ≤ t`,
* `Work.Asymptotics.Tile.halfDevFarMinus` for `h₋` on `3 ≤ t` (below),

together with `Work.Asymptotics.Tile.tile_dev_low` for `1 ≤ t ≤ 3`.
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-- **The `K_+` far half-deviation on the cusp-`±1` tiles.**  Convenience restatement of the
proved `Work.Asymptotics.Tile.halfDevFar8High` / `Work.Asymptotics.Tile.halfDevFar24High`. -/
theorem halfDevFarPlus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → 3 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  rcases hd with rfl | rfl
  · exact halfDevFar8High
  · exact halfDevFar24High

/-- **The far regime of the below-pole window on the cusp-`±1` tiles** (the requested statement). -/
theorem tileWindowFar (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ,
        (n = 1 ∨ n = -1) → ∀ t : ℝ, 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨Cp, Np, Mp, hCp, hNp, hMp, bP⟩ := halfDevFarPlus ℓ d hd
  obtain ⟨Cm, Nm, Mm, hCm, hNm, hMm, bM⟩ := halfDevFarMinus ℓ d hd
  obtain ⟨Cl, Nl, hCl, hNl, bL⟩ := tile_dev_low ℓ d hd
  refine ⟨(Cp + Cm) / 2 + Cl + 1, max (max Np Nm) Nl, max (max Mp Mm) (max Nl 0),
    ?_, ?_, ?_, ?_⟩
  · linarith [hCp, hCm, hCl]
  · exact le_trans (le_trans hNp (le_max_left Np Nm)) (le_max_left _ _)
  · exact le_trans (le_trans hMp (le_max_left Mp Mm)) (le_max_left _ _)
  · intro w hw n hn t ht1 htle
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
    -- the common exponent conversion
    have hNp' : Np ≤ max (max Np Nm) Nl := le_trans (le_max_left Np Nm) (le_max_left _ _)
    have hNm' : Nm ≤ max (max Np Nm) Nl := le_trans (le_max_right Np Nm) (le_max_left _ _)
    have hNl' : Nl ≤ max (max Np Nm) Nl := le_max_right _ _
    have hMp' : Mp ≤ max (max Mp Mm) (max Nl 0) :=
      le_trans (le_max_left Mp Mm) (le_max_left _ _)
    have hMm' : Mm ≤ max (max Mp Mm) (max Nl 0) :=
      le_trans (le_max_right Mp Mm) (le_max_left _ _)
    have hMl' : (0:ℝ) ≤ max (max Mp Mm) (max Nl 0) :=
      le_trans (by positivity) (le_max_right _ _)
    by_cases h3 : t ≤ 3
    · -- the low window `1 ≤ t ≤ 3`: `tile_dev_low`
      have hAexpL : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
          = Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) :=
        Aexp_Gcusp_eq_Gfun' ℓ d hd ((n : ℝ) +ᵥ w) t ht0
      have hKaxL : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
        rw [Work.Kernels.Kaxis, dif_pos ht0]
      rw [hKaxL, hAexpL]
      refine le_trans (bL w hw n hn t ht0 ht1 h3) ?_
      have hb : (Work.Kernels.scale w) ^ Nl ≤ (Work.Kernels.scale w) ^ (max (max Np Nm) Nl) :=
        Real.rpow_le_rpow_of_exponent_le hs1 hNl'
      have htM : (1:ℝ) ≤ t ^ (max (max Mp Mm) (max Nl 0)) :=
        Real.one_le_rpow ht1 hMl'
      calc Cl * (Work.Kernels.scale w) ^ Nl
          = Cl * (Work.Kernels.scale w) ^ Nl * 1 := by ring
        _ ≤ Cl * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) := by
            refine mul_le_mul ?_ htM (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hb hCl.le
        _ ≤ ((Cp + Cm) / 2 + Cl + 1) * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) := by
            have hcoef : Cl ≤ (Cp + Cm) / 2 + Cl + 1 := by linarith
            have h1 : Cl * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
                ≤ ((Cp + Cm) / 2 + Cl + 1) * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl) :=
              mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hs0.le _)
            calc Cl * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
                  * t ^ (max (max Mp Mm) (max Nl 0))
                = (Cl * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl))
                  * t ^ (max (max Mp Mm) (max Nl 0)) := by ring
              _ ≤ (((Cp + Cm) / 2 + Cl + 1) * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl))
                  * t ^ (max (max Mp Mm) (max Nl 0)) :=
                  mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le _)
              _ = ((Cp + Cm) / 2 + Cl + 1) * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
                  * t ^ (max (max Mp Mm) (max Nl 0)) := by ring
    · -- the far window `3 ≤ t`
      push_neg at h3
      have h3' : (3:ℝ) ≤ t := le_of_lt h3
      -- the decomposition of the deviation into the two halves
      have hAexp : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
          = Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) :=
        Aexp_Gcusp_eq_Gfun' ℓ d hd ((n : ℝ) +ᵥ w) t ht0
      have hGfun : Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
          = (Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
              + Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                  (Work.Kernels.imagAxis t ht0)) / 2 := by
        have h := Work.Asymptotics.Compact.gfun_eq ℓ d hd ((n : ℝ) +ᵥ w)
          (Work.Kernels.imagAxis t ht0)
        rw [eq_div_iff (by norm_num : (2:ℂ) ≠ 0), mul_comm]
        exact h.symm
      have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
        rw [Work.Kernels.Kaxis, dif_pos ht0]
      have hKfun : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
          = (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
              + Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)) / 2 := rfl
      have hsplit : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
          = ((Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0))
              + (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                    (Work.Kernels.imagAxis t ht0))) / 2 := by
        rw [hKax, hAexp, hGfun, hKfun]; ring
      have bP' := bP w n (Work.Kernels.imagAxis t ht0) t hn hw rfl h3' htle
      have bM' := bM w n (Work.Kernels.imagAxis t ht0) t hn hw rfl h3' htle
      have bP'' : ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
            - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖
          ≤ Cp * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) := by
        refine le_trans bP' ?_
        have h1 : (Work.Kernels.scale w) ^ Np ≤ (Work.Kernels.scale w) ^ (max (max Np Nm) Nl) :=
          Real.rpow_le_rpow_of_exponent_le hs1 hNp'
        have h2 : t ^ Mp ≤ t ^ (max (max Mp Mm) (max Nl 0)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 hMp'
        have h3n : (0:ℝ) ≤ Cp := hCp.le
        calc Cp * (Work.Kernels.scale w) ^ Np * t ^ Mp
            = Cp * ((Work.Kernels.scale w) ^ Np * t ^ Mp) := by ring
          _ ≤ Cp * ((Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
                * t ^ (max (max Mp Mm) (max Nl 0))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)) h3n
          _ = Cp * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
                * t ^ (max (max Mp Mm) (max Nl 0)) := by ring
      have bM'' : ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
            - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖
          ≤ Cm * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) := by
        refine le_trans bM' ?_
        have h1 : (Work.Kernels.scale w) ^ Nm ≤ (Work.Kernels.scale w) ^ (max (max Np Nm) Nl) :=
          Real.rpow_le_rpow_of_exponent_le hs1 hNm'
        have h2 : t ^ Mm ≤ t ^ (max (max Mp Mm) (max Nl 0)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 hMm'
        have h3n : (0:ℝ) ≤ Cm := hCm.le
        calc Cm * (Work.Kernels.scale w) ^ Nm * t ^ Mm
            = Cm * ((Work.Kernels.scale w) ^ Nm * t ^ Mm) := by ring
          _ ≤ Cm * ((Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
                * t ^ (max (max Mp Mm) (max Nl 0))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)) h3n
          _ = Cm * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
                * t ^ (max (max Mp Mm) (max Nl 0)) := by ring
      rw [hsplit, norm_div, show ‖(2:ℂ)‖ = 2 from by norm_num]
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have hsum := add_le_add bP'' bM''
      have hcoef : Cp + Cm ≤ ((Cp + Cm) / 2 + Cl + 1) * 2 := by linarith
      have hS0 : (0:ℝ) ≤ (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
            * t ^ (max (max Mp Mm) (max Nl 0)) :=
        mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg ht0.le _)
      calc ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
              - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
            + (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                  (Work.Kernels.imagAxis t ht0))‖
          ≤ ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
              - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖
            + ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                  (Work.Kernels.imagAxis t ht0)‖ := norm_add_le _ _
        _ ≤ Cp * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0))
            + Cm * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) := hsum
        _ = (Cp + Cm) * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) := by ring
        _ ≤ (((Cp + Cm) / 2 + Cl + 1) * 2) * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht0.le _)
            exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hs0.le _)
        _ = ((Cp + Cm) / 2 + Cl + 1) * (Work.Kernels.scale w) ^ (max (max Np Nm) Nl)
              * t ^ (max (max Mp Mm) (max Nl 0)) * 2 := by ring

end

end Work.Asymptotics.Tile
