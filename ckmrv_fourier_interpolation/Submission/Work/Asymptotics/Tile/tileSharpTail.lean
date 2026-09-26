/-
# The sharp cusp-`i∞` tail on the cusp-`±1` tiles

For `w ∈ E = KEpsilon`, `n = ±1` and `t ≥ 2 Im (S • w) + 1` the CKMRV kernel `K^{(d)}` differs
from its cusp-`i∞` model `Aexp (Gcusp ℓ d)` by `O((scale w)^N t^M e^{-π (t - Im (S • w))})`:
the rate is measured *from the pole height* `Im (S • w)`.

## Structure of the proof

`Kaxis (Kfun ℓ d) = (K_+ + K_-)/2` and `Aexp (Gcusp ℓ d) = (𝒢_+ + 𝒢_-)/2`, so the target is the
average of the two halves

* `Work.Asymptotics.Tile.KMinusTileTail` — the `K_-` half;
* `Work.Asymptotics.Tile.KPlusTileTail`  — the `K_+` half,

each of which is stated in the shape `Work.Asymptotics.Tile.TB Real.pi 1` of
`Submission/Work/Asymptotics/Tile/tileTB.lean` (which also provides the `τ`-atom calculus on the
tiles and the extraction `TB.to_target` of the target shape).
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.KMinusTileTail
import Submission.Work.Asymptotics.Tile.KPlusTileTail
import Submission.Work.Asymptotics.EtailE.Assembly
import Submission.Work.Asymptotics.Compact.gfun_eq

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels Work.Asymptotics

noncomputable section

/-- **Assembly**: the target `tileSharpTail` from its two halves. -/
theorem tileSharpTail_of_halves (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hKm : TB Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z))
    (hKp : TB Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) z)) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hKm.to_target
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hKp.to_target
  refine ⟨(C1 + C2) / 2, max N1 N2, max M1 M2, by positivity, le_max_of_le_left hN1,
    le_max_of_le_left hM1, ?_⟩
  intro w n hn hw t ht
  have ht0 : (0:ℝ) < t := by linarith [hw.2]
  have hs1 : (1:ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have ht1 : (1:ℝ) ≤ t := by linarith [hw.2]
  have hsN1 : (Work.Kernels.scale w) ^ N1 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hsN2 : (Work.Kernels.scale w) ^ N2 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have htM1 : t ^ M1 ≤ t ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  have htM2 : t ^ M2 ≤ t ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right _ _)
  have b1 := h1 w n hn hw t ht0 ht
  have b2 := h2 w n hn hw t ht0 ht
  -- identifications
  have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
    rw [Work.Kernels.Kaxis, dif_pos ht0]
  have hAex : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
    rw [Gcusp_eq_Gcoef ℓ d hd, Aexp_Gcoef' ℓ d ((n : ℝ) +ᵥ w) t ht0]
  have hGfun : Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
      = (Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
          + Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
              (Work.Kernels.imagAxis t ht0)) / 2 := by
    have h := Work.Asymptotics.Compact.gfun_eq ℓ d hd ((n : ℝ) +ᵥ w)
      (Work.Kernels.imagAxis t ht0)
    rw [eq_div_iff (by norm_num : (2:ℂ) ≠ 0), mul_comm]
    exact h.symm
  have hKfun : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
      = (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
          + Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)) / 2 :=
    rfl
  have hsplit : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
      = ((Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
            - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0))
          + (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
            - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
                (Work.Kernels.imagAxis t ht0))) / 2 := by
    rw [hKax, hAex, hGfun, hKfun]
    ring
  -- the two bounds at the common exponents
  have b1' : ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
        - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖
      ≤ C2 * (Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2)
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
    refine le_trans b2 ?_
    have h0 : (0:ℝ) ≤ Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := (Real.exp_pos _).le
    have hcomp : (Work.Kernels.scale w) ^ N2 * t ^ M2
        ≤ (Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2) :=
      mul_le_mul hsN2 htM2 (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg
        (Work.Kernels.scale_pos w).le _)
    calc C2 * (Work.Kernels.scale w) ^ N2 * t ^ M2
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        = C2 * ((Work.Kernels.scale w) ^ N2 * t ^ M2
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) := by ring
      _ ≤ C2 * ((Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2)
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcomp h0) hC2.le
      _ = C2 * (Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2)
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by ring
  have b2' : ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
        - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖
      ≤ C1 * (Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2)
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
    refine le_trans b1 ?_
    have h0 : (0:ℝ) ≤ Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := (Real.exp_pos _).le
    have hcomp : (Work.Kernels.scale w) ^ N1 * t ^ M1
        ≤ (Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2) :=
      mul_le_mul hsN1 htM1 (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg
        (Work.Kernels.scale_pos w).le _)
    calc C1 * (Work.Kernels.scale w) ^ N1 * t ^ M1
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        = C1 * ((Work.Kernels.scale w) ^ N1 * t ^ M1
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) := by ring
      _ ≤ C1 * ((Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2)
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcomp h0) hC1.le
      _ = C1 * (Work.Kernels.scale w) ^ (max N1 N2) * t ^ (max M1 M2)
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by ring
  rw [hsplit, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num]
  have hsum := add_le_add b1' b2'
  refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
  refine le_trans (div_le_div_of_nonneg_right hsum (by norm_num)) (le_of_eq ?_)
  ring

/-- **The sharp cusp-`i∞` tail on the cusp-`±1` tiles.** -/
theorem tileSharpTail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) :=
  tileSharpTail_of_halves ℓ d hd (KMinusTileTail ℓ d hd) (KPlusTileTail d hd)

end

end Work.Asymptotics.Tile
