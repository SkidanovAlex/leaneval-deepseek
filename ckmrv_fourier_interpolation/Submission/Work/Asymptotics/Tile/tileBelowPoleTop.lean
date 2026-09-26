import Mathlib
import Submission.Work.Asymptotics.Tile.tileWinDefs
import Submission.Work.Asymptotics.Tile.KPlusTileTailSharp
import Submission.Work.Asymptotics.Tile.KMinusTileTailSharp

/-!
# The below-pole "top" window on the cusp-`±1` tiles

Target: `Work.Asymptotics.Tile.TileBelowPoleTop` — for `w ∈ E = KEpsilon`, `n = ±1` and
`Im (S • w) + 1 ≤ t ≤ 2 Im (S • w) + 1`,

  `‖Kaxis (Kfun ℓ d) (n +ᵥ w) t − Aexp (Gcusp ℓ d) (n +ᵥ w) t‖ ≤ C (scale w)^N t^M`.

The range is the band just above the poles `S • w + k` of `z ↦ K (n +ᵥ w, z)` (which are all at
height `Im (S • w)`; see the module docs of `Tile/tileWin.lean`), i.e. the sharp-threshold region
that the crude `TB`-calculus (threshold `2 Im (S • w) + 1`) does not reach.

## Proof

`Kaxis (Kfun ℓ d)` is the average of the two halves `K_±` and `Aexp (Gcusp ℓ d)` is the average
of the two cusp models `𝒢_±` (the `Compact.gfun_eq` identification, exactly as in
`Tile.tileSharpTail_of_halves`), so the deviation is the average of the two *half*-deviations.
The two halves are controlled at the sharp threshold `Im (S • w) + 1` by

* `Work.Asymptotics.Tile.KPlusTileTailSharp` (proved, via the sharp `τ`/`z`-atom calculus
  `Work.Asymptotics.Tile.TBS` of `Tile/SharpTB.lean`), and
* `Work.Asymptotics.Tile.KMinusTileTailSharp` (proved, via the sharp `K_-` chain
  `Work.Asymptotics.Tile.TBM` of `Tile/KMinusSharpChain.lean`, using the sharp reciprocal
  divisor bound `Work.Asymptotics.Tile.tile_invDivisor_le_sharp`),

each with the rate `e^{π(Im (S • w) − t)}`, which is `≤ 1` on the band (as `t ≥ Im (S • w) + 1`).
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels Work.Asymptotics

noncomputable section


/-- Assembly: the two sharp-threshold half-tails imply the target on the band. -/
theorem tileBelowPoleTop_of_sharp_halves (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hKm : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t)))
    (hKp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) :
    TileBelowPoleTop ℓ d := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hKm
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hKp
  set Mx : ℝ := max M1 M2 with hMx
  have hMx0 : (0 : ℝ) ≤ Mx := by rw [hMx]; exact le_trans hM1 (le_max_left _ _)
  refine ⟨((C1 + C2) / 2 + 1) * (2 ^ Mx) + 1, max N1 N2, Mx, by positivity,
    le_max_of_le_left hN1, hMx0, ?_⟩
  intro w hw n hn t ht1 ht2
  have hA2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have ht0 : 0 < t := by linarith
  have ht1' : (1 : ℝ) ≤ t := by linarith
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hspos : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
    rw [Work.Kernels.Kaxis, dif_pos ht0]
  have hAex : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) :=
    (by rw [Work.Asymptotics.Gcusp_eq_Gcoef ℓ d hd,
      Work.Asymptotics.Aexp_Gcoef' ℓ d ((n : ℝ) +ᵥ w) t ht0])
  have hGfun : Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
      = (Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
          + Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w)
              (Work.Kernels.imagAxis t ht0)) / 2 := by
    have h := Work.Asymptotics.Compact.gfun_eq ℓ d hd ((n : ℝ) +ᵥ w)
      (Work.Kernels.imagAxis t ht0)
    rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
    exact h.symm
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
    rw [hKax, hAex, hGfun, hKfun]; ring
  have hexp : Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, ht1]
  have hN1' : (Work.Kernels.scale w) ^ N1 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hN2' : (Work.Kernels.scale w) ^ N2 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hM1' : (1 + t) ^ M1 ≤ (1 + t) ^ Mx := by
    rw [hMx]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hM2' : (1 + t) ^ M2 ≤ (1 + t) ^ Mx := by
    rw [hMx]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have hb1 : ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
        - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖
      ≤ C2 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx := by
    refine le_trans (h2 w n (Work.Kernels.imagAxis t ht0) t hn hw rfl ht1) ?_
    have h0 : (0 : ℝ) ≤ Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) := (Real.exp_pos _).le
    have hcomp : (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
        ≤ (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx :=
      mul_le_mul hN2' hM2' (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    calc C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))
        = C2 * ((Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) := by ring
      _ ≤ C2 * ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcomp h0) hC2.le
      _ ≤ C2 * ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp (by positivity)) hC2.le
      _ = C2 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx := by ring
  have hb2 : ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
        - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖
      ≤ C1 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx := by
    refine le_trans (h1 w n (Work.Kernels.imagAxis t ht0) t hn hw rfl ht1) ?_
    have h0 : (0 : ℝ) ≤ Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) := (Real.exp_pos _).le
    have hcomp : (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1
        ≤ (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx :=
      mul_le_mul hN1' hM1' (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    calc C1 * (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1
          * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))
        = C1 * ((Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) := by ring
      _ ≤ C1 * ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcomp h0) hC1.le
      _ ≤ C1 * ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp (by positivity)) hC1.le
      _ = C1 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx := by ring
  rw [hsplit, norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
  refine le_trans (div_le_div_of_nonneg_right (add_le_add hb1 hb2) (by norm_num)) ?_
  have hsN0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N1 N2) := Real.rpow_nonneg hspos.le _
  have htwo : (1 + t) ^ Mx ≤ (2 ^ Mx) * t ^ Mx := by
    have h : (1 + t) ^ Mx ≤ (2 * t) ^ Mx := Real.rpow_le_rpow (by linarith) (by linarith) hMx0
    rwa [Real.mul_rpow (by norm_num) ht0.le] at h
  have key : (C2 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx
        + C1 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx) / 2
      ≤ (((C1 + C2) / 2 + 1) * (2 ^ Mx) + 1)
          * (Work.Kernels.scale w) ^ (max N1 N2) * t ^ Mx := by
    have h2M : (1 : ℝ) ≤ 2 ^ Mx := Real.one_le_rpow (by norm_num) hMx0
    have hlow : (C1 + C2) / 2 * ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx)
        ≤ ((C1 + C2) / 2) * ((Work.Kernels.scale w) ^ (max N1 N2) * (2 ^ Mx * t ^ Mx)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htwo hsN0) (by positivity)
    calc (C2 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx
            + C1 * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx) / 2
        = ((C1 + C2) / 2) * ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ Mx) := by ring
      _ ≤ ((C1 + C2) / 2) * ((Work.Kernels.scale w) ^ (max N1 N2) * (2 ^ Mx * t ^ Mx)) := hlow
      _ ≤ (((C1 + C2) / 2 + 1) * (2 ^ Mx) + 1)
            * (Work.Kernels.scale w) ^ (max N1 N2) * t ^ Mx := by
          have hpos : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N1 N2) * t ^ Mx :=
            mul_nonneg hsN0 (Real.rpow_nonneg ht0.le _)
          have hcoef : (C1 + C2) / 2 * 2 ^ Mx
              ≤ ((C1 + C2) / 2 + 1) * (2 ^ Mx) + 1 := by
            have := mul_le_mul_of_nonneg_right (by linarith [hC1.le, hC2.le] : (C1 + C2) / 2
              ≤ (C1 + C2) / 2 + 1) (by positivity : (0:ℝ) ≤ 2 ^ Mx)
            linarith
          calc ((C1 + C2) / 2) * ((Work.Kernels.scale w) ^ (max N1 N2) * (2 ^ Mx * t ^ Mx))
              = ((C1 + C2) / 2 * 2 ^ Mx) * ((Work.Kernels.scale w) ^ (max N1 N2) * t ^ Mx) := by ring
            _ ≤ (((C1 + C2) / 2 + 1) * (2 ^ Mx) + 1)
                  * ((Work.Kernels.scale w) ^ (max N1 N2) * t ^ Mx) :=
                mul_le_mul_of_nonneg_right hcoef hpos
            _ = (((C1 + C2) / 2 + 1) * (2 ^ Mx) + 1)
                  * (Work.Kernels.scale w) ^ (max N1 N2) * t ^ Mx := by ring
  exact le_trans key (le_refl _)


/-- **The below-pole top window on the cusp-`±1` tiles** (the requested statement). -/
theorem tileBelowPoleTop (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Work.Asymptotics.Tile.TileBelowPoleTop ℓ d :=
  tileBelowPoleTop_of_sharp_halves ℓ d hd (KMinusTileTailSharp ℓ d hd)
    (KPlusTileTailSharp ℓ d hd)

end

end Work.Asymptotics.Tile
