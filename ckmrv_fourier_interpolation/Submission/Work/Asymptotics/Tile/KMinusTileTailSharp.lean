import Mathlib
import Submission.Work.Asymptotics.Tile.KMinusSharpChain
import Submission.Work.Asymptotics.Tile.tileDivisorSharp

/-!
# The sharp-threshold `K_-` cusp-`i∞` tail on the cusp-`±1` tiles

For `w ∈ E = KEpsilon`, `n = ±1` and the *sharp* threshold `t ≥ Im (S • w) + 1` the kernel
`K_-^{(d)}` differs from its cusp model `𝒢_-^{(d)}` by
`O((scale w)^N (1+t)^M e^{π Im(Sw) - π t})`:

`Work.Asymptotics.Tile.KMinusTileTailSharp`.

This is `Work.Asymptotics.Tile.KMinusTileTail` with the crude threshold `2 Im (S • w) + 1 ≤ t`
replaced by the sharp one `Im (S • w) + 1 ≤ t` — the height of the nearest pole of `z ↦ K(τ,z)`
above the real axis (the poles in question are the translates `S • w + k`, all of height
`Im (S • w)`; see `Work.Asymptotics.Tile.tileWin` for the role of this range).

The proof is the same as for `KMinusTileTail`: the exact identity

`3456π(K_- - 𝒢_-)(τ,z) = -(Sh τ z)⁻¹ (br + Sh · br0)`

of `Work.Asymptotics.Compact.tail_identity`, combined with

* the *sharp* reciprocal-divisor bound `Work.Asymptotics.Tile.tile_invDivisor_le_sharp`
  (`‖(Sh)⁻¹‖ ≤ 16` for `t ≥ Im (S•w) + 1`), and
* the sharp-threshold bracket bound `Work.Asymptotics.Tile.TBM.ktl_G8` / `TBM.ktl_G24` of
  `Submission/Work/Asymptotics/Tile/KMinusSharpChain.lean` (the `TB`-calculus of
  `Submission/Work/Asymptotics/Tile/tileTB.lean` with the sharp threshold; every exponent pair
  occurring in the `K_-` bracket satisfies `a ≤ b π`, so the whole chain of
  `Submission/Work/Asymptotics/Tile/KMinusTileTail.lean` goes through verbatim).
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels

noncomputable section

theorem KMinusTileTailSharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) := by
  have hG : TBM Real.pi 1 (fun w n z => Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z) := by
    rcases hd with rfl | rfl
    · exact TBM.ktl_G8 ℓ
    · exact TBM.ktl_G24 ℓ
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hG
  refine ⟨(3456 * Real.pi)⁻¹ * 16 * C, N, M, by positivity, hN, hM, ?_⟩
  intro w n z t hn hw hz ht
  -- the sharp reciprocal-divisor bound, in the form `Sh τ z = -Δ(z)(j τ - j z)`
  have hdiv : (1 / 16 : ℝ) ≤ ‖DeltaFun z
      * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z)‖ :=
    tileDivisorLowerSharp w hw z t hz ht n hn
  have hSne : Compact.Sh ((n : ℝ) +ᵥ w) z ≠ 0 := by
    have hne : DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hdiv
      norm_num at hdiv
    rw [Compact.Sh_eq]
    simpa using hne
  have hid := Compact.tail_identity ℓ d hd ((n : ℝ) +ᵥ w) z hSne
  have hinv : ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹‖ ≤ 16 := by
    rw [Compact.Sh_eq, inv_neg, norm_neg]
    exact tile_invDivisor_le_sharp w hw z t hz ht n hn
  have hbr : ‖Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖
      ≤ C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) := by
    have h := hb w n z t hn hw hz ht
    rwa [show Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t)
        = Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) from by congr 1; ring] at h
  have hnorm : ‖((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
        - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z)‖
      = ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹ * (Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
          + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖ := by
    rw [hid, norm_neg]
  have hconst : ‖((3456 : ℂ) * (Real.pi : ℂ))‖ = 3456 * Real.pi := by
    rw [norm_mul, show ‖(3456 : ℂ)‖ = 3456 by norm_num, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hkey : ((3456 : ℝ) * Real.pi) * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
        - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
      ≤ 16 * (C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) := by
    have h1 : ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹ * (Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖
        = ((3456 : ℝ) * Real.pi) * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
            - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖ := by
      rw [← hnorm, norm_mul, hconst]
    rw [← h1]
    calc ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹ * (Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖
        ≤ ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹‖
          * ‖Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖ := norm_mul_le _ _
      _ ≤ 16 * ‖Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ ≤ 16 * (C * (scale w) ^ N * (1 + t) ^ M
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) :=
          mul_le_mul_of_nonneg_left hbr (by norm_num)
  calc ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
        - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
      = ((3456 * Real.pi)⁻¹) * (((3456 : ℝ) * Real.pi)
          * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
            - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ ≤ ((3456 * Real.pi)⁻¹) * (16 * (C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * ((ModularGroup.S • w).im - t)))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((3456 * Real.pi)⁻¹ * 16 * C) * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) := by ring


/-- **The `K_-` half of the below-pole window on the cusp-`±1` tiles.**

In the range `Im (S • w) + 1 ≤ t ≤ 2 Im (S • w) + 1` the sharp tail bound of
`KMinusTileTailSharp` degenerates (the exponential factor is `≤ 1`) and one obtains the polynomial
bound `O((scale w)^N t^M)` of `Work.Asymptotics.Tile.TileBelowPoleTop` for the `K_-` half. -/
theorem KMinusTileTopWindow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
        t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := KMinusTileTailSharp ℓ d hd
  refine ⟨C * 2 ^ M, N, M, by positivity, hN, hM, ?_⟩
  intro w n z t hn hw hz ht ht2
  have ht1 : (1 : ℝ) ≤ t := by have := hw.2; linarith
  have hHt : (ModularGroup.S • w).im ≤ t := by linarith
  have hb' := hb w n z t hn hw hz ht
  have hexp : Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos]
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
  have hpoly : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
    have h1 : (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0] at h1
  have hscale : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos w).le N
  have hstep : (1 + t) ^ M * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))
      ≤ (2 ^ M * t ^ M) * 1 :=
    mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
  calc ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
        - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
      ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) := hb'
    _ = C * (Work.Kernels.scale w) ^ N
          * ((1 + t) ^ M * Real.exp (Real.pi * ((ModularGroup.S • w).im - t))) := by ring
    _ ≤ C * (Work.Kernels.scale w) ^ N * ((2 ^ M * t ^ M) * 1) :=
        mul_le_mul_of_nonneg_left hstep (mul_nonneg hC.le hscale)
    _ = C * 2 ^ M * (Work.Kernels.scale w) ^ N * t ^ M := by ring


end

end Work.Asymptotics.Tile
