import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Tile.tileFarDiv
import Submission.Work.Asymptotics.TileFarBracket

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-!
# The `K_-` far half-deviation on the cusp-`±1` tiles

For `w ∈ E = KEpsilon`, `n = ±1`, `z = i t` with `3 ≤ t ≤ Im (S • w) - 1`, the deviation of
`K_-^{(d)}` from its cusp model `𝒢_-` is bounded polynomially:

  `‖K_-^{(d)}(n +ᵥ w, i t) - 𝒢_-^{(d)}(n +ᵥ w, i t)‖ ≤ C (scale w)^N t^M`.

## The proof

The cusp bracket identity (`Work.Asymptotics.Compact.tail_identity`)

  `3456π (K_- - 𝒢_-)(τ,z) = -(Sh τ z)⁻¹ (brMinus τ z + Sh τ z · br0 τ z)`,  `Sh = -Δ(z)(jτ - jz)`,

reduces the deviation to the *cleared* bracket `brMinus + Sh · br0`.  The far-window calculus
`Work.Asymptotics.Tile.TBF` (`TileFarBracket.lean`) bounds that bracket on exactly this window
with the exponent pair `(2π, 2)`, i.e.

  `‖brMinus + Sh · br0‖ ≤ C (scale w)^N (1+t)^M e^{2π (Im (S•w) - t)}`

(`TBF.ktl_G8_far`, `TBF.ktl_G24_far`), while the sharp divisor lower bound
`Tile.divisorLowerSharpFar` gives

  `‖Sh‖ ≥ c e^{2π (Im (S•w) - t)}`.

The two exponentials cancel and the polynomial bound results.
-/

/-- **The cleared bracket bound of the far window**, in the exact form used below (`1 ≤ t`,
`t ≤ Im (S • w) - 1`).  This is `Work.Asymptotics.Tile.TBF.ktl_G8_far` /
`TBF.ktl_G24_far`. -/
private theorem brMinus_add_Sh_br0_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → 3 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Asymptotics.Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
          + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z
            * Work.Asymptotics.Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
  rcases hd with rfl | rfl
  · obtain ⟨C, N, M, hC, hN, hM, hb⟩ := TBF.ktl_G8_far ℓ
    exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht3 htle =>
      hb w n z t hn hw hz ⟨by linarith, htle⟩⟩
  · obtain ⟨C, N, M, hC, hN, hM, hb⟩ := TBF.ktl_G24_far ℓ
    exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht3 htle =>
      hb w n z t hn hw hz ⟨by linarith, htle⟩⟩

/-- `‖(3456 * π : ℂ)‖ = 3456 * π`. -/
private lemma norm_3456_pi :
    ‖((3456 : ℂ) * (Real.pi : ℂ))‖ = 3456 * Real.pi := by
  rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

theorem halfDevFarMinus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → 3 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨c, hc, hdiv⟩ := divisorLowerSharpFar
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb⟩ := brMinus_add_Sh_br0_far ℓ d hd
  refine ⟨C1 / (c * (3456 * Real.pi)) * 2 ^ M1, N1, M1, ?_, hN1, hM1, ?_⟩
  · have h1 : (0 : ℝ) < c * (3456 * Real.pi) := by positivity
    have h2 : (0 : ℝ) < C1 / (c * (3456 * Real.pi)) := div_pos hC1 h1
    have h3 : (0 : ℝ) < (2 : ℝ) ^ M1 := Real.rpow_pos_of_pos (by norm_num) M1
    positivity
  · intro w n z t hn hw hz ht3 htle
    have ht0 : (0 : ℝ) < t := by linarith
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have hzs : z = Work.Kernels.imagAxis t ht0 :=
      UpperHalfPlane.ext (by rw [hz]; rfl)
    have hjv : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w :=
      ktl_jInvariantFun_vadd_int n hn w
    -- `‖Sh‖` is the far divisor
    have hSheq : ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z‖
        = ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht0)
            * (Work.Kernels.jInvariantFun w
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0))‖ := by
      rw [Work.Asymptotics.Compact.Sh_eq, hzs, hjv, norm_neg]
    have hEeq : Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t))
        = Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
      congr 1; ring
    have hhlow : c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
        ≤ ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z‖ := by
      rw [hSheq, ← hEeq]; exact hdiv w t ht0 hw ht1 htle
    have hce : 0 < c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
      positivity
    have hShne : Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hhlow
      linarith
    -- the tail identity
    have htail := Work.Asymptotics.Compact.tail_identity ℓ d hd ((n : ℝ) +ᵥ w) z hShne
    have hnum := hb w n z t hn hw hz ht3 htle
    have hShpos : 0 < ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z‖ := lt_of_lt_of_le hce hhlow
    have hinv : ‖(Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹‖
        ≤ (c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t))⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ hShpos hce).mpr hhlow
    -- take norms of the identity
    have hnorm : (3456 * Real.pi)
          * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        = ‖(Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹
            * (Work.Asymptotics.Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
              + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z
                * Work.Asymptotics.Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖ := by
      have h2 : ‖((3456 : ℂ) * (Real.pi : ℂ))
            * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z)‖
          = (3456 * Real.pi)
            * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖ := by
        rw [norm_mul, norm_3456_pi]
      rw [← h2, htail, norm_neg]
    -- the main estimate, before the division by `3456 π`
    have hmain : (3456 * Real.pi)
          * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ C1 / c * (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1 := by
      rw [hnorm]
      calc ‖(Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹
            * (Work.Asymptotics.Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
              + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z
                * Work.Asymptotics.Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖
          ≤ ‖(Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹‖
            * ‖Work.Asymptotics.Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
              + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) z
                * Work.Asymptotics.Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖ := norm_mul_le _ _
        _ ≤ (c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t))⁻¹
              * (C1 * (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1
                  * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)) :=
              mul_le_mul hinv hnum (norm_nonneg _) (inv_nonneg.mpr hce.le)
        _ = C1 / c * (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1 := by
              have hc0 : c ≠ 0 := ne_of_gt hc
              have hEne :
                  Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) ≠ 0 :=
                ne_of_gt (Real.exp_pos _)
              field_simp
    -- absorb the constant of `(1+t)^M₁ ≤ 2^M₁ t^M₁`
    have hfin : (3456 * Real.pi)
          * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ C1 / c * (Work.Kernels.scale w) ^ N1 * (2 ^ M1 * t ^ M1) := by
      refine le_trans hmain ?_
      have h1t : (1 + t) ^ M1 ≤ (2 * t) ^ M1 :=
        Real.rpow_le_rpow (by positivity) (by linarith) hM1
      have h2t : (2 * t) ^ M1 = 2 ^ M1 * t ^ M1 :=
        Real.mul_rpow (by norm_num) ht0.le
      have hcoef : (0 : ℝ) ≤ C1 / c * (Work.Kernels.scale w) ^ N1 :=
        mul_nonneg (div_pos hC1 hc).le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N1)
      exact mul_le_mul_of_nonneg_left (h1t.trans (le_of_eq h2t)) hcoef
    -- divide by `3456 π`
    have h34 : (0 : ℝ) < 3456 * Real.pi := by positivity
    have hstep : ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
        ≤ (C1 / c * (Work.Kernels.scale w) ^ N1 * (2 ^ M1 * t ^ M1))
            / (3456 * Real.pi) := by
      rw [le_div_iff₀ h34, mul_comm]
      exact hfin
    refine le_trans hstep (le_of_eq ?_)
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

end

end Work.Asymptotics.Tile
