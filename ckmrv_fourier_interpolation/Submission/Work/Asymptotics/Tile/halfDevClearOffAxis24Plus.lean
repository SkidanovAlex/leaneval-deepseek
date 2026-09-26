import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.Tile.HalfDev24Aux
import Submission.Work.Asymptotics.Tile.HalfDev24TileFacts

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

set_option linter.unusedVariables false

-- **Cleared off-axis half-deviation bound for `K₊^{(24)}`** — one of the four ingredients of the
-- ball bound `Tile.tileNumBallBound`.
--
-- This is the same statement as `halfDevClearAxisPlus24` in
-- `Submission/Work/Asymptotics/Tile/tileStripCusp1Re.lean`, restated in its own module so that the
-- modules spelling out the ball bound can import it.  The proof below *reproduces* that file's proof
-- (inline, including a private copy of its `qParamFun`-norm helper), so that this module does not
-- depend on `tileStripCusp1Re` — which in turn imports modules that use this one.
-- `ℓ` is unused (kept for uniformity with the consumers).

/-- Off-axis norm of `qParamFun`. -/
private lemma norm_qParamFun_offAxis_inline (ζ : UpperHalfPlane) :
    ‖Work.Kernels.qParamFun ζ‖ = Real.exp (-(2 * Real.pi * ζ.im)) := by
  have h : Work.Kernels.qParamFun ζ = (Work.Residues.Ept ζ) ^ 2 := by
    rw [Work.Kernels.qParamFun, Work.Residues.Ept, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  rw [h, norm_pow, Work.Residues.norm_Ept, ← Real.exp_nat_mul]
  congr 1
  push_cast; ring

/-- **The cleared `K₊^{(24)}` deviation, off axis.**
For `w ∈ E`, `n = ±1` and `ζ ∈ ℍ` with `3 ≤ Im ζ` and `|Re ζ| ≤ 3`:
`‖Sh (n+ᵥw) ζ‖ ‖K₊24 (n+ᵥw) ζ - 𝒢₊24 (n+ᵥw) ζ‖`
`  ≤ C (scale w)^N (1 + Im ζ)^M exp (2π (Im (S•w) - Im ζ))`. -/
theorem halfDevClearOffAxis24Plus (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (ζ : UpperHalfPlane), (n = 1 ∨ n = -1) →
        w ∈ Work.Asymptotics.KEpsilon → 3 ≤ ζ.im → |(ζ : ℂ).re| ≤ 3 →
        ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ‖
            * ‖Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gplus 24 ((n : ℝ) +ᵥ w) ζ‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + ζ.im) ^ M
              * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im)) := by
  obtain ⟨KA, NA, hKAp, hNA, hAtoms⟩ := H24.tileAtoms24_axis
  obtain ⟨Ks, Ns, hKsp, hNsp, hSmsum⟩ := sm_sum_le_atoms
  refine ⟨‖K24F.c‖ * (64 * Ks * (KA + 1) ^ 2 * 4 ^ Ns) + 1, 2 * NA + Ns, 2,
    by positivity, by positivity, by norm_num, ?_⟩
  intro w n ζ hn hw hz3 hzre
  have hzw : (0 : ℝ) < ζ.im := by linarith
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  set E : ℝ := Real.exp (2 * Real.pi * (ModularGroup.S • w).im) with hEdef
  have hE1 : (1 : ℝ) ≤ E := by
    rw [hEdef, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have h2 := hw.2
    positivity
  set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
  -- scale τ ≤ 4 scale w
  have hscaleτ : Work.Kernels.scale τ ≤ 4 * Work.Kernels.scale w := by
    have hcoe : ((τ : ℍ) : ℂ) = ((n : ℝ) : ℂ) + (w : ℂ) := by
      rw [hτdef]; exact UpperHalfPlane.coe_vadd _ _
    have hτim : τ.im = w.im := by
      have h := congrArg Complex.im hcoe
      simpa [UpperHalfPlane.coe_im] using h
    have hn1 : ‖((n : ℝ) : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      rcases hn with h | h <;> rw [h] <;> norm_num
    have hnorm : ‖(τ : ℂ)‖ ≤ ‖(w : ℂ)‖ + 1 := by
      rw [hcoe]
      calc ‖((n : ℝ) : ℂ) + (w : ℂ)‖ ≤ ‖((n : ℝ) : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
        _ = ‖(w : ℂ)‖ + 1 := by rw [hn1]; ring
    have h1 : (w.im)⁻¹ ≤ Work.Kernels.scale w := by
      rw [Work.Kernels.scale]; linarith [norm_nonneg ((w : ℂ))]
    have h2 : ‖(w : ℂ)‖ ≤ Work.Kernels.scale w := by
      rw [Work.Kernels.scale]; linarith [inv_nonneg.mpr w.im_pos.le]
    rw [Work.Kernels.scale, hτim]
    nlinarith [h1, h2, hs1, hnorm]
  have hpowτ : (Work.Kernels.scale τ) ^ Ns ≤ 4 ^ Ns * (Work.Kernels.scale w) ^ Ns := by
    have h1 : (Work.Kernels.scale τ) ^ Ns ≤ (4 * Work.Kernels.scale w) ^ Ns :=
      Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le hscaleτ hNsp
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hs0.le] at h1
  -- the tile atoms, upgraded to the convenient constants
  set K0 : ℝ := KA + 1 with hK0def
  have hK01 : (1 : ℝ) < K0 := by rw [hK0def]; linarith
  have hK00 : (0 : ℝ) ≤ K0 := le_trans zero_le_one hK01.le
  set D : ℝ := K0 * (Work.Kernels.scale w) ^ NA with hDdef
  set Dj : ℝ := K0 * (Work.Kernels.scale w) ^ NA * E with hDjdef
  have hD0 : (0 : ℝ) ≤ D := by
    rw [hDdef]; exact mul_nonneg hK00 (Real.rpow_nonneg hs0.le NA)
  have hDj0 : (0 : ℝ) ≤ Dj := by rw [hDjdef]; exact mul_nonneg hD0 (Real.exp_nonneg _)
  have hsNA1 : (1 : ℝ) ≤ (Work.Kernels.scale w) ^ NA := Real.one_le_rpow hs1 hNA
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hDdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ K0 * (Work.Kernels.scale w) ^ NA :=
          mul_le_mul hK01.le hsNA1 (by norm_num) hK00
  have hDj1 : (1 : ℝ) ≤ Dj := by
    rw [hDjdef]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ K0 * (Work.Kernels.scale w) ^ NA * E :=
          mul_le_mul (mul_le_mul hK01.le hsNA1 (by norm_num) hK00) hE1 (by norm_num) hD0
  have hAt0 : TileAtoms24 τ D Dj := by
    have h0 := hAtoms w n hn hw
    refine h0.mono ?_ ?_
    · rw [hDdef]; exact mul_le_mul_of_nonneg_right (by rw [hK0def]; linarith)
        (Real.rpow_nonneg hs0.le NA)
    · rw [hDjdef]
      have h1 : KA * (Work.Kernels.scale w) ^ NA ≤ K0 * (Work.Kernels.scale w) ^ NA :=
        mul_le_mul_of_nonneg_right (by rw [hK0def]; linarith) (Real.rpow_nonneg hs0.le NA)
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  have hSm := hSmsum τ ζ D Dj hD0 hDj0 hAt0 hz3
  by_cases hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ = 0
  · have hSh0 : Work.Asymptotics.Compact.Sh τ ζ = 0 := by
      rw [Work.Asymptotics.Compact.Sh_eq, hJ, mul_zero, neg_zero]
    rw [hSh0]
    simp only [norm_zero, zero_mul]
    positivity
  · have hdiff := K24F.KPlus24_diff τ ζ hJ (K24F.E4_ne_zero_three ζ hz3)
    have hSh : Work.Asymptotics.Compact.Sh τ ζ
        = -(Work.Kernels.DeltaFun ζ
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ)) :=
      Work.Asymptotics.Compact.Sh_eq τ ζ
    have hkey : Work.Asymptotics.Compact.Sh τ ζ
          * (Work.Kernels.KPlus 24 τ ζ - Work.Asymptotics.Compact.Gplus 24 τ ζ)
        = -(K24F.c * (ζ : ℂ) ^ 2
            * (K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ)) := by
      rw [hSh, neg_mul, hdiff]
    rw [← norm_mul, hkey, norm_neg]
    -- numeric bounds
    have hznorm : ‖(ζ : ℂ)‖ ≤ 4 * (1 + ζ.im) := by
      have h1 : ‖(ζ : ℂ)‖ ≤ |(ζ : ℂ).re| + |(ζ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
      have h2 : |(ζ : ℂ).im| = ζ.im := by rw [UpperHalfPlane.coe_im, abs_of_pos hzw]
      rw [h2] at h1
      nlinarith [h1, hzre, hz3]
    have hq : ‖Work.Kernels.qParamFun ζ‖ = Real.exp (-(2 * Real.pi * ζ.im)) :=
      norm_qParamFun_offAxis_inline ζ
    have hprod : (1 + D) * (1 + Dj) ≤ 4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E := by
      have h1 : (1 : ℝ) + D ≤ 2 * D := by linarith
      have h2 : (1 : ℝ) + Dj ≤ 2 * Dj := by linarith
      have h3 : (1 + D) * (1 + Dj) ≤ (2 * D) * (2 * Dj) :=
        mul_le_mul h1 h2 (by linarith) (by linarith)
      have hs2 : (Work.Kernels.scale w) ^ NA * (Work.Kernels.scale w) ^ NA
          = (Work.Kernels.scale w) ^ (2 * NA) := by
        rw [← Real.rpow_add hs0]; congr 1; ring
      calc (1 + D) * (1 + Dj) ≤ (2 * D) * (2 * Dj) := h3
        _ = 4 * (K0 ^ 2 * ((Work.Kernels.scale w) ^ NA * (Work.Kernels.scale w) ^ NA) * E) := by
            rw [hDdef, hDjdef]; ring
        _ = 4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E := by rw [hs2]; ring
    have hexp : E * Real.exp (-(2 * Real.pi * ζ.im))
        = Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im)) := by
      rw [hEdef, ← Real.exp_add]
      congr 1; ring
    have hmain : ‖K24F.c * (ζ : ℂ) ^ 2
          * (K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ)‖
        ≤ ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
              * Real.exp (-(2 * Real.pi * ζ.im))) := by
      have h1 : ‖(ζ : ℂ) ^ 2‖ = ‖(ζ : ℂ)‖ ^ 2 := norm_pow _ 2
      have h2 : ‖(ζ : ℂ)‖ ^ 2 ≤ (4 * (1 + ζ.im)) ^ 2 := by
        have h0 : (0 : ℝ) ≤ ‖(ζ : ℂ)‖ := norm_nonneg _
        nlinarith [hznorm, h0, hzw]
      calc ‖K24F.c * (ζ : ℂ) ^ 2
            * (K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ)‖
          = ‖K24F.c‖ * ‖(ζ : ℂ) ^ 2‖ * ‖K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ
              + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
              * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
                  * ‖Work.Kernels.qParamFun ζ‖) := by
            rw [h1]
            exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) hSm
              (by positivity) (by positivity)
        _ = ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
              * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
                  * Real.exp (-(2 * Real.pi * ζ.im))) := by rw [hq]
    refine le_trans hmain ?_
    have hKsD : Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
        ≤ Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E)
            * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) := by
      have h1a : Ks * ((1 + D) * (1 + Dj))
          ≤ Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E) :=
        mul_le_mul_of_nonneg_left hprod hKsp.le
      have h1b := mul_le_mul h1a hpowτ (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le Ns)
        (by positivity)
      calc Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
          = (Ks * ((1 + D) * (1 + Dj))) * (Work.Kernels.scale τ) ^ Ns := by ring
        _ ≤ (Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E))
              * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) := h1b
    have hstep : ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
              * Real.exp (-(2 * Real.pi * ζ.im)))
        ≤ ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E)
              * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) * Real.exp (-(2 * Real.pi * ζ.im))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hKsD (Real.exp_nonneg _))
        (by positivity)
    have hcoef0 : (0 : ℝ) ≤ ‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns) := by positivity
    have hcomb2 : (Work.Kernels.scale w) ^ (2 * NA + Ns)
        = (Work.Kernels.scale w) ^ (2 * NA) * (Work.Kernels.scale w) ^ Ns :=
      Real.rpow_add hs0 _ _
    have hL : ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E)
              * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) * Real.exp (-(2 * Real.pi * ζ.im)))
        = (‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns))
          * ((Work.Kernels.scale w) ^ (2 * NA) * (Work.Kernels.scale w) ^ Ns)
          * (1 + ζ.im) ^ 2 * (E * Real.exp (-(2 * Real.pi * ζ.im))) := by ring
    refine le_trans hstep ?_
    rw [hL, ← hcomb2, hexp]
    have hfin : (‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns))
          * (Work.Kernels.scale w) ^ (2 * NA + Ns) * (1 + ζ.im) ^ 2
          * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im))
        ≤ (‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns) + 1) * (Work.Kernels.scale w) ^ (2 * NA + Ns)
          * (1 + ζ.im) ^ 2 * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs0.le _)
      linarith
    have hK0eq : K0 = KA + 1 := hK0def
    refine le_trans hfin (le_of_eq ?_)
    rw [hK0eq, Real.rpow_two]



end Work.Asymptotics.Tile
