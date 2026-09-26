import Mathlib
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresZAtoms
import Submission.Work.Asymptotics.KhatE1.KdevBracket_rest
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.Compact.zsmall

/-!
# Assembly of the sharp funnel bound from the two function-level estimates

The cleared residual of the sharp bracket tail bound is, by the *proved*
`KhatE1.KdevWresClearedPoly_decomp`,

  `Δ(τ)·(Δ(τ)·Sh(τ,z)·Wres) = WresPoly ℓ τ z + WresDev ℓ τ z`,

where `Wres = Kdev8Bracket ℓ τ z - 2·KdevE2 ℓ τ z·E(z)²`, `WresPoly` is the explicit polynomial
obtained by replacing every `z`-atom by its second/high truncation, and `WresDev` collects the
three deviation aggregates.

This file isolates the purely analytic assembly: **if** both `WresPoly` and `WresDev` are
`O(‖q(τ)‖³‖E(z)‖²(scale τ)^N(1+t)^M)` on the funnel strip, **then** the sharp tail bound

  `‖Wres‖ ≤ C‖q(τ)‖(scale τ)^N(1+t)^M exp(-2πt)`

holds.  The two estimates are the "floor" computations of the `u = Ept z` expansion; the
division steps here consume only the proved uniform lower bounds

* `‖Δ(τ)‖ ≥ (1/2)‖q(τ)‖` (`Funnel24Aux.DeltaFun_ge_half_qParam`),
* `‖Sh(τ,z)‖ ≥ 1/16` on the funnel strip (`KhatE1.funnel_Sh_ge_strip`).

-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- The residual of the sharp bracket tail bound:
`Wres = Kdev8Bracket - 2·KdevE2·E(z)²`. -/
def Wres (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
    - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2

/-- The deviation part of the cleared residual (the three aggregates of
`KhatE1.KdevWresClearedPoly_decomp`). -/
def WresDev (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Asymptotics.KhatE1.kdevA2JF ℓ τ z
      - 2 * (Work.Residues.Ept z) ^ 2
          * (Work.Kernels.DeltaFun τ * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z))
      * Work.Asymptotics.KhatE1.ShDev τ z
    + Work.Asymptotics.KhatE1.KdevA2Dev ℓ τ z * Work.Asymptotics.KhatE1.ShDeltaZtr τ z
    + Work.Asymptotics.KhatE1.KdevSig2Dev ℓ τ z

/-- **The exact split of the doubly cleared residual.** -/
theorem Delta_sq_mul_Wres_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0)
    (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z
        * Wres ℓ τ z)
      = Work.Asymptotics.KhatE1.WresPoly ℓ τ z + WresDev ℓ τ z := by
  have h := Work.Asymptotics.KhatE1.KdevWresClearedPoly_decomp ℓ τ z hSh hΔ
  rw [show Wres ℓ τ z = (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
        - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2) from rfl]
  rw [h]
  unfold WresDev
  ring

/-- **The assembly.**  The two function-level estimates for `WresPoly` and `WresDev` imply the
sharp funnel bracket tail bound. -/
theorem Kdev8Bracket_tail_of_WresBounds (ℓ : Work.Kernels.LogLambdaData)
    (hP : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.WresPoly ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
    (hD : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖WresDev ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Wres ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨CP, NP, MP, hCP, hNP, hMP, hPb⟩ := hP
  obtain ⟨CD, ND, MD, hCD, hND, hMD, hDb⟩ := hD
  refine ⟨64 * (CP + CD), max NP ND, max MP MD, by positivity,
    le_trans hNP (le_max_left _ _), le_trans hMP (le_max_left _ _), ?_⟩
  intro τ z t hτ ht h1z h2z hzt
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have ht3 : (3 : ℝ) ≤ t := by linarith
  have hz3 : (3 : ℝ) ≤ z.im := by rw [hzt]; exact ht3
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 :=
    Work.Asymptotics.KhatE1.Sh_ne_zero_of_im_ge τ z hτ2 (by rw [hzt]; exact ht)
  have hsplit := Delta_sq_mul_Wres_eq ℓ τ z hSh hΔ
  have hPv := hPb τ z t hτ ht h1z h2z hzt
  have hDv := hDb τ z t hτ ht h1z h2z hzt
  -- shrink the exponents to the common `max`
  set S : ℝ := Work.Kernels.scale τ with hSdef
  set T : ℝ := 1 + t with hTdef
  set X : ℝ := ‖Work.Kernels.qParamFun τ‖ with hXdef
  set E2 : ℝ := ‖Work.Residues.Ept z‖ ^ 2 with hE2def
  have hS1 : (1 : ℝ) ≤ S := by rw [hSdef]; exact Work.Kernels.one_le_scale τ
  have hS0 : (0 : ℝ) ≤ S := le_trans zero_le_one hS1
  have hT1 : (1 : ℝ) ≤ T := by rw [hTdef]; linarith
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hE20 : (0 : ℝ) ≤ E2 := by rw [hE2def]; positivity
  have hSN1 : S ^ NP ≤ S ^ max NP ND := Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left _ _)
  have hSN2 : S ^ ND ≤ S ^ max NP ND := Real.rpow_le_rpow_of_exponent_le hS1 (le_max_right _ _)
  have hTM1 : T ^ MP ≤ T ^ max MP MD := Real.rpow_le_rpow_of_exponent_le hT1 (le_max_left _ _)
  have hTM2 : T ^ MD ≤ T ^ max MP MD := Real.rpow_le_rpow_of_exponent_le hT1 (le_max_right _ _)
  have hSmax0 : (0 : ℝ) ≤ S ^ max NP ND := Real.rpow_nonneg hS0 _
  have hTmax0 : (0 : ℝ) ≤ T ^ max MP MD := Real.rpow_nonneg hT0 _
  have hSND0 : (0 : ℝ) ≤ S ^ ND := Real.rpow_nonneg hS0 _
  have hTMD0 : (0 : ℝ) ≤ T ^ MD := Real.rpow_nonneg hT0 _
  have hSNP0 : (0 : ℝ) ≤ S ^ NP := Real.rpow_nonneg hS0 _
  have hTMP0 : (0 : ℝ) ≤ T ^ MP := Real.rpow_nonneg hT0 _
  have key : ‖Work.Asymptotics.KhatE1.WresPoly ℓ τ z‖ + ‖WresDev ℓ τ z‖
      ≤ (CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by
    have h1 : ‖Work.Asymptotics.KhatE1.WresPoly ℓ τ z‖
        ≤ CP * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by
      refine le_trans hPv ?_
      have hmono : S ^ NP * T ^ MP ≤ S ^ (max NP ND) * T ^ (max MP MD) :=
        mul_le_mul hSN1 hTM1 hTMP0 hSmax0
      calc CP * X ^ 3 * E2 * S ^ NP * T ^ MP
          = CP * X ^ 3 * E2 * (S ^ NP * T ^ MP) := by ring
        _ ≤ CP * X ^ 3 * E2 * (S ^ (max NP ND) * T ^ (max MP MD)) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = CP * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by ring
    have h2 : ‖WresDev ℓ τ z‖
        ≤ CD * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by
      refine le_trans hDv ?_
      have hmono : S ^ ND * T ^ MD ≤ S ^ (max NP ND) * T ^ (max MP MD) :=
        mul_le_mul hSN2 hTM2 hTMD0 hSmax0
      calc CD * X ^ 3 * E2 * S ^ ND * T ^ MD
          = CD * X ^ 3 * E2 * (S ^ ND * T ^ MD) := by ring
        _ ≤ CD * X ^ 3 * E2 * (S ^ (max NP ND) * T ^ (max MP MD)) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = CD * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by ring
    have h3 : (CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD)
        = CP * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD)
          + CD * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by ring
    rw [h3]
    exact add_le_add h1 h2
  -- the standard `A·B = AB`-form of the two bounds
  have hAB : ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ
        * (Work.Asymptotics.Compact.Sh τ z * Wres ℓ τ z)‖ ≤
      (CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by
    rw [show Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ
          * (Work.Asymptotics.Compact.Sh τ z * Wres ℓ τ z)
        = Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ
            * Work.Asymptotics.Compact.Sh τ z * Wres ℓ τ z) from by ring, hsplit]
    exact le_trans (norm_add_le _ _) key
  -- divide: `‖Wres‖ = ‖Δ²·(Sh·Wres)‖ / (‖Δ‖·‖ΔSh‖)`
  have hΔlow : (1 / 2 : ℝ) * X ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    rw [hXdef]; exact Work.FunnelNumerics.Delta_funnel_bounds.1 τ hτ2
  have hDSh : (1 / 32 : ℝ) * X
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖ := by
    rw [hXdef]
    exact Work.Asymptotics.KhatE1.Delta_mul_Sh_ge_strip τ z t hτ ht hzt
  have hXpos : 0 < X := by
    rw [hXdef]; exact norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ)
  have hnorm : ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ
        * (Work.Asymptotics.Compact.Sh τ z * Wres ℓ τ z)‖
      = ‖Work.Kernels.DeltaFun τ‖
        * (‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖ * ‖Wres ℓ τ z‖) := by
    rw [show Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ
          * (Work.Asymptotics.Compact.Sh τ z * Wres ℓ τ z)
        = Work.Kernels.DeltaFun τ * ((Work.Kernels.DeltaFun τ
            * Work.Asymptotics.Compact.Sh τ z) * Wres ℓ τ z) from by ring,
      norm_mul, norm_mul]
  have hden : (1 / 2 : ℝ) * X * ((1 / 32 : ℝ) * X)
      ≤ ‖Work.Kernels.DeltaFun τ‖
        * ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖ :=
    mul_le_mul hΔlow hDSh (by positivity) (by positivity)
  have hmain : X ^ 2 / 64 * ‖Wres ℓ τ z‖
      ≤ (CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD) := by
    have hcoef : (1 / 2 : ℝ) * X * ((1 / 32 : ℝ) * X) = X ^ 2 / 64 := by ring
    have h1 : X ^ 2 / 64 * ‖Wres ℓ τ z‖
        ≤ ‖Work.Kernels.DeltaFun τ‖
          * (‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖
              * ‖Wres ℓ τ z‖) := by
      rw [← hcoef]
      calc (1 / 2 : ℝ) * X * ((1 / 32 : ℝ) * X) * ‖Wres ℓ τ z‖
          ≤ (‖Work.Kernels.DeltaFun τ‖
              * ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖)
            * ‖Wres ℓ τ z‖ := mul_le_mul_of_nonneg_right hden (norm_nonneg _)
        _ = ‖Work.Kernels.DeltaFun τ‖
              * (‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖
                * ‖Wres ℓ τ z‖) := by ring
    rw [← hnorm] at h1
    exact le_trans h1 hAB
  have hmul : X ^ 2 * ‖Wres ℓ τ z‖
      ≤ 64 * ((CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD)) := by
    have h64 := mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ (64 : ℝ))
    calc X ^ 2 * ‖Wres ℓ τ z‖
        = 64 * (X ^ 2 / 64 * ‖Wres ℓ τ z‖) := by ring
      _ ≤ 64 * ((CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD)) := h64
  have hX2 : 0 < X ^ 2 := by positivity
  have h64 : 64 * ((CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD)) / X ^ 2
      = 64 * (CP + CD) * X * S ^ (max NP ND) * T ^ (max MP MD) * E2 := by
    field_simp
  have hfinal : ‖Wres ℓ τ z‖
      ≤ 64 * (CP + CD) * X * S ^ (max NP ND) * T ^ (max MP MD) * E2 := by
    have hdiv : ‖Wres ℓ τ z‖
        ≤ 64 * ((CP + CD) * X ^ 3 * E2 * S ^ (max NP ND) * T ^ (max MP MD)) / X ^ 2 :=
      (le_div_iff₀ hX2).mpr (by rw [mul_comm]; exact hmul)
    rwa [h64] at hdiv
  have hE2eq : E2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [hE2def, Work.Residues.norm_Ept, hzt]
    rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  rw [hXdef, hSdef, hTdef, hE2eq] at hfinal
  exact hfinal

end

end Work.Asymptotics.KhatE1Core
