import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresTailPoly
import Submission.Work.Asymptotics.KhatE1R.Kdev8WresAssembly

/-!
# `Kdev8WresTailGlue`: the last composition of the sharp `d = 8` funnel tail bound

`KhatE1Core.Kdev8WresAssembly.Kdev8Bracket_tail_of_WresBounds` (proved) reduces the sharp tail
bound to the two function-level estimates

* `‖WresPoly ℓ τ z‖ ≤ C‖q(τ)‖³‖Ept z‖²(scale τ)^N(1+t)^M`,
* `‖WresDev ℓ τ z‖ ≤ C‖q(τ)‖³‖Ept z‖²(scale τ)^N(1+t)^M`,

and `KhatE1.WresPoly_eq_pol_add` splits the first as
`WresPoly = WresPolyPol + ((3456π)⁻¹Δ·Dev8Rem − tailC⁻¹Δ²·kdevNum0Rem)`.

This file composes the three pieces: it takes the estimate for the explicit polynomial
`WresPolyPol`, the estimate for the `Dev8Rem`/`kdevNum0Rem` remainder, and the estimate for
`WresDev`, and produces the exact conclusion of `KhatE1.Kdev8BracketTailBound`.
-/

namespace Work.Asymptotics.KhatE1R

open Work.Asymptotics.KhatE1Core Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The deviation remainder of `WresPoly_eq_pol_add`, as a named object. -/
def WresPolyDevRem (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Kernels.DeltaFun τ * Dev8Rem ℓ τ z
    - Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ
        * kdevNum0Rem τ z

/-- **`WresPoly` is the explicit polynomial plus `WresPolyDevRem`.**  Repackaging of
`WresPoly_eq_pol_add`. -/
theorem WresPoly_eq_pol_add_rem (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    WresPoly ℓ τ z = WresPolyPol ℓ τ z + WresPolyDevRem ℓ τ z := by
  rw [WresPoly_eq_pol_add ℓ τ z, WresPolyDevRem]

/-- **The final assembly.**  The three function-level estimates imply the sharp funnel tail
bound for the `d = 8` bracket, i.e. the conclusion of `KhatE1.Kdev8BracketTailBound`. -/
theorem Kdev8BracketTail_of_three (ℓ : Work.Kernels.LogLambdaData)
    (hP : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖WresPolyPol ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
    (hdev : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖WresPolyDevRem ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
    (hD : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1RCore.WresDev ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨CP, NP, MP, hCP, hNP, hMP, hPb⟩ := hP
  obtain ⟨CD, ND, MD, hCD, hND, hMD, hDb⟩ := hdev
  -- combine into the `WresPoly` estimate
  refine Work.Asymptotics.KhatE1RCore.Kdev8Bracket_tail_of_WresBounds ℓ
    ⟨CP + CD, max NP ND, max MP MD, by positivity, le_trans hNP (le_max_left _ _),
      le_trans hMP (le_max_left _ _), ?_⟩ hD
  intro τ z t hτ ht h1 h2 hzt
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hT1 : (1 : ℝ) ≤ 1 + t := by
    have : (2 : ℝ) ≤ τ.im := hτ.2
    linarith
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hS0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hS1
  have hT0 : (0 : ℝ) ≤ 1 + t := le_trans zero_le_one hT1
  have hE0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ 2 := by positivity
  have hSN1 : (Work.Kernels.scale τ) ^ NP ≤ (Work.Kernels.scale τ) ^ max NP ND :=
    Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left _ _)
  have hSN2 : (Work.Kernels.scale τ) ^ ND ≤ (Work.Kernels.scale τ) ^ max NP ND :=
    Real.rpow_le_rpow_of_exponent_le hS1 (le_max_right _ _)
  have hTM1 : (1 + t) ^ MP ≤ (1 + t) ^ max MP MD :=
    Real.rpow_le_rpow_of_exponent_le hT1 (le_max_left _ _)
  have hTM2 : (1 + t) ^ MD ≤ (1 + t) ^ max MP MD :=
    Real.rpow_le_rpow_of_exponent_le hT1 (le_max_right _ _)
  have hSmax0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ max NP ND := Real.rpow_nonneg hS0 _
  have hTmax0 : (0 : ℝ) ≤ (1 + t) ^ max MP MD := Real.rpow_nonneg hT0 _
  have hSNP0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ NP := Real.rpow_nonneg hS0 _
  have hTMP0 : (0 : ℝ) ≤ (1 + t) ^ MP := Real.rpow_nonneg hT0 _
  have hSND0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ ND := Real.rpow_nonneg hS0 _
  have hTMD0 : (0 : ℝ) ≤ (1 + t) ^ MD := Real.rpow_nonneg hT0 _
  have hbase : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 :=
    mul_nonneg (pow_nonneg hq0 _) hE0
  have hA : ‖WresPolyPol ℓ τ z‖
      ≤ CP * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
          * (Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD := by
    refine le_trans (hPb τ z t hτ ht h1 h2 hzt) ?_
    have hmono : (Work.Kernels.scale τ) ^ NP * (1 + t) ^ MP
        ≤ (Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD :=
      mul_le_mul hSN1 hTM1 hTMP0 hSmax0
    calc CP * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * (Work.Kernels.scale τ) ^ NP * (1 + t) ^ MP
        = CP * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * ((Work.Kernels.scale τ) ^ NP * (1 + t) ^ MP) := by ring
      _ ≤ CP * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * ((Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = CP * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * (Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD := by ring
  have hB : ‖WresPolyDevRem ℓ τ z‖
      ≤ CD * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
          * (Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD := by
    refine le_trans (hDb τ z t hτ ht h1 h2 hzt) ?_
    have hmono : (Work.Kernels.scale τ) ^ ND * (1 + t) ^ MD
        ≤ (Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD :=
      mul_le_mul hSN2 hTM2 hTMD0 hSmax0
    calc CD * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * (Work.Kernels.scale τ) ^ ND * (1 + t) ^ MD
        = CD * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * ((Work.Kernels.scale τ) ^ ND * (1 + t) ^ MD) := by ring
      _ ≤ CD * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * ((Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = CD * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
            * (Work.Kernels.scale τ) ^ max NP ND * (1 + t) ^ max MP MD := by ring
  rw [WresPoly_eq_pol_add_rem ℓ τ z]
  refine le_trans (norm_add_le _ _) ?_
  have hsum := add_le_add hA hB
  refine le_trans hsum (le_of_eq ?_)
  ring

end

end Work.Asymptotics.KhatE1R
