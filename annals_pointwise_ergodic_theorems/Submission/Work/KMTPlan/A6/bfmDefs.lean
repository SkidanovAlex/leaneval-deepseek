/-
# Vocabulary for the Fourier-mass bound of the KMT bumps (`bumpFourierMass`)

This module fixes the objects in which the pieces of `Work.KMTPlan.A6.bumpFourierMass` are
stated.

The bumps `varphiN N k₁` and `varphitildeN d N k₂` of `Work.KMTAreas.A7` are *dilations of a
fixed bump*: with `L = Log N` (`Work.Analysis.EndVar.logN`) and `c := 2 ^ (d (L - k))` one has

  `varphiN N k₁   = fun ξ => ψ₁ (lacσ N k₁ * ξ)`  (`k₁ ≥ 1`, `lacσ N k₁ = 2 ^ (L - k₁)`),
  `varphitildeN d N k₂ = fun ξ => ψ_d (c ξ)`      (`k₂ ≥ 1`, `c = 2 ^ (d (L - k₂))`),

where `ψ_d (x) = η x - η (2^d x)` is the `d`-*scaled* mean-zero bump: the definition of
`varphitildeN` uses the `d`-fold rescaled frequencies, so the two `η`-terms differ by the factor
`2 ^ d` and not by `2`; for `d = 1` the bump `ψ_1` is the workspace's `lacψ`.  The dilations are
what turn the mass sum `∑_p ‖𝓕⁻(bump) (u - p)‖` into the lattice sum of `latticeQuadMass`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacBumpKernel

set_option autoImplicit false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open Work.Analysis.IonescuWainger
open Work.KMTContract

/-- **The `d`-scaled mean-zero bump** `ψ_d (x) = η x - η (2^d x)`, the fixed seed of the
`d`-fold rescaled bump `varphitildeN d N k₂`.  For `d = 1` it is the workspace's `lacψ`. -/
noncomputable def bfmBump (d : ℕ) (x : ℝ) : ℂ := kmtEta x - kmtEta ((2 : ℝ) ^ d * x)

/-- The frequency scale `2 ^ (d (Log N - k))` of the `d`-fold rescaled bump `varphitildeN`. -/
noncomputable def bfmTildeScale (d N k : ℕ) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))

/-- `ψ_1 = lacψ`: the `d = 1` bump is the workspace bump used for `varphiN`. -/
theorem bfmBump_one : bfmBump 1 = Work.KMTAreas.A7.lacψ := by
  funext x
  simp only [bfmBump, Work.KMTAreas.A7.lacψ, pow_one]

/-- The KMT cutoff is smooth (at every order). -/
theorem bfm_contDiff_kmtEta (n : ℕ∞) : ContDiff ℝ n kmtEta := by
  have h1 : ContDiff ℝ n (kmtBump : ℝ → ℝ) := ContDiffBump.contDiff kmtBump
  have h2 : ContDiff ℝ n (Complex.ofRealCLM : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  have h3 : kmtEta = (Complex.ofRealCLM : ℝ → ℂ) ∘ (kmtBump : ℝ → ℝ) := rfl
  rw [h3]
  exact h2.comp h1

/-- The KMT cutoff has compact support (it vanishes off `[-1,1]`). -/
theorem bfm_hasCompactSupport_kmtEta : HasCompactSupport kmtEta := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc (fun x hx => ?_)
  simp only [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  refine kmtEta_zero ?_
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-- The `d`-scaled bump is smooth. -/
theorem contDiff_bfmBump (d : ℕ) : ContDiff ℝ 2 (bfmBump d) := by
  have h1 : ContDiff ℝ 2 (fun x : ℝ => kmtEta x) := bfm_contDiff_kmtEta 2
  have h2 : ContDiff ℝ 2 (fun x : ℝ => kmtEta ((2 : ℝ) ^ d * x)) :=
    (bfm_contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)
  have h3 : bfmBump d
      = (fun x : ℝ => kmtEta x) - (fun x : ℝ => kmtEta ((2 : ℝ) ^ d * x)) := rfl
  rw [h3]
  exact h1.sub h2

/-- The `d`-scaled bump has compact support (both `η`-terms vanish off `[-1,1]`). -/
theorem hasCompactSupport_bfmBump (d : ℕ) : HasCompactSupport (bfmBump d) := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc (fun x hx => ?_)
  simp only [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  have hx1 : 1 ≤ |x| := by
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have h1 : kmtEta x = 0 := kmtEta_zero hx1
  have h2 : kmtEta ((2 : ℝ) ^ d * x) = 0 := by
    refine kmtEta_zero ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ d * |x| :=
          mul_le_mul (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ (2 : ℝ) ^ d) hx1
            (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  simp only [bfmBump, h1, h2, sub_zero]

end

end Work.KMTPlan.A6
