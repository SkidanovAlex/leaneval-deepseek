import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouWindow.fatouSecondDerivWideBound
import Submission.Work.FatouL1.normOneSubMulDerivLe

/-!
# FATOU-L1: the derivative defect on the unit window is `1/150`

Let `F` be a near-translation on `𝒬 = Qreg b₁ b₂` satisfying the `L¹` line bound, and let `x₀` be a
vertical line at distance `≥ 1` to the right of `b₁` and `≥ 3` to the left of `b₂` (so that the wide
strip `W = {x₀ - 1/8 < Re < x₀ + 17/8}` lies in `𝒬`).  This file proves that **some** Fatou
coordinate `Φ` of `F` satisfies

  `‖Φ' z - 1 / (F z - z)‖ ≤ 1/150`   for   `x₀ - 1/8 < Re z < x₀ + 33/32`.

## The mathematics

The point of the normalisation `1/(F z - z)`: for the exact translation `F z = z + v` the Fatou
coordinate is `z/v`, so `Φ' = 1/v` *exactly*; the statement says that for a near-translation this
holds to second order.  Indeed, the Abel relation `Φ (F z) = Φ z + 1` together with Taylor's
formula with integral remainder along the segment `[z, F z]` gives the *exact* first-order identity

  `Φ' z = 1/(F z - z) + O(‖F z - z - 1‖²)`,

and the whole segment `[z, F z]` stays in `W`: since `Re (F z - z) ≥ 31/32 > 0` and
`‖F z - z‖ ≤ 33/32`, its real part runs from `Re z > x₀ - 1/8` up to
`Re z + 33/32 < x₀ + 33/16 < x₀ + 17/8`.  The second-derivative bound `‖Φ''‖ ≤ 1/100` on `W`
(`Work.FatouWindow.fatouSecondDerivWideBound`, see below) therefore bounds the remainder:

  `‖1 - (F z - z) Φ' z‖ ≤ ‖F z - z‖² · (1/200) ≤ (33/32)²/200`,

whence `‖Φ' z - 1/(F z - z)‖ ≤ (33/32)²/(200 · 31/32) < 1/150` (the Taylor step is
`Work.FatouL1.normOneSubMulDerivLe`).

This is the window input of `Work.FatouL1.qregDerivBound`.

## Why the quantitative input is taken from re-homed modules

`Work.FatouL1.fatouCoord` is defined in `Submission/Work/FatouL1/fatouDerivSetup.lean` through the
*placeholder* `Work.FatouL1.fatouCoordExistsL1` (`Submission/Work/FatouL1/cruxTemp.lean`, a
*unfilled*), so every theorem of the `L¹` chain mentioning the canonical coordinate
(`fatouU_apriori_bound*`, `fatouMassMBound`, `fatouSecondDerivWideBound`) currently depends on
an extra placeholder axiom and fails an axiom audit.  `Submission/Work/FatouWindow/*` is a verbatim re-homing of
that chain (definitions, a priori bounds, mass bound, second-derivative bound) whose only change
is the source of the coordinate: `Work.FatouWindow.fatouCoordExistsClean`, proved from the
(axiom-clean) contract `Work.FatouCH.fatouCH`.  The mathematical content is identical, and the
re-homed statement is axiom-clean, so this file is too.
-/

open MandelDim Set
open scoped Topology

namespace Work.FatouL1

noncomputable section

theorem windowDefectBound {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂) ∧
      ∀ z : ℂ, x₀ - 1 / 8 < z.re → z.re < x₀ + 33 / 32 → ‖deriv Φ z - 1 / (F z - z)‖ ≤ 1 / 150 := by
  obtain ⟨Φ, hΦ, hΦ2⟩ := Work.FatouWindow.fatouSecondDerivWideBound hadm hF h₁ h₂
  refine ⟨Φ, hΦ, ?_⟩
  intro z hz₁ hz₂
  -- the window lies in the wide strip (`33/32 < 17/8`)
  have hzW : z ∈ wStrip x₀ := mem_wStrip.mpr ⟨hz₁, by linarith⟩
  have hzQ : z ∈ MandelDim.Qreg b₁ b₂ := wideStrip_subset_Qreg h₁ h₂ hzW
  have hΦd : DifferentiableOn ℂ Φ (wStrip x₀) := hΦ.1.mono (wideStrip_subset_Qreg h₁ h₂)
  set v : ℂ := F z - z with hv
  -- `v = F z - z` is within `1/32` of `1`
  have hFz_sub : F z - (z + 1) = v - 1 := by rw [hv]; ring
  have hv_sub_one : ‖v - 1‖ ≤ (1 : ℝ) / 32 := by
    rw [← hFz_sub]; exact (hF.1.2 z hzQ).1
  have hre_abs : |v.re - 1| ≤ (1 : ℝ) / 32 := by
    have h := Complex.abs_re_le_norm (v - 1)
    have h' : |v.re - 1| ≤ ‖v - 1‖ := by simpa using h
    exact h'.trans hv_sub_one
  have hv_re_ub : v.re ≤ 33 / 32 := by
    have h2 : v.re - 1 ≤ 1 / 32 := le_trans (le_abs_self _) hre_abs
    linarith
  have hv_re_lb : (31 : ℝ) / 32 ≤ v.re := by
    have h2 : -(1 / 32) ≤ v.re - 1 := le_trans (neg_le_neg hre_abs) (neg_abs_le _)
    linarith
  have hv_norm_lb : (31 : ℝ) / 32 ≤ ‖v‖ := by
    have h : ‖(1 : ℂ)‖ ≤ ‖v‖ + ‖v - 1‖ := by
      have := norm_sub_le v (v - 1)
      simpa using this
    rw [norm_one] at h
    linarith
  have hv_norm_ub : ‖v‖ ≤ 33 / 32 := by
    have h := abs_norm_sub_norm_le v (1 : ℂ)
    rw [norm_one] at h
    have h2 := (abs_le.mp h).2
    linarith
  have hv_ne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv_norm_lb
    norm_num at hv_norm_lb
  -- the whole segment `[z, F z]` stays in the wide strip
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, z + t • v ∈ wStrip x₀ := by
    intro t ht
    rw [mem_wStrip]
    have hre : (z + t • v).re = z.re + t * v.re := by simp
    constructor
    · rw [hre]
      have : 0 ≤ t * v.re := mul_nonneg ht.1 (by linarith)
      linarith
    · rw [hre]
      have h3 : t * v.re ≤ 33 / 32 := by
        calc t * v.re ≤ 1 * v.re := mul_le_mul_of_nonneg_right ht.2 (by linarith)
          _ = v.re := one_mul _
          _ ≤ 33 / 32 := hv_re_ub
      linarith
  have hFzW : F z ∈ wStrip x₀ := by
    have h1 := hseg 1 (by norm_num)
    have h2 : z + (1 : ℝ) • v = F z := by rw [one_smul, hv]; ring
    rwa [h2] at h1
  have hFzQ : F z ∈ MandelDim.Qreg b₁ b₂ := wideStrip_subset_Qreg h₁ h₂ hFzW
  have hAbel : Φ (z + v) = Φ z + 1 := by
    have h2 : z + v = F z := by rw [hv]; ring
    rw [h2]; exact hΦ.2.2 z hzQ hFzQ
  have h2b : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDeriv 2 Φ (z + t • v)‖ ≤ 1 / 100 :=
    fun t ht => hΦ2 _ (hseg t ht)
  -- second-order Taylor along `[z, F z]` with the Abel relation
  have hkey : ‖1 - v * deriv Φ z‖ ≤ ‖v‖ ^ 2 * ((1 / 100) / 2) :=
    normOneSubMulDerivLe (wStrip_isOpen x₀) hΦd hseg h2b hAbel
  have hnum : ‖v * deriv Φ z - 1‖ ≤ (33 / 32) ^ 2 * ((1 / 100) / 2) := by
    rw [norm_sub_rev]
    calc ‖1 - v * deriv Φ z‖ ≤ ‖v‖ ^ 2 * ((1 / 100) / 2) := hkey
      _ ≤ (33 / 32) ^ 2 * ((1 / 100) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact pow_le_pow_left₀ (norm_nonneg v) hv_norm_ub 2
  have hfin : ‖deriv Φ z - 1 / v‖ ≤ ((33 / 32) ^ 2 * ((1 / 100) / 2)) / ((31 : ℝ) / 32) := by
    have hdiv : deriv Φ z - 1 / v = (v * deriv Φ z - 1) / v := by
      field_simp
    rw [hdiv, norm_div]
    exact div_le_div₀ (by norm_num) hnum (by norm_num) hv_norm_lb
  exact hfin.trans (by norm_num)

end

end Work.FatouL1
