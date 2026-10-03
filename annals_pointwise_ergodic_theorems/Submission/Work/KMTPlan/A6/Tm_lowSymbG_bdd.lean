import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallIngredients

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Pointwise boundedness of `Tm` at the small-scale `g`-side slices of the low case

This is the `g`-side companion of `Work.KMTPlan.A6.Tm_lowSymbF_bdd` (proved in
`Submission/Work/KMTPlan/A6/Tm_lowSymbF_bdd.lean`).  For each index `k` the symbol
`lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k` is either `0` (at the anchor `k = 0`, and off the admissible
set `lowSmallSet`) or the modulated `d`-fold bump `φ̃_{⌊a k⌋,t}` of the paper's §6 (with
`d = P.natDegree`); in both cases `Tm ρ l₂ · g` is a bounded function of `y`, because the symbol is
a `C²` compactly supported function, so the kernel of the Ionescu--Wainger multiplier is in `ℓ¹`
(`Tm_bdd_of_l2`), and convolution with an `ℓ¹` kernel maps `ℓ²` to `ℓ^∞`.
-/

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-- **The modulated `d`-fold bump `φ̃_{N,t}` is a legitimate `ℓ²`-to-`ℓ^∞` symbol for an
*arbitrary* real `t`.**  Companion of `exists_varphiNt_bound`: smoothness and compact support hold
for every `t` (`contDiff_varphitildeNt_local`, `hasCompactSupport_varphitildeNt_local`), and the
bound `S` on the `L¹` norms of `φ̃_{N,t}` and of `(φ̃_{N,t})''` is allowed to depend on `t`, which
is all the pointwise bound on `Tm` needs. -/
theorem exists_varphitildeNt_bound (P : Polynomial ℤ) (N k₂ : ℕ) (t : ℝ) :
    ∃ S : ℝ, 0 ≤ S ∧
      ContDiff ℝ 2 (varphitildeNt P P.natDegree N k₂ t) ∧
      HasCompactSupport (varphitildeNt P P.natDegree N k₂ t) ∧
      (∫ y : ℝ, ‖varphitildeNt P P.natDegree N k₂ t y‖) ≤ S ∧
      (∫ y : ℝ, ‖iteratedDeriv 2 (varphitildeNt P P.natDegree N k₂ t) y‖) ≤ S := by
  refine ⟨(∫ y : ℝ, ‖varphitildeNt P P.natDegree N k₂ t y‖)
      + (∫ y : ℝ, ‖iteratedDeriv 2 (varphitildeNt P P.natDegree N k₂ t) y‖) + 1,
    ?_, contDiff_varphitildeNt_local P P.natDegree N k₂ t,
    hasCompactSupport_varphitildeNt_local P P.natDegree N k₂ t, ?_, ?_⟩
  · have h1 : 0 ≤ ∫ y : ℝ, ‖varphitildeNt P P.natDegree N k₂ t y‖ :=
      integral_nonneg fun y => norm_nonneg _
    have h2 : 0 ≤ ∫ y : ℝ, ‖iteratedDeriv 2 (varphitildeNt P P.natDegree N k₂ t) y‖ :=
      integral_nonneg fun y => norm_nonneg _
    linarith
  · have h2 : 0 ≤ ∫ y : ℝ, ‖iteratedDeriv 2 (varphitildeNt P P.natDegree N k₂ t) y‖ :=
      integral_nonneg fun y => norm_nonneg _
    linarith
  · have h1 : 0 ≤ ∫ y : ℝ, ‖varphitildeNt P P.natDegree N k₂ t y‖ :=
      integral_nonneg fun y => norm_nonneg _
    linarith

/-- **Pointwise boundedness of `Tm` at the small-scale `g`-side slices of the low case.**

For each index `k` the symbol `lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k` is either `0` (at `k = 0`, and
off the admissible set `lowSmallSet`) or the modulated `d`-fold bump
`φ̃_{⌊a k⌋,t}` (`d = P.natDegree`).  In both cases `Tm ρ l₂ · g` is a bounded function of `y`:

* in the degenerate case the symbol vanishes, so the multiplier vanishes
  (`Work.KMTPlan.A6.Tm_zero`);
* otherwise `Tm_bdd_of_l2` bounds `Tm ρ l₂ φ̃ g` pointwise by `C · ‖g‖_{ℓ²}`, since
  `φ̃ = φ̃_{⌊a k⌋,t}` is a `C²` compactly supported symbol with finite `L¹` norms of itself and of
  its second derivative (`exists_varphitildeNt_bound`). -/
theorem Tm_lowSymbG_bdd (P : Polynomial ℤ) (ρ : ℝ) (l₁ : ℕ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    ∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ,
      ‖Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k) g y‖ ≤ D := by
  intro k
  obtain ⟨S, hSnn, hcd, hcs, hA, hB⟩ := exists_varphitildeNt_bound P (Nat.floor (a k)) k₂ t
  by_cases hk0 : k = 0
  · -- the symbol vanishes at the anchor `k = 0`
    have hs : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
      funext ξ; simp [lowSymbG, hk0]
    refine ⟨0, fun y => ?_⟩
    rw [hs, Tm_zero ρ l₂ g hg]
    simp
  · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
    · -- the symbol is the modulated `d`-fold bump `φ̃_{⌊a k⌋,t}`
      have hs : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k
          = varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t := by
        funext ξ; simp [lowSymbG, hk0, hls]
      obtain ⟨C, _hCnn, hC⟩ := Tm_bdd_of_l2 ρ l₂ S hSnn
      refine ⟨C * Real.sqrt (∑' j : ℤ, ‖g j‖ ^ 2), fun y => ?_⟩
      rw [hs]
      exact hC (varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t) hcd hcs hA hB g hg y
    · -- the symbol vanishes off the admissible set
      have hs : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
        funext ξ; simp [lowSymbG, hk0, hls]
      refine ⟨0, fun y => ?_⟩
      rw [hs, Tm_zero ρ l₂ g hg]
      simp

end

end Work.KMTPlan.A6
