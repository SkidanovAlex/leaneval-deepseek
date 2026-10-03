/-
# The endpoint exponent of the wiring of `lacunaryBumpVarEstimate` (item 1)

The exponent upgrade of `Work.KMTAreas.A7.lacunaryBumpVarEstimate` runs the Ionescu–Wainger
endpoint bound (`Work.KMTAreas.A7.opArc_iwArithFreqs_endpoint`, exponent `2r`) at a single even
exponent `2k₀` and then reaches the target exponent `p ∈ (1,∞)` and its Hölder dual `p' = p/(p-1)`
by Riesz–Thorin interpolation between `2` and `2k₀`
(`Work.Analysis.IWMultiplier.IWLqBound_interpolation`) and, for `p < 2`, by the discrete
adjoint duality (`Work.Analysis.IWMultiplier.Dual`).

This file isolates the arithmetic of that step: the choice `k₀ := max 2 (iwR p)` of
`Work.BourgainPlan.Maximal.iwR`, with `2 k₀ ≥ max p (p/(p-1))`.  (The same estimate is used
inside `Work.BourgainPlan.Maximal.iwSupersetBound_proof`.)
-/
import Mathlib
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

/-- **The endpoint exponent of the wiring.**  For every real exponent `p > 1` there is an integer
`k₀ ≥ 2` with `2 k₀ ≥ p` and `2 k₀ ≥ p / (p - 1)`, so that both `p` and its Hölder dual lie in the
interpolation range `[2, 2 k₀]` (and `p` is below `2` exactly when it is reached by duality from
`p' ∈ [2, 2 k₀]`). -/
theorem exists_endpoint_exponent (p : ℝ) (hp : 1 < p) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ p ≤ 2 * (k₀ : ℝ) ∧ p / (p - 1) ≤ 2 * (k₀ : ℝ) := by
  refine ⟨max 2 (max ⌈p / 2⌉₊ ⌈(p / (p - 1)) / 2⌉₊), le_max_left _ _, ?_, ?_⟩
  · have h1 : ((⌈p / 2⌉₊ : ℕ) : ℝ) ≤ ((max 2 (max ⌈p / 2⌉₊ ⌈(p / (p - 1)) / 2⌉₊) : ℕ) : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : p / 2 ≤ ((⌈p / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  · have h1 : ((⌈(p / (p - 1)) / 2⌉₊ : ℕ) : ℝ)
        ≤ ((max 2 (max ⌈p / 2⌉₊ ⌈(p / (p - 1)) / 2⌉₊) : ℕ) : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _)
    have h2 : (p / (p - 1)) / 2 ≤ ((⌈(p / (p - 1)) / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith

end Work.KMTAreas.A7

/-- **The weight arithmetic of the target.**  With the loss exponent `A := 1`, the contract's
weight `lossWeight 1 ρ l₁ l₂ k₁ k₂ = (1+L)·2^{ρL}` (`L = lmaxR l₁ l₂ k₁ k₂`) dominates the
`(1 + k₁)` loss produced by the shifted Calderón–Zygmund theorem: `k₁ ≤ L` because `k₁` is one of
the four parameters defining `lmax`, and `2^{ρL} ≥ 1` (with `ρ ≥ 0`).

Consequently every factor `(1+k₁)` occurring in the wiring can be absorbed into the target's right
hand side `ofReal (lossWeight A ρ l₁ l₂ k₁ k₂)` with `A = 1`, leaving only a `ρ`- and
`p`-dependent constant (which `C : NNReal → NNReal` may carry). -/
theorem one_add_k₁_le_lossWeight {ρ : ℝ} (_hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 + (k₁ : ℝ)) ≤ Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ := by
  have hL : (k₁ : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
    have h : (k₁ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    exact_mod_cast h
  have hLnn : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
    have h : (0 : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
      le_trans (le_trans (by exact_mod_cast Nat.zero_le k₁) (le_max_left _ _)) (le_max_right _ _)
    exact_mod_cast h
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hone : (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ (1 : ℝ)
      = 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := Real.rpow_one _
  rw [Work.KMTAreas.A7.lossWeight, hone]
  calc (1 + (k₁ : ℝ)) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by linarith
    _ ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
          * 2 ^ (1 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
        le_mul_of_one_le_right (by linarith) h2
