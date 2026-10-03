import Mathlib
import Submission.Work.A3Fix.PolyEnergyDeep
import Submission.Work.A3.transitionArc_bound
import Submission.Work.A3.partialSum_power_saving_real

/-!
# `PolyEnergyBound` from the deep-shoulder input alone (Area A3)

This module takes the capstone `Work.A3.polyEnergy_bound_of_transition_and_deep` of
`Work.A3.polyEnergy_deep` and **discharges its remaining hypotheses** except the deep-shoulder
power saving:

* the complete-sum power saving `hc` — `Work.A3.completeSum_power_saving` (proved);
* the partial-sum power saving `hps` — `Work.A3.partialSum_power_saving_real` (proved);
* the transition bound `htrans` — `Work.A3.transitionArc_bound` (proved).

The two power savers come with *their own* exponents `(δ₁,C₁)`, `(δ₂,C₂)`; they are combined
into a common pair `(δ₀,C₀) = (min δ₁ δ₂, max C₁ C₂)` and the transition bound is run at that
pair.  What is left is the single arithmetic input

`(DEEP')`  `‖expSum Q N (a/q + β)‖ ≤ C₀ N^{1-θ₀}`  for `θ₀ > 0` fixed, `(a,q) = 1`,
`q ≤ N^{1/2}` (the level `γ = 1/2` of `deepArcSet`) and
`(N/q)^{d/(d+1)}/100 ≤ |β| N^d ≤ N^{d/2}/q`,

the power saving on the *deep shoulder* of the major arcs (the region where the block
sum/integral comparison underlying the transition bound fails).  This is the genuine
critical-scale Vinogradov-mean-value/BDG-type input; see `NOTES_A3_deepShoulder_SESSION.md`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The reduction of `PolyEnergyBound` to the deep-shoulder power saving.** -/
theorem polyEnergy_bound_of_deep (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {θ₀ C₀ : ℝ} (hθ₀ : 0 < θ₀) (hC₀ : 0 < C₀)
    (hdeep : ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) →
      ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100
        ≤ |β| * (N : ℝ) ^ Q.natDegree →
      |β| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) →
      ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C₀ * (N : ℝ) ^ (1 - θ₀)) :
    PolyEnergyBound Q := by
  obtain ⟨δ₁, C₁, hδ₁, hC₁, hcs⟩ := completeSum_power_saving Q hd
  obtain ⟨δ₂, hδ₂, C₂, hC₂, hps⟩ := partialSum_power_saving_real Q hd
  set δ : ℝ := min δ₁ δ₂ with hδdef
  set C : ℝ := max C₁ C₂ with hCdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hC : 0 < C := lt_max_of_lt_left hC₁
  -- monotone shrinking of the exponent, and enlarging of the constant
  have hδ_le₁ : δ ≤ δ₁ := min_le_left _ _
  have hδ_le₂ : δ ≤ δ₂ := min_le_right _ _
  have hC₁C : C₁ ≤ C := le_max_left _ _
  have hC₂C : C₂ ≤ C := le_max_right _ _
  have hcs' : ∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
      ‖completeSum Q a q‖ ≤ C * (q : ℝ) ^ (1 - δ) := by
    intro q a hq hcop
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h1 := hcs q a hq hcop
    have h2 : (q : ℝ) ^ (1 - δ₁) ≤ (q : ℝ) ^ (1 - δ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    calc ‖completeSum Q a q‖ ≤ C₁ * (q : ℝ) ^ (1 - δ₁) := h1
      _ ≤ C * (q : ℝ) ^ (1 - δ) :=
          mul_le_mul hC₁C h2 (by positivity) (le_of_lt hC)
  have hps' : ∀ (q : ℕ) (a : ℤ) (t : ℕ), 1 ≤ q → IsCoprime a (q : ℤ) → t ≤ q →
      ‖∑ r ∈ Finset.range t,
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((a : ℝ) * (((Q.eval (r : ℤ)) : ℤ) : ℝ) / (q : ℝ))))‖
      ≤ C * (q : ℝ) ^ (1 - δ) := by
    intro q a t hq hcop ht
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h1 := hps q a t hq hcop ht
    have h2 : (q : ℝ) ^ (1 - δ₂) ≤ (q : ℝ) ^ (1 - δ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    calc ‖∑ r ∈ Finset.range t,
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((a : ℝ) * (((Q.eval (r : ℤ)) : ℤ) : ℝ) / (q : ℝ))))‖
        ≤ C₂ * (q : ℝ) ^ (1 - δ₂) := h1
      _ ≤ C * (q : ℝ) ^ (1 - δ) :=
          mul_le_mul hC₂C h2 (by positivity) (le_of_lt hC)
  obtain ⟨Ctr, hCtr, htrans⟩ := transitionArc_bound Q hd hC hδ hcs' hps'
  exact polyEnergy_bound_of_transition_and_deep Q hd hδ hC hcs' hps' hθ₀ hC₀ hdeep hCtr htrans

end

end Work.A3
