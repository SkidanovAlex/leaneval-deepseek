import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Helpers
import Submission.SelCore
import Submission.Deep
import Submission.Chain12
import Submission.Ratio
import Submission.BinomOne
import Submission.Thm57p
import Submission.Binom
import Submission.Binom2
import Submission.Final12
import Submission.PConv
import Submission.The13
import ChallengeDeps

/-!
# Main Statements from On a conjecture of Talagrand on selector processes and a consequence
# on positive empirical processes

We formalise the statements of the main results from J. Park and H. T. Pham,
`On a conjecture of Talagrand on selector processes and a consequence on positive empirical
processes`, Annals of Math, 199 (3) 2024.
-/


namespace Submission

open _root_.SupremumOfSelectorProcesses
set_option autoImplicit false

namespace SupremumOfSelectorProcesses

open MeasureTheory ProbabilityTheory Measure unitInterval Finset

open scoped NNReal ENNReal

/-- The constant `L` of Theorem 1.2. -/
noncomputable def L₂ : ℝ≥0 := Final12.L2

/-- The constant of Theorem 1.2 is positive. -/
theorem L₂_pos : L₂ > 0 := by
  unfold L₂ Final12.L2
  positivity

open Classical in
theorem theorem_1_2 (p : I) (hp₀ : 0 < p) (hp₁ : p < 1) (X : Type*) [Fintype X] (Λ : Set (X → ℝ≥0))
    (hE₀ : 0 < 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p])
    (hE : 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] < ∞) :
    IsSmall p {s : Set X | ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) ≥
        L₂ * 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p]} := by
  classical
  have hE₀' : 0 < Final12.mu p Λ := by
    simpa [Final12.mu, Final12.bigSup] using hE₀
  have hE' : Final12.mu p Λ < ∞ := by
    simpa [Final12.mu, Final12.bigSup] using hE
  let 𝓕 : Set (Set X) := {s : Set X | Final12.bigSup Λ s ≥ (Final12.L2 : ℝ≥0∞) * Final12.mu p Λ}
  have hF : {s : Set X | ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) ≥
        L₂ * 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p]} = 𝓕 := by
    ext s
    constructor
    · intro hs
      simpa [𝓕, Final12.bigSup, Final12.mu, L₂] using hs
    · intro hs
      simpa [𝓕, Final12.bigSup, Final12.mu, L₂] using hs
  have hsmall := Final12.selector_p_small p hp₀ hp₁ Λ hE₀' hE'
  rw [hF]
  exact PConv.pSmall_imp_IsSmall p 𝓕 hsmall

/-- The constant `L` of Theorem 1.3. -/
noncomputable def L₃ : ℝ≥0 := L3v

/-- The constant of Theorem 1.3 is positive. -/
theorem L₃_pos : L₃ > 0 := by
  unfold L₃
  exact L3v_pos

open Classical in
theorem theorem_1_3 (N : ℕ) (N_pos : N > 0) (𝕋 : Type*) (t𝕋 : TopologicalSpace 𝕋)
    (p𝕋 : PolishSpace 𝕋)
    (m𝕋 : MeasurableSpace 𝕋) (b𝕋 : BorelSpace 𝕋) (ν : Measure 𝕋) (hν : IsProbabilityMeasure ν)
    (Ω : Type*) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (Y : Fin N → Ω → 𝕋)
    (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
    (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕)
    (hZ₀ : 0 < 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]) (hZ : 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] < ∞) :
    ∃ 𝓒 : Finset ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}),
      {ω | ⨆ f ∈ 𝓕, Z N Y f ω ≥ L₃ * 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]} ⊆ ⋃ c ∈ 𝓒, {ω | c.2 ≤ Z N Y c.1 ω}
      ∧ ∑ c : 𝓒, P {ω | c.val.2 ≤ Z N Y c.val.1 ω} ≤ 2⁻¹ := by
  classical
  simpa [L₃] using (discretization_main N N_pos 𝕋 t𝕋 p𝕋 m𝕋 b𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν 𝓕 h𝓕 hZ₀ hZ)

end SupremumOfSelectorProcesses

end Submission
