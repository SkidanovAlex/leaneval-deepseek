import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.integral_sq_finset_sum_of_orthogonal`

**Pythagoras for the box pairing.**  For a finite family `f` of continuous functions
`X N → ℝ` that is *pairwise orthogonal* for the box pairing
`⟨u, v⟩ = ∫_{abox N ℓ} u · v` (`ℓ > 0`), the box integral of the square of the sum is
the sum of the box integrals of the squares:

    ∫_{abox N ℓ} (Σ_{i∈s} f i)² = Σ_{i∈s} ∫_{abox N ℓ} (f i)².

## The proof

The elementary expansion `(Σᵢ fᵢ)² = Σᵢ Σⱼ fᵢ fⱼ` (`sq`, `Finset.sum_mul_sum`) turns
the left-hand side into the double integral `Σᵢ Σⱼ ∫ fᵢ fⱼ`; the two `Finset` sums may
be exchanged with the box integral because on the compact box `abox N ℓ` the products
`fᵢ fⱼ` of continuous functions are integrable
(`ContinuousOn.integrableOn_compact`, `Submission.BoseGases.abox_compact`).  In the
inner sum over `j ∈ s` only the term `j = i` survives, since every off-diagonal pairing
integral vanishes by hypothesis (`Finset.sum_eq_single`) — and that surviving term is
`∫ (f i)²`.  No positivity, measurability or smoothness beyond continuity, and no
hypothesis on `N ≥ 1`, is needed.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Pythagoras for the box pairing.**  For a finite family `f` of continuous functions
`X N → ℝ` that is pairwise orthogonal for the box pairing `⟨u,v⟩ = ∫_{abox N ℓ} u·v`
(`0 < ℓ`), the box integral of the square of the sum is the sum of the box integrals of
the squares: only the diagonal of the double sum `ΣᵢΣⱼ∫ fᵢ·fⱼ` survives. -/
lemma integral_sq_finset_sum_of_orthogonal {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ι : Type*}
    (s : Finset ι) (f : ι → Submission.BoseGases.X N → ℝ)
    (hc : ∀ i ∈ s, Continuous (f i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ x in Submission.BoseGases.abox N ℓ, f i x * f j x = 0) :
    (∫ x in Submission.BoseGases.abox N ℓ, (∑ i ∈ s, f i x) ^ 2)
      = ∑ i ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, (f i x) ^ 2 := by
  -- Integrability of every product on the (compact, finite-measure) box.
  have hint : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun x : Submission.BoseGases.X N => f i x * f j x)
        ((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) := by
    intro i hi j hj
    exact ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact N hℓ)
      ((hc i hi).mul (hc j hj)).continuousOn
  -- Expand the square and exchange integral with the double `Finset` sum.
  have hexp : (∫ x in Submission.BoseGases.abox N ℓ, (∑ i ∈ s, f i x) ^ 2)
      = ∑ i ∈ s, ∑ j ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, f i x * f j x := by
    have h1 : (fun x : Submission.BoseGases.X N => (∑ i ∈ s, f i x) ^ 2)
        = fun x => ∑ i ∈ s, ∑ j ∈ s, f i x * f j x := by
      funext x
      rw [sq, Finset.sum_mul_sum]
    rw [h1, MeasureTheory.integral_finsetSum _
      (fun i hi => MeasureTheory.integrable_finsetSum _ (fun j hj => hint i hi j hj))]
    exact Finset.sum_congr rfl fun i hi =>
      MeasureTheory.integral_finsetSum _ (fun j hj => hint i hi j hj)
  -- Only the diagonal `j = i` of the inner sum survives.
  rw [hexp]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · simp only [sq]
  · intro j hj hji
    exact horth i hi j hj (Ne.symm hji)
  · intro hcon
    exact absurd hi hcon

end Work.BoseFixB2.Sector
