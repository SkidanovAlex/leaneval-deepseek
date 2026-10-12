import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0SpectralDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.abox_integral_sq_finset_sum`

**Expansion of the box integral of a squared finite sum.**  For any finite family
`f : ι → X N → ℝ`, any coefficients `c : ι → ℝ` and any `ℓ : ℝ`, if every product
`f i · f j` (`i, j ∈ s`) is integrable on the centred `N`-particle box
`abox N ℓ ⊆ X N`, then

    ∫_{abox N ℓ} (Σ_{i∈s} c i · f i x)²  =  Σ_{i∈s} Σ_{j∈s} c i · c j · ∫_{abox N ℓ} f i x · f j x.

## Proof

Purely algebraic.  Pointwise, `sq` and `Finset.sum_mul_sum` give

    (Σ_{i∈s} c i * f i x)² = Σ_{i∈s} Σ_{j∈s} (c i * f i x) * (c j * f j x)
                           = Σ_{i∈s} Σ_{j∈s} c i * c j * (f i x * f j x),

the second step by `ring` termwise.  The two `Finset` sums commute with the box integral
(`MeasureTheory.integral_finsetSum`, twice): each summand `c i * c j * (f i * f j)` is
integrable on the box by hypothesis (`MeasureTheory.Integrable.const_mul`), so a finite sum
of them is too (`MeasureTheory.integrable_finsetSum`), and finally the constant `c i * c j`
comes out of the integral (`MeasureTheory.integral_const_mul`).

Nothing about the geometry of `abox N ℓ` (measurability, positivity of `ℓ`, finiteness of
`N`) is used: the only input is the integrability hypothesis, which for continuous `f` on
the compact box is supplied by `ContinuousOn.integrableOn_compact`.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false

theorem abox_integral_sq_finset_sum {N : ℕ} {ℓ : ℝ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → Submission.BoseGases.X N → ℝ)
    (hint : ∀ i ∈ s, ∀ j ∈ s, MeasureTheory.IntegrableOn (fun x => f i x * f j x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox N ℓ, (∑ i ∈ s, c i * f i x) ^ 2)
      = ∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ x in Submission.BoseGases.abox N ℓ, f i x * f j x) := by
  -- Integrability of each summand, as a scalar multiple of a product `f i * f j`.
  have hint' : ∀ i ∈ s, ∀ j ∈ s,
      MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => c i * c j * (f i x * f j x))
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) :=
    fun i hi j hj => (hint i hi j hj).const_mul (c i * c j)
  -- Pointwise expansion of the square.
  have hpt : (fun x : Submission.BoseGases.X N => (∑ i ∈ s, c i * f i x) ^ 2)
      = fun x => ∑ i ∈ s, ∑ j ∈ s, c i * c j * (f i x * f j x) := by
    funext x
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hpt]
  -- Exchange the outer `Finset` sum with the box integral.
  rw [MeasureTheory.integral_finsetSum _
    (fun i hi => MeasureTheory.integrable_finsetSum _ (fun j hj => hint' i hi j hj))]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- Exchange the inner `Finset` sum with the box integral.
  rw [MeasureTheory.integral_finsetSum _ (fun j hj => hint' i hi j hj)]
  -- Pull the constant `c i * c j` out of each integral.
  exact Finset.sum_congr rfl fun j hj => by
    rw [MeasureTheory.integral_const_mul]

end Work.BoseFixB1S
