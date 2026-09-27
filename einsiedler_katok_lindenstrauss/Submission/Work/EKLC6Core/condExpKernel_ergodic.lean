import Mathlib
import Submission.Work.EKLC6Core.invariant_hull
import Submission.Work.EKLC6Core.fiber_inv_finite
import Submission.Work.EKLC6Core.quasiErgodic_of_trivial_invariants
import Submission.Work.EKLC6Core.famIndicator
import Submission.Work.EKLC6Core.famIndicator_dense
import Submission.Work.EKLC6Core.exists_countable_piSystem_generating
import Submission.Work.EKLC6Core.tendsto_birkhoffAverage_condExp
import Submission.Work.EKLC6Core.ae_tendsto_birkhoff_condExpKernel
import Submission.Work.EKLC6Core.trivial_of_birkhoff_approx

/-!
# `Work.EKLC6Core.condExpKernel_ergodic`

The conditional measures `ν_x = condExpKernel μ (invariants T) x` of a measure preserving map `T`
of a standard Borel probability space are, for `μ`-a.e. `x`, **ergodic** for `T`: every measurable
`E` which is `T`-invariant `ν_x`-a.e. satisfies `ν_x E = 0` or `ν_x Eᶜ = 0`.

This is the ergodic decomposition theorem for a single measure-preserving transformation,
assembled from

* `tendsto_birkhoffAverage_condExp` — von Neumann's mean ergodic theorem in `L²(μ)`;
* `ae_tendsto_birkhoff_condExpKernel` — transfer of that statement to the conditional measures;
* `trivial_of_birkhoff_approx` — `L²` Birkhoff approximation implies ergodicity;
* `exists_countable_piSystem_generating`, `famIndicator_dense` — the countable dense family;
* `fiber_inv_finite` — the conditional measures are a.e. `T`-invariant;
* `quasiErgodic_of_trivial_invariants` — reduction of the target to triviality on the invariant
  σ-algebra.
-/

namespace Work.EKLC6Core

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

theorem condExpKernel_ergodic {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, ∀ E : Set X, MeasurableSet E →
      T ⁻¹' E =ᵐ[ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x] E →
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) E = 0 ∨
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) Eᶜ = 0 := by
  -- A countable generating π-system of the Borel σ-algebra.
  obtain ⟨S, hS, hπ, hU, hgen⟩ := exists_countable_piSystem_generating (X := X)
  -- For a.e. `x`, the Birkhoff averages of every rational indicator combination approximate the
  -- corresponding constant in `L²(ν_x)`.
  have hkey : ∀ᵐ x ∂μ, ∀ c : ℕ →₀ ℚ, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      ∫ y, (birkhoffAverage ℝ T (famIndicator S c) n y
          - ∫ z, famIndicator S c z
              ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)) ^ 2
        ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) < ε :=
    eventually_countable_forall.mpr fun c =>
      ae_tendsto_birkhoff_condExpKernel μ T hT hmp (famIndicator S c)
        (memLp_famIndicator S hS c μ)
        (tendsto_birkhoffAverage_condExp μ T hmp (famIndicator S c)
          (memLp_famIndicator S hS c μ))
  -- Hence `ν_x` is trivial on the invariant σ-algebra, for a.e. `x`.
  have hE : ∀ᵐ x ∂μ, ∀ A : Set X, @MeasurableSet X (MeasurableSpace.invariants T) A →
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) A = 0 ∨
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) Aᶜ = 0 := by
    filter_upwards [fiber_inv_finite μ T hT hmp, hkey] with x hinv hx
    intro A hA
    obtain ⟨hAm, hAi⟩ := (MeasurableSpace.measurableSet_invariants (f := T)).mp hA
    rcases trivial_of_birkhoff_approx
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T hT hinv S hS
        (fun f hf ε hε => famIndicator_dense S hS hπ hU hgen _ f hf hε)
        (fun c ε hε => hx c ε hε) A hAm hAi with h0 | h1
    · exact Or.inl h0
    · exact Or.inr ((prob_compl_eq_zero_iff hAm).mpr h1)
  exact quasiErgodic_of_trivial_invariants μ T hT hmp hE

end Work.EKLC6Core
