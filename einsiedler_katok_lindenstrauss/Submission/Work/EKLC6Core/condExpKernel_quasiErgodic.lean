import Mathlib
import Submission.Work.EKLC6Core.invariant_hull
import Submission.Work.EKLC6Core.famIndicator
import Submission.Work.EKLC6Core.fiber_inv_finite
import Submission.Work.EKLC6Core.condExpKernel_invariants_T
import Submission.Work.EKLC6Core.quasiErgodic_of_trivial_invariants
import Submission.Work.EKLC6Core.famIndicator_dense
import Submission.Work.EKLC6Core.exists_countable_piSystem_generating
import Submission.Work.EKLC6Core.tendsto_birkhoffAverage_condExp
import Submission.Work.EKLC6Core.ae_tendsto_birkhoff_condExpKernel
import Submission.Work.EKLC6Core.trivial_of_birkhoff_approx

/-!
# `Work.EKLC6Core.condExpKernel_quasiErgodic`

Target: for a measure-preserving map `T` of a standard Borel probability space `(X, μ)`, the
conditional measure `ν_x = condExpKernel μ (MeasurableSpace.invariants T) x` is, for `μ`-a.e. `x`,
quasi-ergodic for `T`: every measurable `E` with `T ⁻¹' E =ᵐ[ν_x] E` satisfies
`ν_x E = 0` or `ν_x Eᶜ = 0`.

The key point is the ergodic decomposition theorem: for `μ`-a.e. `x`, `ν_x` is *ergodic*, i.e.
`ν_x A ∈ {0,1}` for every `T`-invariant measurable `A`.  This is proved here from the mean ergodic
theorem in `L²(μ)` (von Neumann), transferred to each `ν_x` via the defining identity
`∫ f ∂ν_x = μ[f | invariants T] x` of the conditional kernel.

## Structure of the argument

* `Work.EKLC6Core.exists_countable_piSystem_generating`: a countable π-system `S` of measurable
  sets generating the σ-algebra (on a standard Borel space).
* `Work.EKLC6Core.famIndicator S c`: the countable family of rational indicator combinations of `S`.
* `Work.EKLC6Core.famIndicator_dense`: that family is dense in `L²(ν)` for every probability
  `ν`.
* `Work.EKLC6Core.tendsto_birkhoffAverage_condExp`: **von Neumann's mean ergodic theorem in `L²(μ)`**
  (built on Mathlib's Hilbert space mean ergodic theorem).
* `Work.EKLC6Core.ae_tendsto_birkhoff_condExpKernel`: the a.e.-in-`x` transfer of that statement to
  the conditional measures `ν_x`, using `∫ h ∂ν_x = μ[h|E] x`.
* `Work.EKLC6Core.trivial_of_birkhoff_approx`: the abstract Hilbert-space step: if the Birkhoff
  averages of every member of a countable `L²`-dense family approximate its mean in `L²(ν)`, then
  `T`-invariant sets are `ν`-trivial.
* `condExpKernel_invariants_trivial` below assembles these; `quasiErgodic_of_trivial_invariants`
  (`Work.EKLC6Core.quasiErgodic_of_trivial_invariants`) is the final reduction to the target.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal
open Filter

namespace Work.EKLC6Core

/-- **The conditional measure of an invariant set is its indicator.**
For `A` measurable in the invariant σ-algebra `MeasurableSpace.invariants T` of a
measure-preserving `T`, the conditional measure `condExpKernel μ (invariants T) x` of `A` equals
`1_A(x)` for `μ`-a.e. `x`.  In particular it is `0` or `1`. -/
theorem condExpKernel_invariants_apply {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) {A : Set X} (hA : MeasurableSet[MeasurableSpace.invariants T] A) :
    ∀ᵐ x ∂μ, (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) A
      = A.indicator (fun _ => (1 : ENNReal)) x := by
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace X) :=
    MeasurableSpace.invariants_le T
  have hAm : MeasurableSet A := hm A hA
  have hmeas : Measurable[MeasurableSpace.invariants T] (A.indicator (fun _ => (1 : ℝ))) :=
    Measurable.indicator measurable_const hA
  have hint : MeasureTheory.Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (MeasureTheory.integrable_const (1 : ℝ)).indicator hAm
  have h1 : μ[(A.indicator (fun _ => (1 : ℝ)))|MeasurableSpace.invariants T]
      = (A.indicator (fun _ => (1 : ℝ))) :=
    MeasureTheory.condExp_of_stronglyMeasurable hm hmeas.stronglyMeasurable hint
  have h2 := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ)
      (m := MeasurableSpace.invariants T) hm hint
  filter_upwards [h2] with x hx2
  have key : (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x).real A
      = A.indicator (fun _ => (1 : ℝ)) x :=
    calc (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x).real A
        = ∫ y, A.indicator (fun _ => (1 : ℝ)) y
            ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
          (MeasureTheory.integral_indicator_one hAm).symm
      _ = (μ[(A.indicator (fun _ => (1 : ℝ)))|MeasurableSpace.invariants T]) x := hx2.symm
      _ = A.indicator (fun _ => (1 : ℝ)) x := congrFun h1 x
  rw [MeasureTheory.Measure.real_def] at key
  have : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.isProbabilityMeasure x
  have hne : (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) A ≠ ⊤ :=
    measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hne, key]
  by_cases h : x ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- **The ergodic decomposition of `μ` on the invariant σ-algebra.**
For `μ`-a.e. `x` the conditional measure `ν_x = condExpKernel μ (invariants T) x` is `0`-`1` valued
on the invariant σ-algebra; equivalently, `ν_x` is ergodic with respect to `T`. -/
theorem condExpKernel_invariants_trivial {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, ∀ A : Set X, MeasurableSet[MeasurableSpace.invariants T] A →
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) A = 0 ∨
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) Aᶜ = 0 := by
  classical
  obtain ⟨S, hS, hπ, hU, hgen⟩ := exists_countable_piSystem_generating (X := X)
  -- (1) the a.e.-in-`x` Birkhoff approximation, for every member of the countable family.
  have hkey : ∀ᵐ x ∂μ, ∀ c : ℕ →₀ ℚ, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      ∫ y, (birkhoffAverage ℝ T (famIndicator S c) n y
          - ∫ z, famIndicator S c z
              ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x))^2
        ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) < ε := by
    rw [MeasureTheory.ae_all_iff]
    exact fun c => ae_tendsto_birkhoff_condExpKernel μ T hT hmp (famIndicator S c)
      (memLp_famIndicator S hS c μ)
      (tendsto_birkhoffAverage_condExp μ T hmp (famIndicator S c) (memLp_famIndicator S hS c μ))
  filter_upwards [hkey, fiber_inv_finite μ T hT hmp] with x hx hxinv
  -- (2) the abstract triviality lemma, applied to the probability `ν_x` (which is a probability
  -- measure by the global instance `IsMarkovKernel (condExpKernel μ m)`).
  have htriv : ∀ B : Set X, MeasurableSet B → T ⁻¹' B = B →
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) B = 0 ∨
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) B = 1 :=
    trivial_of_birkhoff_approx _ T hT hxinv S hS
      (fun f hf ε hε => famIndicator_dense S hS hπ hU hgen _ f hf hε) hx
  intro A hA
  obtain ⟨hAmeas, hAinv⟩ := (MeasurableSpace.measurableSet_invariants (f := T)).mp hA
  rcases htriv A hAmeas hAinv with h0 | h1
  · exact Or.inl h0
  · refine Or.inr ?_
    have hfin : (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) A ≠ ⊤ :=
      measure_ne_top _ A
    have hc := MeasureTheory.measure_compl (μ :=
      ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) hAmeas hfin
    rw [measure_univ, h1, tsub_self] at hc
    exact hc

/-- **The target.**  For `μ`-a.e. `x` the conditional measure `ν_x` is quasi-ergodic for `T`.
Immediate from `condExpKernel_invariants_trivial` (the ergodic decomposition step) and the
already-proved reduction `quasiErgodic_of_trivial_invariants`. -/
theorem condExpKernel_quasiErgodic {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, ∀ E : Set X, MeasurableSet E →
      T ⁻¹' E =ᵐ[ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x] E →
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) E = 0 ∨
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) Eᶜ = 0 := by
  exact Work.EKLC6Core.quasiErgodic_of_trivial_invariants μ T hT hmp
    (condExpKernel_invariants_trivial μ T hT hmp)

end Work.EKLC6Core
