import Mathlib
import Submission.Work.EKLC6Core.invariant_hull
import Submission.Work.EKLC6Core.fiber_inv_finite

/-!
# `Work.EKLC6Core.quasiErgodic_of_trivial_invariants`

The conditional measures `κ x = condExpKernel μ (invariants T) x` of `μ` over the σ-algebra of
`T`-invariant sets are *quasi-ergodic* for `T`, granted that they are trivial on that σ-algebra
almost everywhere:

> if, for `μ`-a.e. `x`, every `invariants T`-measurable set `A` satisfies `κ x A = 0` or
> `κ x Aᶜ = 0`, then for `μ`-a.e. `x` every *measurable* set `E` with `T ⁻¹' E =ᵐ[κ x] E`
> satisfies `κ x E = 0` or `κ x Eᶜ = 0`.

## The argument

Fix such an `x` (a.e.), write `ν = κ x`, and let `E` be measurable with `T ⁻¹' E =ᵐ[ν] E`.

* `ν` is `T`-invariant, i.e. `MeasurePreserving T ν ν` (`Work.EKLC6Core.fiber_inv_finite`, the
  finite-measure form of the invariance of the conditional measures of the invariant σ-algebra).
* `Work.EKLC6Core.invariant_hull` applied to `ν` and `E` produces a *strictly* `T`-invariant
  measurable set `B` with `ν (E △ B) = 0`.
* `B` is `invariants T`-measurable, so the hypothesis gives `ν B = 0` or `ν Bᶜ = 0`.
* Since `E △ B = Eᶜ △ Bᶜ` is `ν`-null, the same dichotomy holds for `E`.

No countability of `E` is needed in the last step: `invariant_hull` already produces the
simultaneous hull `B` for the single set `E` in hand.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Work.EKLC6Core

/-- If the symmetric difference of `A` and `B` is `ν`-null, then `A` and `B` have the same
`ν`-measure. -/
private lemma measure_eq_of_symmDiff_eq_zero {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {A B : Set X} (h : ν (A \ B ∪ (B \ A)) = 0) : ν A = ν B :=
  measure_congr ((ae_eq_set).mpr
    ⟨measure_mono_null Set.subset_union_left h, measure_mono_null Set.subset_union_right h⟩)

theorem quasiErgodic_of_trivial_invariants {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ] (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) (hE : ∀ᵐ x ∂μ, ∀ A : Set X, @MeasurableSet X (MeasurableSpace.invariants T) A → (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) A = 0 ∨ (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) Aᶜ = 0) : ∀ᵐ x ∂μ, ∀ E : Set X, MeasurableSet E → T ⁻¹' E =ᵐ[ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x] E → (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) E = 0 ∨ (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) Eᶜ = 0 := by
  -- the conditional measures are `T`-invariant, a.e.
  filter_upwards [fiber_inv_finite μ T hT hmp, hE] with x hinvx hEx
  intro E hEmeas hEae
  -- the strictly invariant hull of `E`
  obtain ⟨B, hBmeas, hBinv, hBnull⟩ := invariant_hull
    (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T hT hinvx hEmeas hEae
  have hBJ : @MeasurableSet X (MeasurableSpace.invariants T) B :=
    (MeasurableSpace.measurableSet_invariants (f := T)).mpr ⟨hBmeas, hBinv⟩
  rcases hEx B hBJ with hB0 | hBc0
  · -- `ν B = 0`
    left
    exact (measure_eq_of_symmDiff_eq_zero hBnull).trans hB0
  · -- `ν Bᶜ = 0`; note `Eᶜ △ Bᶜ = E △ B`
    right
    have hsymm : (Eᶜ \ Bᶜ ∪ (Bᶜ \ Eᶜ)) = (E \ B ∪ (B \ E)) := by
      ext y; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff]; tauto
    have hnull' : (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Eᶜ \ Bᶜ ∪ (Bᶜ \ Eᶜ)) = 0 := by rw [hsymm]; exact hBnull
    exact (measure_eq_of_symmDiff_eq_zero hnull').trans hBc0

end Work.EKLC6Core
