import Mathlib

/-!
# `Work.EKLC6Core.condExpKernel_invariants_T`

For a self-map `T` of a standard Borel space `X` with a finite measure `μ`, the conditional
measure

`x ↦ ν_x := ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x`

of `μ` with respect to the σ-algebra of `T`-invariant measurable sets is `T`-invariant:

`ν_{T x} = ν_x` for **every** `x : X` (not merely for `μ`-a.e. `x`).

## The argument

The kernel `condExpKernel μ m` is by construction a `Kernel[m] X X`: its first variable is
*measurable with respect to the sub-σ-algebra* `m` (this is part of the `Kernel` structure and is
exposed as `ProbabilityTheory.measurable_condExpKernel`).  Hence for each fixed measurable
`A : Set X` the function `y ↦ (condExpKernel μ m y) A` is constant on the *measurable atoms* of the
σ-algebra `m`, by `ProbabilityTheory.Kernel.apply_congr_of_mem_measurableAtom` (the proof of which
only uses that the two points lie in the same atom, since `ℝ≥0∞` has measurable singletons).

For `m = MeasurableSpace.invariants T` the atoms are `T`-invariant: by definition a set `s` is
`(invariants T)`-measurable iff it is measurable and `T ⁻¹' s = s` (see
`MeasurableSpace.measurableSet_invariants`), so

`x ∈ s ↔ T x ∈ T ⁻¹' s ↔ T x ∈ s`,

i.e. `T x` and `x` lie in exactly the same `(invariants T)`-measurable sets.  Therefore
`T x ∈ measurableAtom x` and `Kernel.apply_congr_of_mem_measurableAtom` applied to
`κ = condExpKernel μ (invariants T)` gives `κ (T x) = κ x`.

Note that neither the measurability of `T` nor its measure preservation is used: the statement
holds for an arbitrary self-map, and (through `MeasurableSpace.invariants`) it says that the
conditional measures on the invariant σ-algebra are automatically equivariant.
-/

namespace Work.EKLC6Core

-- `hT` and `hmp` are part of the requested signature but are not needed for the argument.
set_option linter.unusedVariables false in
theorem condExpKernel_invariants_T {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ] (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) (x : X) : ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) (T x) = ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x := by
  -- `T x` and `x` lie in the same atom of the invariant σ-algebra.
  have hmem : T x ∈ @measurableAtom X (MeasurableSpace.invariants T) x := by
    simp only [measurableAtom, Set.mem_iInter]
    intro s hxs hs
    have hinv : T ⁻¹' s = s :=
      (MeasurableSpace.measurableSet_invariants (f := T)).mp hs |>.2
    have h2 : x ∈ T ⁻¹' s ↔ T x ∈ s := Iff.rfl
    rw [hinv] at h2
    exact h2.mp hxs
  -- the conditional kernel is measurable w.r.t. its first argument's σ-algebra.
  exact ProbabilityTheory.Kernel.apply_congr_of_mem_measurableAtom
    (κ := ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T)) hmem

end Work.EKLC6Core
