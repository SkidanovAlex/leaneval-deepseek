import Mathlib

/-!
# `mfderiv` congruence lemmas in their Lean v4.33 form (v4.34 port)

On v4.34 Mathlib, `Filter.EventuallyEq.mfderiv_eq` and `Filter.EventuallyEq.mfderivWithin_eq` state
the congruence with an explicit `tangentSpaceCast` in front (`mfderiv f₁ x = cast ∘L mfderiv f x`).
The cast is definitionally the identity, since every `TangentSpace I' y` is `E'`. The proofs in this
development were written against the v4.33 statements without the cast; these lemmas restore that
form.
-/

open Filter Topology

namespace Filter.EventuallyEq

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {f f₁ : M → M'} {x : M} {s : Set M}

/-- `Filter.EventuallyEq.mfderiv_eq` without the (definitionally trivial) tangent-space cast. -/
theorem mfderiv_eq_v433 (hL : f₁ =ᶠ[𝓝 x] f) :
    mfderiv I I' f₁ x = mfderiv I I' f x := by
  rw [hL.mfderiv_eq]
  ext v
  rfl

/-- `Filter.EventuallyEq.mfderivWithin_eq` without the (definitionally trivial) tangent-space
cast. -/
theorem mfderivWithin_eq_v433 (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    mfderivWithin I I' f₁ s x = mfderivWithin I I' f s x := by
  rw [hL.mfderivWithin_eq hx]
  ext v
  rfl

end Filter.EventuallyEq
