import Mathlib
import Submission.Work.EKLC7.Defs

/-!
# `Work.EKLC7.SmulMS` — translating a σ-algebra and a set along the action

To exploit the `condexp` field of `IsLeafwise` at *two* points related by `u ∈ U`, we translate a
plaque algebra `(Z, m)` along the point transformation `R_u : y ↦ u • y`:

* `smulSt u Z = R_u '' Z` — the carrier;
* `smulMS u m = {R_u B : B ∈ m}` — the σ-algebra, i.e. the translate of `m` by `u`.

**Convention warning.** In the pinned Mathlib the `MeasurableSet'` field of `MeasurableSpace.comap`
is `fun s => ∃ s' ∈ m, f ⁻¹' s' = s`, i.e. `comap f m = {f ⁻¹' s' : s' ∈ m}`.  Hence the translate
`{R_u B : B ∈ m}` is `MeasurableSpace.comap R_u⁻¹ m`, **not** `comap R_u m`; with the latter,
`atom (comap R_u m) (u • x)` would be `R_u⁻¹ '' atom m (u • u • x)` instead of `R_u '' atom m x`.
The definition below uses `comap R_u⁻¹ m`, so that the statements of `Work.EKLC7.atom_smulMS`,
`Work.EKLC7.isPlaqueAlgebra_smulMS` and `Work.EKLC7.shape_smulMS` are the ones displayed here.

`MAlg X` wraps a σ-algebra in a structure: a bare local variable `m : MeasurableSpace X` of class
type is captured by type-class search, which makes statements mentioning `Measure.map` fail to
elaborate ("synthesized type class instance is not definitionally equal ...").

The measure-theoretic companion is `Work.EKLC7.restrict_smulSt`: for `IsUInvariant μ U` and
`u ∈ U`, `μ.restrict (smulSt u Z)` is the image of `μ.restrict Z` under `R_u`.  This is where the
hypothesis `IsUInvariant μ U` enters the proof of the `(U4)` direction `IsUInvariant → a.e. Haar`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-- A σ-algebra wrapped in a structure (so that it is not captured by type-class search when it
occurs as a local hypothesis in a statement mentioning `Measure.map`/`Measure X₃`). -/
structure MAlg (X : Type*) where
  m : MeasurableSpace X

/-- The translate of a σ-algebra along the point transformation `y ↦ u • y`. -/
abbrev smulMS (u : SL3) (m : MeasurableSpace X3) : MeasurableSpace X3 :=
  MeasurableSpace.comap (fun y : X3 => u⁻¹ • y) m

/-- The translate of a set along the point transformation `y ↦ u • y`. -/
abbrev smulSt (u : SL3) (Z : Set X3) : Set X3 := (fun y : X3 => u • y) '' Z

/-- Membership in a translated set. -/
theorem smulSt_mem {u : SL3} {Z : Set X3} {y : X3} : y ∈ smulSt u Z ↔ u⁻¹ • y ∈ Z := by
  rw [smulSt]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have h : u • z = y := hzy
    rw [← h, inv_smul_smul]
    exact hz
  · intro h
    exact ⟨u⁻¹ • y, h, by show u • (u⁻¹ • y) = y; rw [smul_inv_smul]⟩

/-- The degree-`1` action is injective. -/
theorem smul_injective (u : SL3) : Function.Injective (fun y : X3 => u • y) :=
  fun a b h => by simpa using congrArg (fun t : X3 => u⁻¹ • t) h

end Work.EKLC7
