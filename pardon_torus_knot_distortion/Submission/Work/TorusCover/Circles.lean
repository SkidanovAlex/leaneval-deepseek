import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.Lifting

/-!
# The winding vectors of the meridian and longitude circles

The level curves of a parametrisation `psi : ℝ → ℝ → R3` generate `π₁` of the torus:

* the **meridian circle** `{x = const}`, i.e. the curve `φ ↦ psi x φ`, has winding vector
  `(0, 1)` (its lift is `φ ↦ (x, φ)`),
* the **longitude circle** `{y = const}`, i.e. the curve `θ ↦ psi θ y`, has winding vector
  `(1, 0)` (its lift is `θ ↦ (θ, y)`).

This identifies the winding vector of an arbitrary closed curve with its class in
`π₁ (range psi) ≅ ℤ²` expressed in the meridian/longitude basis, and it shows that both circles
are essential.

Main results:

* `Work.TorusCover.hasWinding_meridian`, `Work.TorusCover.hasWinding_longitude`;
* `Work.TorusCover.isEssential_meridian`, `Work.TorusCover.isEssential_longitude`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

/-- The meridian circle `φ ↦ psi x φ` (the level set `{x = const}`) has winding vector
`(0, 1)`. -/
theorem hasWinding_meridian (P : TorusParam) (x : ℝ) :
    HasWinding P.psi (fun φ => P.psi x φ) (0, 1) :=
  ⟨fun φ => (x, φ), ⟨continuous_const.prodMk continuous_id, fun _ => rfl⟩, fun φ => by
    ext <;> simp [periodShift]⟩

/-- The longitude circle `θ ↦ psi θ y` (the level set `{y = const}`) has winding vector
`(1, 0)`. -/
theorem hasWinding_longitude (P : TorusParam) (y : ℝ) :
    HasWinding P.psi (fun θ => P.psi θ y) (1, 0) :=
  ⟨fun θ => (θ, y), ⟨continuous_id.prodMk continuous_const, fun _ => rfl⟩, fun θ => by
    ext <;> simp [periodShift]⟩

/-- The meridian circle is essential. -/
theorem isEssential_meridian (P : TorusParam) (x : ℝ) :
    IsEssential P.psi (fun φ => P.psi x φ) :=
  ⟨(0, 1), by decide, hasWinding_meridian P x⟩

/-- The longitude circle is essential. -/
theorem isEssential_longitude (P : TorusParam) (y : ℝ) :
    IsEssential P.psi (fun θ => P.psi θ y) :=
  ⟨(1, 0), by decide, hasWinding_longitude P y⟩

end

end Work.TorusCover
