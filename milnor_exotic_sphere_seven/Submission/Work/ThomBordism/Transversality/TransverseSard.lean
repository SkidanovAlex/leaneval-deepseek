import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Regular values of a map on a manifold with boundary

`IsTransverseAt X I F x` (`Basic.lean`) says: if `F x` lies on the core then `Φ ∘ F` is a
submersion at `x`.  Read on the composite `G = Φ ∘ F` alone, this is exactly the statement that
**`0` is a regular value of `G`** — and the natural vocabulary for the perturbation argument of the
homotopy theorem (§9.2 of the `README.md`) is the chart-free one: a point `t` is a regular value of
`G` if `G` is a submersion at every point of the level set `G ⁻¹' {t}`.  Since
`Manifold.IsSubmersionAt` is a chart-based (hence chart-independent) condition, this is a property of
the *map* `G`.

The measure-theoretic content of the perturbation argument is that for a `C^∞` map `G : M → ℝ^k`
which is a submersion on `G ⁻¹' {0}`, and a nonnegative smooth `χ : M → ℝ` vanishing near `∂M`, the
set of parameters `t` for which `0` is **not** a regular value of `x ↦ G x - χ x • t` has measure
zero.  This is the manifold-level form of `Sard.sardParametric` (`Sard/sardParametric.lean`), and it
is the analytic step of the transversality homotopy theorem.

## Main definitions

* `Work.ThomBordism.Transversality.IsRegularValue`

## Main results

* `isTransverse_iff_isRegularValue` — `IsTransverse` is `IsRegularValue` of the composite;
* `isRegularValue_of_avoid`, `isRegularValue_congr` — elementary API.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality

noncomputable section

variable {n k : ℕ}

/-- **`t` is a regular value of `G : M → ℝ^k`**: `G` is a submersion at every point of the level set
`G ⁻¹' {t}`.  (`Manifold.IsSubmersionAt` is the chart-based form of submersivity, so this is a
property of the map and not of a chart.) -/
def IsRegularValue {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] {k : ℕ} (G : M → EuclideanSpace ℝ (Fin k))
    (t : EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ x : M, G x = t → IsSubmersionAt I (𝓡 k) ∞ G x

theorem isRegularValue_def {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] {k : ℕ} {G : M → EuclideanSpace ℝ (Fin k)}
    {t : EuclideanSpace ℝ (Fin k)} :
    IsRegularValue I G t ↔ ∀ x : M, G x = t → IsSubmersionAt I (𝓡 k) ∞ G x := Iff.rfl

/-- **Transversality to the core is regularity of the composite**: `F` is transverse to the core of
`X` exactly when `0` is a regular value of `Φ ∘ F`. -/
theorem isTransverse_iff_isRegularValue {E' : Type*} {H : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] {X : CoreTarget n k} {F : M → X.E} :
    IsTransverse X I F ↔ IsRegularValue I (fun y => X.Φ (F y)) 0 := by
  simp only [isTransverse_def, isTransverseAt_def, isRegularValue_def]

/-- A value which is not attained is regular. -/
theorem isRegularValue_of_avoid {E' : Type*} {H : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} {G : M → EuclideanSpace ℝ (Fin k)}
    {t : EuclideanSpace ℝ (Fin k)} (h : ∀ x : M, G x ≠ t) : IsRegularValue I G t :=
  fun x hx => absurd hx (h x)

/-- `IsRegularValue` only depends on the map. -/
theorem isRegularValue_congr {E' : Type*} {H : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} {G G' : M → EuclideanSpace ℝ (Fin k)}
    {t : EuclideanSpace ℝ (Fin k)} (h : G = G') :
    IsRegularValue I G t ↔ IsRegularValue I G' t := by
  subst h; rfl

end

end Work.ThomBordism.Transversality
