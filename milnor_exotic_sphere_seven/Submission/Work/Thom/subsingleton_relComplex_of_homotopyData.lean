import Mathlib
import Submission.Work.Thom.homotopyRetractVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of `H^k(U, U ∩ A)` from a deformation of `U` into `A`

Let `U, A ⊆ Y` be subsets of a topological space, `p : Y → Y` a continuous map and `H` a homotopy
from the identity to `p`.  Assume

* `p` maps `U` into `U` and into `A` (`hpU`, `hpA`),
* `H` maps `I × U` into `U` (`hHU`),
* `H` maps `I × (U ∩ A)` into `A` (`hHA`).

Then the relative cohomology `H^k(U, U ∩ A; ℤ)` vanishes for every `k`.

Indeed, the restriction of `H` to `U` is a homotopy, inside `U`, from the identity to the map
`y ↦ p y`; and since `H` preserves `U ∩ A`, its restriction to `U ∩ A` is a homotopy, inside
`U ∩ A`, from the identity to the same map.  Composing with the inclusions of the subspace
`A' = {y ∈ U | y ∈ A} ⊆ U`, the map `r y = p y` (viewed as a map `U → A'`) is a homotopy inverse
to the inclusion `A' ↪ U`, both ways.  Hence the pair `(U, A')` is homotopy equivalent, as a pair,
to `(A', A')`, and the general vanishing result `Work.Thom.subsingleton_relComplex_of_homotopyRetract`
for a homotopy-equivalent subspace applies.

Note that no hypotheses on `p` or `H` are needed on the complement of `U`; the data is used only
after restriction to `U`, with respect to the subspace topology.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Thom

noncomputable section

theorem subsingleton_relComplex_of_homotopyData {Y : Type} [TopologicalSpace Y] (U A : Set Y)
    (p : C(Y, Y)) (H : C(↑unitInterval × Y, Y))
    (hH0 : ∀ y, H (0, y) = y) (hH1 : ∀ y, H (1, y) = p y)
    (hpU : ∀ y ∈ U, p y ∈ U) (hpA : ∀ y ∈ U, p y ∈ A)
    (hHU : ∀ t y, y ∈ U → H (t, y) ∈ U)
    (hHA : ∀ t y, y ∈ U → y ∈ A → H (t, y) ∈ A)
    (k : ℕ) :
    Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of ↥U) {y : ↥U | (y : Y) ∈ A}).homology k) := by
  -- `A'` is the part of `U` lying in `A`; the relative pair under consideration is
  -- `(U, A') = (U, U ∩ A)`.
  let A' : Set ↥U := {y | (y : Y) ∈ A}
  -- The map `r : U → A'`, `r y = p y`; the hypotheses `hpU`, `hpA` are exactly what is needed to
  -- land in `A'`.
  have hr : Continuous fun y : ↥U => (⟨⟨p y, hpU y y.2⟩, hpA y y.2⟩ : A') := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact p.continuous.comp continuous_subtype_val
  let r : C(↥U, A') := ⟨fun y => ⟨⟨p y, hpU y y.2⟩, hpA y y.2⟩, hr⟩
  -- The restriction `H : I × U → U` of the given homotopy, a homotopy from `id` to `incl ∘ r`.
  have hKUcont : Continuous fun q : ↥unitInterval × ↥U =>
      (⟨H (q.1, q.2), hHU q.1 q.2 q.2.2⟩ : ↥U) := by
    apply Continuous.subtype_mk
    exact H.continuous.comp (by continuity)
  let K : ContinuousMap.Homotopy (ContinuousMap.id ↥U)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A', ↥U)).comp r) :=
    { toContinuousMap := ⟨fun q => ⟨H (q.1, q.2), hHU q.1 q.2 q.2.2⟩, hKUcont⟩
      map_zero_left := by intro y; apply Subtype.ext; exact hH0 (y : Y)
      map_one_left := by intro y; apply Subtype.ext; exact hH1 (y : Y) }
  have h₁ : ContinuousMap.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(A', ↥U)).comp r)
      (ContinuousMap.id ↥U) := ⟨K.symm⟩
  -- The restriction `H : I × A' → A'` of the given homotopy, a homotopy from `id` to `r ∘ incl`;
  -- it needs both `hHU` (to stay in `U`) and `hHA` (to stay in `A`).
  have hLAcont : Continuous fun q : ↥unitInterval × A' =>
      (⟨⟨H (q.1, q.2), hHU q.1 (q.2 : Y) (q.2 : ↥U).2⟩,
        hHA q.1 (q.2 : Y) (q.2 : ↥U).2 (q.2 : A').2⟩ : A') := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact H.continuous.comp (by continuity)
  let L : ContinuousMap.Homotopy (ContinuousMap.id A')
      (r.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A', ↥U))) :=
    { toContinuousMap := ⟨fun q => (⟨⟨H (q.1, q.2), hHU q.1 (q.2 : Y) (q.2 : ↥U).2⟩,
        hHA q.1 (q.2 : Y) (q.2 : ↥U).2 (q.2 : A').2⟩ : A'), hLAcont⟩
      map_zero_left := by intro a; apply Subtype.ext; apply Subtype.ext; exact hH0 (a : Y)
      map_one_left := by intro a; apply Subtype.ext; apply Subtype.ext; exact hH1 (a : Y) }
  have h₂ : ContinuousMap.Homotopic (r.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A', ↥U)))
      (ContinuousMap.id A') := ⟨L.symm⟩
  -- `r` is a homotopy inverse of the inclusion `A' ↪ U`, so `H^k(U, A')` vanishes.
  exact Work.Thom.subsingleton_relComplex_of_homotopyRetract (X := ↥U) A' r h₁ h₂ k

end

end Work.Thom
