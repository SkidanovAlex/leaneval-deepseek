import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.curve_tangent_chart
import Submission.Work.ManifoldParity.exists_circle_parametrization
import Submission.Work.ManifoldParity.exists_tangentField_of_closed_curves

/-!
# A continuous non-vanishing tangent field on a compact locally-graph set

The target of this file: a compact set `K ⊆ ℝⁿ` which is locally the graph of a smooth function
over some coordinate axis admits a continuous non-vanishing field which is tangent to `K` in the
strong chartwise sense (`IsTangentField`).

This is assembled from two inputs:

* `Work.ManifoldParity.exists_circle_parametrization`: `K` is the union of the ranges of finitely
  many smooth periodic regular curves;
* `Work.ManifoldParity.exists_tangentField_of_closed_curves`: such a family of curves yields a
  continuous non-vanishing chartwise tangent field.
-/

namespace Work.ManifoldParity

noncomputable section

open Set Function
open scoped Topology Manifold

variable {n : ℕ}

/-- `HasLocalGraphCharts` is the hypothesis of the target, with the conjunction reordered. -/
theorem hasLocalGraphCharts_of (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
          (∀ t, (η t) i = 0) ∧
          ∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) :
    HasLocalGraphCharts K := by
  intro x hx
  obtain ⟨i, U, η, h1, h2, h3, h4, h5⟩ := hgra x hx
  exact ⟨i, U, η, ⟨h1, h3, h4, h5⟩, h2⟩

/-- The statement of `IsTangentField` is exactly the chartwise condition of the target. -/
theorem isTangentField_iff (K : Set (EuclideanSpace ℝ (Fin n)))
    (U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    IsTangentField K U ↔
      ∀ x ∈ K, ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
          (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen V → x ∈ V → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η →
        (∀ t, (η t) i = 0) →
        (∀ y ∈ V, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧
          U x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ)) := by
  constructor
  · intro h x hx i V η hV hxV hη hηi hgr
    exact h x hx i V η ⟨hV, hη, hηi, hgr⟩ hxV
  · intro h x hx i V η hchart hxV
    exact h x hx i V η hchart.1 hxV hchart.2.1 hchart.2.2.1 hchart.2.2.2

theorem exists_continuous_tangent_field {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
          (∀ t, (η t) i = 0) ∧
          ∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))
    : ∃ U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContinuousOn U K ∧
        (∀ x ∈ K, U x ≠ 0) ∧
        (∀ x ∈ K, ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
            (η : ℝ → EuclideanSpace ℝ (Fin n)),
          IsOpen V → x ∈ V → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η →
          (∀ t, (η t) i = 0) →
          (∀ y ∈ V, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
          ∃ c : ℝ, c ≠ 0 ∧
            U x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) := by
  classical
  obtain ⟨m, γ, T, hT, hsm, hper, hvel, hinj, hrange⟩ :=
    exists_circle_parametrization K hK hgra
  have hcover : ∀ j, ∀ t, γ j t ∈ K := by
    intro j t
    rw [hrange]
    exact mem_iUnion.mpr ⟨j, mem_range_self t⟩
  have hsurj : ∀ x ∈ K, ∃ j t, γ j t = x := by
    intro x hx
    rw [hrange] at hx
    obtain ⟨j, t, ht⟩ := mem_iUnion.mp hx
    exact ⟨j, t, ht⟩
  obtain ⟨U, hcont, hne, htan⟩ :=
    exists_tangentField_of_closed_curves K (hasLocalGraphCharts_of K hgra) γ T hT hsm hper
      hvel hinj hcover hsurj
  exact ⟨U, hcont, hne, (isTangentField_iff K U).mp htan⟩

end

end Work.ManifoldParity
