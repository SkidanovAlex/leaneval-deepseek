import Mathlib
import Submission.Work.Euclidean.TangentField.Setup
import Submission.Work.Euclidean.TangentField.CurveTangent
import Submission.Work.Euclidean.TangentField.graph_tangent_field_of_continuous_localGraph
import Submission.Work.Euclidean.TangentField.ComponentField

/-!
# A smooth compactly supported tangent field along a compact `P`-locally-graph set

The target `Work.Euclidean.TangentField.exists_smooth_tangent_field`: if the ambient predicate `P`
is locally the graph of a smooth function over a coordinate axis at every point of a compact set
`K ⊆ P`, then there is a smooth compactly supported field `V` which is non-zero on `K` and parallel
to the graph tangent of every local graph presentation of `P` at every point of `K`.

It is the composition of two facts.

* `Work.Euclidean.TangentField.exists_continuous_tangent_field_localGraph_alt`: the same local graph
  hypothesis yields a *continuous* non-vanishing field along `K` which is parallel to every
  `P`-chart at every point of `K` (component-wise construction: the set `A := P ∩ ⋃_j U_j` of a
  finite chart cover is genuinely locally a graph, and each of its (finitely many, for the compact
  `K`) connected components carries such a field — the compact ones by the manifold chapter
  `Work.ManifoldParity`, the non-compact ones by parametrising the component by `ℝ`).
* `Work.Euclidean.TangentField.graph_tangent_field_of_continuous_localGraph`: such a continuous
  field is smoothed and cut down to compact support by a partition of unity subordinate to the
  chart cover, comparing the local chart fields with the continuous field by the sign of their inner
  product.
-/

namespace Work.Euclidean.TangentField

theorem exists_smooth_tangent_field {n : ℕ} {P : EuclideanSpace ℝ (Fin n) → Prop}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKsub : ∀ x ∈ K, P x)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
        ∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) :
    ∃ V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧
      (∀ x ∈ K, V x ≠ 0) ∧
      (∀ x ∈ K, ∀ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
          (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t, η t i = 0) →
        (∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧
          V x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) := by
  obtain ⟨U₀, hU₀cont, hU₀ne, hU₀par⟩ :=
    exists_continuous_tangent_field_localGraph_alt hK hKsub hgra
  exact graph_tangent_field_of_continuous_localGraph hK hKsub hgra U₀ hU₀cont hU₀ne hU₀par

end Work.Euclidean.TangentField
