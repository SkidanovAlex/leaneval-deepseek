import Mathlib

/-!
# Definitions for the circle-parametrisation of a locally-graph compact set

A compact set `K ⊆ ℝⁿ` which is *locally the graph of a smooth function over some coordinate axis*
is a compact `1`-dimensional manifold, hence a finite disjoint union of circles; the target
`Work.ManifoldParity.exists_circle_parametrization` makes this explicit by exhibiting periodic
smooth immersions whose ranges cover `K`.

This file collects the definitions used in that reduction.

* `gmap i η` — the graph map `u ↦ u • eᵢ + η u`;
* `IsGraphChart K i U η` — on the open set `U`, the set `K` is exactly the graph of `η` over the
  `i`-th coordinate;
* `HasLocalGraphCharts K` — the hypothesis of the target theorem;
* `IsTangentField K V` — the field `V` is non-zero and tangent to `K` in the strong chartwise form:
  at `x ∈ K`, for every graph chart `(i,U,η)` at `x`, the value `V x` is a non-zero multiple of
  `eᵢ + η'(xᵢ)(1)`;
* `IsCircleParam γ T` — the conclusion shape for a single closed curve: `T > 0`, `γ` is smooth, `T`
  is a period of `γ`, `γ'` never vanishes, and `γ` is injective modulo `T`.
-/

namespace Work.ManifoldParity

noncomputable section

open Set

variable {n : ℕ}

/-- The graph map `u ↦ u • eᵢ + η u` over the `i`-th coordinate. -/
def gmap (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) :
    ℝ → EuclideanSpace ℝ (Fin n) :=
  fun u => u • EuclideanSpace.single i (1 : ℝ) + η u

@[simp]
theorem gmap_apply (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) (u : ℝ) :
    gmap i η u = u • EuclideanSpace.single i (1 : ℝ) + η u := rfl

/-- The `i`-th coordinate of a graph point is the parameter. -/
theorem gmap_coord {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ∀ t, η t i = 0)
    (u : ℝ) : (gmap i η u) i = u := by
  simp [gmap, hη]

/-- The graph map is injective when `η` takes values in the coordinate hyperplane. -/
theorem gmap_injective {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ∀ t, η t i = 0) :
    Function.Injective (gmap i η) := by
  intro a b hab
  have h : (gmap i η a) i = (gmap i η b) i := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hab
  rw [gmap_coord hη, gmap_coord hη] at h
  exact h

/-- The graph map is as smooth as `η`. -/
theorem contDiff_gmap {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)}
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gmap i η) := by
  rw [show gmap i η = fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u from rfl]
  exact ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff).add hη

/-- **A local graph chart for `K`:** on the open set `U`, the set `K` is exactly the graph of `η`
over the `i`-th coordinate. -/
def IsGraphChart (K : Set (EuclideanSpace ℝ (Fin n))) (i : Fin n)
    (U : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  IsOpen U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
    ∀ y ∈ U, (y ∈ K ↔ y = gmap i η (y i))

/-- **The hypothesis of the target theorem:** every point of `K` has a local graph chart. -/
def HasLocalGraphCharts (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
      (η : ℝ → EuclideanSpace ℝ (Fin n)), IsGraphChart K i U η ∧ x ∈ U

/-- **Tangency of a field along `K`, chartwise.**  At every `x ∈ K` and for every graph chart
`(i,U,η)` at `x`, the value `V x` is a non-zero multiple of the tangent direction
`eᵢ + η'(xᵢ)(1)`. -/
def IsTangentField (K : Set (EuclideanSpace ℝ (Fin n)))
    (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ K, ∀ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
      (η : ℝ → EuclideanSpace ℝ (Fin n)),
    IsGraphChart K i U η → x ∈ U →
    ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (x i)) (1 : ℝ))

/-- **The conclusion shape for one closed curve:** `T > 0` is a period of the smooth curve `γ`, the
velocity of `γ` never vanishes, and `γ` is injective modulo `T`. -/
def IsCircleParam (γ : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ) : Prop :=
  0 < T ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧ Function.Periodic γ T ∧
    (∀ t : ℝ, fderiv ℝ γ t (1 : ℝ) ≠ 0) ∧
    (∀ a b : ℝ, γ a = γ b → ∃ k : ℤ, a = b + k * T)

end

end Work.ManifoldParity
