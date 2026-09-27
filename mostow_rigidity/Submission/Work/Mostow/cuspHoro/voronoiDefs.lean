import Mathlib

/-!
# Dirichlet cells and inner parallel bodies

For a group `G` acting on the Euclidean space `E m` by isometries through a homomorphism
`ρ : G →* (E m ≃ᵢ E m)`, the *Dirichlet cell* of a point `x₀` is the set of points of `E m` whose
distance to `x₀` is at most their distance to every other point of the orbit `G · x₀`:

`cell ρ x₀ = {y | ∀ g, dist y x₀ ≤ dist y (ρ g x₀)}`.

Its *inner parallel body* at scale `ε` is the set of points whose open `ε`-ball is contained in
the cell: `innerBody ε D = {y | ∀ z, dist y z < ε → z ∈ D}`.
-/

namespace Work.Mostow.cuspHoro

open Metric

/-- The Dirichlet (Voronoi) cell of `x₀` for the action `ρ` of `G` on `E m`. -/
def cell {m : ℕ} {G : Type*} [Group G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | ∀ g : G, dist y x₀ ≤ dist y (ρ g x₀)}

/-- The inner parallel body of `D` at scale `ε`: the points whose open `ε`-ball is contained
in `D`. -/
def innerBody {m : ℕ} (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin m))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {y | ∀ z, dist y z < ε → z ∈ D}

end Work.Mostow.cuspHoro
