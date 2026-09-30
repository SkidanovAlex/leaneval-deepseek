import Mathlib
import Submission.Work.RatHurewicz.Excision
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.RatHurewicz
variable {R : Type} [CommRing R] [Nontrivial R]

set_option linter.unusedVariables false

open scoped Topology unitInterval
namespace Work.SSSR.RatHurewicz

noncomputable section

/-- The standard `n`-cube, `Iⁿ = (Fin n → [0,1])`. -/
abbrev ICube (n : ℕ) : Type := Fin n → unitInterval

/-- **The compression property of the pair `(Y, A)` in dimension `d`**: every map of pairs
`(Iᵈ, ∂Iᵈ) → (Y, A)` is homotopic to a map into `A`, relative to the boundary.

By tom Dieck, *Algebraic Topology*, Proposition 6.7.5, this is equivalent to the vanishing of the
relative homotopy groups `π_q(Y,A,·)` for `q ≤ d` and to the connectivity statements for the
inclusion `A ↪ Y`. -/
def CompressRel (Y : Type) [TopologicalSpace Y] (A : Set Y) (d : ℕ) : Prop :=
  ∀ f : C(ICube d, Y), (∀ x, x ∈ Cube.boundary (Fin d) → f x ∈ A) →
    ∃ G : C(ICube d × I, Y),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x (hx : x ∈ Cube.boundary (Fin d)) t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ A)

end

end Work.SSSR.RatHurewicz
