import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- Integrality is preserved by a ring hom `σ : S →+* T` that intertwines `τ : R →+* R` with the
structure maps: `σ (algebraMap R S r) = algebraMap R T (τ r)`.  Proof route: from a monic
`p : R[X]` with `p.eval₂ (algebraMap R S) x = 0`, use `p.map τ`, which is monic, and
`Polynomial.hom_eval₂`: `(p.map τ).eval₂ (algebraMap R T) (σ x) = σ (p.eval₂ (algebraMap R S) x)`. -/
lemma NeTwoIsIntegralMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] (σ : S →+* T) (τ : R →+* R)
    (h : ∀ r : R, σ (algebraMap R S r) = algebraMap R T (τ r)) {x : S} (hx : IsIntegral R x) :
    IsIntegral R (σ x) :=
  IsIntegral.map_of_comp_eq τ σ (RingHom.ext fun r => (h r).symm) hx

end Work.MotC2
