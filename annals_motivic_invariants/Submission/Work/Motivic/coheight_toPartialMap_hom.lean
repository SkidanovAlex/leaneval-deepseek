import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- A partial isomorphism preserves the coheight (codimension) of a point: the underlying
partial map of `i` is an open immersion `i.source.toScheme ⟶ Y`, and coheight is insensitive
to restriction to an open subscheme (an open neighbourhood of a point contains all its
generizations). -/
theorem coheight_toPartialMap_hom {X Y : Scheme.{0}} (i : X.PartialIso Y) {x : X}
    (hx : x ∈ i.source) :
    Order.coheight (i.toPartialMap.hom ⟨x, hx⟩) = Order.coheight x := by
  change Order.coheight ((i.iso.hom ≫ i.target.ι) (⟨x, hx⟩ : ↑i.source)) = Order.coheight x
  have h2 := coheight_eq_of_isOpenImmersion (f := i.iso.hom ≫ i.target.ι)
    (x := (⟨x, hx⟩ : ↑i.source))
  rw [h2]
  exact (coheight_eq_of_isOpenImmersion (X := X) (f := i.source.ι)
    (x := (⟨x, hx⟩ : ↑i.source))).symm

end Work.Motivic
