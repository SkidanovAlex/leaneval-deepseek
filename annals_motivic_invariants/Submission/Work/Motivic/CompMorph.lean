import Mathlib
import ChallengeDeps

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Explicit composite morphisms of partial maps

Given partial maps `a : X.PartialMap Y` and `b : Y.PartialMap X`, the composite
`a.comp b : X.PartialMap X` has, by definition, hom

`(a.domain.ι.isoImage (a.hom ⁻¹ᵁ b.domain)).inv ≫ (a.hom ∣_ b.domain) ≫ b.hom`.

The purpose of this file is to package this morphism **with its explicit domain**, so that the
resulting term is well-typed by construction and can be used in the "unfolded" form.  Moreover we
package the first half of this composite as a morphism into `↑b.domain`, which is what one uses to
prove that the image of `a.hom` lands where it should.
-/

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The composite morphism `a ∘ b`, written with its explicit source
`a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ b.domain)`. -/
noncomputable def compMorph {X Y : Scheme.{0}} (a : X.PartialMap Y) (b : Y.PartialMap X) :
    ↑(a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ b.domain)) ⟶ X :=
  (Hom.isoImage a.domain.ι (a.hom ⁻¹ᵁ b.domain)).inv ≫ (a.hom ∣_ b.domain) ≫ b.hom

/-- `compMorph a b` is the underlying morphism of the composite partial map `a.comp b`. -/
lemma compMorph_eq {X Y : Scheme.{0}} [PreirreducibleSpace X] [Nonempty Y]
    (a : X.PartialMap Y) [IsDominant a.hom] (b : Y.PartialMap X) :
    compMorph a b = (a.comp b).hom :=
  PartialMap.comp_hom a b

/-- The first half of the composite morphism `a ∘ b`, as a morphism `↑U ⟶ ↑b.domain`
where `U ≤ a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ b.domain)`. -/
noncomputable def compMorphInv {X Y : Scheme.{0}} (a : X.PartialMap Y) (b : Y.PartialMap X)
    {U : X.Opens} (hU : U ≤ a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ b.domain)) :
    ↑U ⟶ (↑(b.domain) : Scheme) :=
  X.homOfLE hU ≫ (Hom.isoImage a.domain.ι (a.hom ⁻¹ᵁ b.domain)).inv ≫ (a.hom ∣_ b.domain)

end Work.Motivic
