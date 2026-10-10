import Mathlib
import Submission.Work.CrauderKatz.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz

/-- **The residue field of a field is the field itself.**  For a type `K` carrying a field
structure, the residue field `IsLocalRing.ResidueField K = K ⧸ 𝔪` (with `𝔪 = ⊥`) is canonically
isomorphic to `K`: the local ring homomorphism `K → K`, viewed as a map out of the local ring `K`,
descends to the residue field (`IsLocalRing.ResidueField.lift`), and is a bijection because the
residue map is surjective. -/
noncomputable def residueFieldEquivSelf (K : Type) [Field K] :
    IsLocalRing.ResidueField K ≃+* K :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (RingHom.id K))
    ⟨RingHom.injective _, fun y => ⟨IsLocalRing.residue K y, by simp⟩⟩

/-- **The function field of a divisor is the residue field of its generic point.**  For an immersion
`i : D ⟶ X` of integral schemes, the residue field of the image of the generic point of `D` (a point
of `X`) is the function field of `D`.  Concretely, for a divisor `D ⊂ X` this computes `κ(η_D)`.

This is the first of the two computations needed for the (F1) inputs of the Crauder–Katz link (the two
exceptional divisors of the link are `ℙ¹`-bundles over the curves `C`, `C' = Jac²C`, and their
function fields are `κ(C)(t)`, `κ(C')(t)`); the companion fact identifying the function field of the
`𝔸¹`-cylinder with `RatFunc κ(C)` — the model `Work.CrauderKatz.cylinderField` of this area — is the
separate target `Work.CrauderKatz.functionField_prod_affineLine`.

The conclusion is a ring equivalence (not yet the `𝕜`-linear form `ResAlgEquiv` used by the (F1)
fields of `Work.CrauderKatz.CrauderKatzLink`); for `i = 𝟙 X` it specialises to the function field of
`X` itself.  Mathlib has no bridge between `Scheme.residueField` at a generic point and
`Scheme.functionField`, so this fills a genuine gap in the library. -/
theorem residueField_genericPoint_eq_functionField {D X : AlgebraicGeometry.Scheme.{0}}
    [IrreducibleSpace D] [IrreducibleSpace X] [AlgebraicGeometry.IsIntegral D]
    [AlgebraicGeometry.IsIntegral X] (i : D ⟶ X) [AlgebraicGeometry.IsImmersion i] :
    Nonempty (X.residueField (i (genericPoint D)) ≃+*
      (AlgebraicGeometry.Scheme.functionField D : Type)) := by
  -- An immersion is a preimmersion, hence induces *surjective* maps on stalks; passing to residue
  -- fields gives a surjective ring homomorphism `κ(i η_D) → κ(η_D)` between fields, which is
  -- therefore an isomorphism.  Composing with `κ(η_D) ≅ κ(η_D)` for the integral scheme `D`
  -- (the residue field of the local ring `𝒪_{D, η_D} = κ(D)` is `κ(D)` itself, since `κ(D)` is a
  -- field) gives the claim.
  have hsurj : Function.Surjective (i.residueFieldMap (genericPoint D)).hom := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨b, hb⟩ := AlgebraicGeometry.Scheme.Hom.stalkMap_surjective i (genericPoint D) a
    exact ⟨IsLocalRing.residue _ b, by
      change IsLocalRing.ResidueField.map (AlgebraicGeometry.Scheme.Hom.stalkMap i (genericPoint D)).hom
          (IsLocalRing.residue _ b) = IsLocalRing.residue _ a
      rw [IsLocalRing.ResidueField.map_residue, hb]⟩
  exact ⟨(RingEquiv.ofBijective (i.residueFieldMap (genericPoint D)).hom
      ⟨RingHom.injective _, hsurj⟩).trans
    (residueFieldEquivSelf (AlgebraicGeometry.Scheme.functionField D : Type))⟩

end Work.CrauderKatz
