import Submission.Work.G2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.G2.BaseChangeAPI` — functoriality and stability of the base change `X ↦ X ×_{Spec ℤ} Spec 𝕜`

The base change `Work.G2.baseChangeZ 𝕜 : (Spec ℤ-schemes) → (Spec 𝕜-schemes)` is a functor, and it
preserves the properties of morphisms that the `G₂`-construction uses.  All of this is *proved*
here; none of it is a named input.

* `Work.G2.baseChangeZMap_id`, `Work.G2.baseChangeZMap_comp` — functoriality;
* `Work.G2.baseChangeZMap_isOver` — over the base (in `Work.G2.Defs`);
* `Work.G2.baseChangeZProj_isOver` — the projection of a base change is a morphism over `Spec ℤ`;
* `Work.G2.isClosedImmersion_baseChangeZMap` — the base change of a closed immersion is one;
* `Work.G2.isoOver_baseChangeZ` — the base change of an isomorphism over `Spec ℤ` is an isomorphism
  over `Spec 𝕜`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.G2

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The base change commutes with identities.** -/
theorem baseChangeZMap_id (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of ℤ))] :
    baseChangeZMap 𝕜 (𝟙 X) = 𝟙 (baseChangeZ 𝕜 X) := by
  unfold baseChangeZMap
  exact pullback.map_id

/-- **The base change commutes with composition**: it is a functor from `Spec ℤ`-schemes to
`Spec 𝕜`-schemes. -/
theorem baseChangeZMap_comp (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] [Z.Over (Spec (.of ℤ))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of ℤ))] [g.IsOver (Spec (.of ℤ))] :
    baseChangeZMap 𝕜 (f ≫ g) = baseChangeZMap 𝕜 f ≫ baseChangeZMap 𝕜 g := by
  unfold baseChangeZMap
  rw [pullback.map_comp]
  rfl

/-- **The projection of a base change is a morphism over `Spec ℤ`** (`X_𝕜` is a `Spec ℤ`-scheme
through its projection to `X`, and `X_𝕜 ⟶ X` commutes with the structure morphisms). -/
theorem baseChangeZProj_isOver (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of ℤ))] :
    (baseChangeZProj 𝕜 X).IsOver (Spec (.of ℤ)) :=
  ⟨rfl⟩

/-- **The base change of a closed immersion is a closed immersion** (closed immersions are stable
under base change).  This is the *proved* half of "the centres `Z_𝕜 ⊂ G_𝕜/P_𝕜`,
`Z'_𝕜 ⊂ G_𝕜/P'_𝕜` and the zero locus `X_𝕜 ⊂ G_𝕜/B_𝕜` are closed subvarieties" of the paper. -/
theorem isClosedImmersion_baseChangeZMap (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℤ))] [Y.Over (Spec (.of ℤ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℤ))]
    [IsClosedImmersion f] : IsClosedImmersion (baseChangeZMap 𝕜 f) :=
  MorphismProperty.of_isPullback (baseChangeZMap_isPullback 𝕜 f).flip ‹IsClosedImmersion f›

/-- **The base change of an isomorphism over `Spec ℤ` is an isomorphism over `Spec 𝕜`.**

This is the descent direction of `Work.CY3.IsoOver` for the `ℤ`-models: a `Spec ℤ`-isomorphism
`X ≅ Y` gives a `𝕜`-isomorphism of the base changes, so that e.g. `Z_ℤ ≅ Z'_ℤ` would imply
`Z_𝕜 ≅ Z'_𝕜`.  (The converse fails in general — two non-isomorphic `ℤ`-schemes can become
isomorphic after base change to `𝕜` — which is why the non-isomorphism of the two centres is
obtained not from the `ℤ`-model but from the *cubic self-intersection* `14 ≠ 42`,
`Work.G2.not_isoOver_of_cubic`.) -/
theorem isoOver_baseChangeZ (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of ℤ))]
    [Y.Over (Spec (.of ℤ))] [GeometricallyIntegral (X ↘ Spec (.of ℤ))]
    [IsSeparated (X ↘ Spec (.of ℤ))] [LocallyOfFiniteType (X ↘ Spec (.of ℤ))]
    [QuasiCompact (X ↘ Spec (.of ℤ))] [GeometricallyIntegral (Y ↘ Spec (.of ℤ))]
    [IsSeparated (Y ↘ Spec (.of ℤ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℤ))]
    [QuasiCompact (Y ↘ Spec (.of ℤ))] (e : X ≅ Y) [e.hom.IsOver (Spec (.of ℤ))] :
    Work.CY3.IsoOver 𝕜 (baseChangeZ 𝕜 X) (baseChangeZ 𝕜 Y) := by
  haveI : IsIso (baseChangeZMap 𝕜 e.hom) := by
    unfold baseChangeZMap
    exact pullback.map_isIso (specMapZ 𝕜) (X ↘ Spec (.of ℤ)) (specMapZ 𝕜)
      (Y ↘ Spec (.of ℤ)) (𝟙 (Spec (.of 𝕜))) e.hom (𝟙 (Spec (.of ℤ))) _ _
  exact ⟨asIso (baseChangeZMap 𝕜 e.hom), baseChangeZMap_isOver 𝕜 e.hom⟩

end

end Work.G2
