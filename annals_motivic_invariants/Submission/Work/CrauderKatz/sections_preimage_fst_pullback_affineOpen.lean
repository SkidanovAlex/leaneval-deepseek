import Mathlib
import Submission.Work.CrauderKatz.sections_pullback_spec_polynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz

set_option linter.style.haveILetI false

/-- **Sections of a chart of `X × 𝔸¹`.**  Let `X` be a scheme over the field `𝕜`, let
`P := X ×_{Spec 𝕜} Spec 𝕜[t]` be the fibre product of `f : X ⟶ Spec 𝕜` with
`𝔸¹_𝕜 = Spec 𝕜[t]`, and let `p : P ⟶ X` be the first projection.  For a nonempty affine open
`U ⊆ X`, the preimage `p ⁻¹ᵁ U` is affine with ring of sections `Γ(X, U)[t]`.

Suggested route:
* `φ := pullback.map ((U.ι) ≫ f) g f g (U.ι) (𝟙 _) (𝟙 _) _ _ : pullback ((U.ι) ≫ f) g ⟶ P`
  (where `g = Spec.map (algebraMap 𝕜 (Polynomial 𝕜))`) is an open immersion
  (`AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion`), and the square with `U.ι` and `p` is a
  pullback; hence by `IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback` (with
  `W = ⊤`) the range of `φ` is exactly `p ⁻¹ᵁ U`, so
  `pullback ((U.ι) ≫ f) g ≅ (p ⁻¹ᵁ U).toScheme` (`IsOpenImmersion.isoOfRangeEq`).
* `Γ(pullback ((U.ι) ≫ f) g, ⊤) ≅ Γ(U,⊤) ⊗[𝕜] 𝕜[t] ≅ Γ(U,⊤)[t]`: either by
  `isPushout_appTop_of_isPullback` (pushout of rings) plus `polyEquivTensor'`, or by transporting to
  `Spec Γ(U,⊤)` via `AlgebraicGeometry.IsAffineOpen.isoSpec` and applying
  `AlgebraicGeometry.pullbackSpecIso` (cf. the sibling statement
  `Work.CrauderKatz.sections_pullback_spec_polynomial`, which is the case `U = Spec Γ(X,U)`).
* The `𝕜`-algebra structure on `Γ(X, U)` used above is
  `RingHom.toAlgebra ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ f.appTop ≫
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)).hom`.
* Finally `Γ(X, U) ≅ Γ(U, ⊤)` via the open immersion `U.ι` (`Γ.map (U.ι)` is iso, or
  `X.presheaf.map ...`).
* Note `Scheme.Opens`, `Γ`, `⁻¹ᵁ` and `≫` are scoped notations; write
  `(TopologicalSpace.Opens.map (...).base).obj U` and `CategoryTheory.CategoryStruct.comp` if you do
  not open the namespaces. -/
theorem sections_preimage_fst_pullback_affineOpen (𝕜 : Type) [Field 𝕜]
    (X : AlgebraicGeometry.Scheme.{0}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
    (U : X.Opens) [Nonempty U] (hU : AlgebraicGeometry.IsAffineOpen U) :
    Nonempty (((CategoryTheory.Limits.pullback f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))).presheaf.obj
      (Opposite.op ((TopologicalSpace.Opens.map (CategoryTheory.Limits.pullback.fst f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))).base).obj U)) : Type)
      ≃+* Polynomial ((X.presheaf.obj (Opposite.op U) : Type))) := by
  open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
  open scoped AlgebraicGeometry in
  -- Abbreviations.
  let g : Spec (CommRingCat.of (Polynomial 𝕜)) ⟶ Spec (CommRingCat.of 𝕜) :=
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))
  let P := pullback f g
  let p : P ⟶ X := pullback.fst f g
  let Q := pullback ((U.ι) ≫ f) g
  -- The `𝕜`-algebra structure on `Γ(X, U)` for which `Spec Γ(X,U) ⟶ Spec 𝕜` is the structure map.
  let φ : 𝕜 →+* ↑(X.presheaf.obj (Opposite.op U)) :=
    CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ f.appLE ⊤ U (le_top : U ≤ ⊤))
  letI : Algebra 𝕜 ↑(X.presheaf.obj (Opposite.op U)) := φ.toAlgebra
  let F : Spec (CommRingCat.of ↑(X.presheaf.obj (Opposite.op U))) ⟶ Spec (CommRingCat.of 𝕜) :=
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 ↑(X.presheaf.obj (Opposite.op U))))
  -- `F` is the structure morphism of the affine open `U`.
  have hspec : Spec.map (CommRingCat.ofHom φ) = hU.fromSpec ≫ f := by
    have h2 := IsAffineOpen.SpecMap_appLE_fromSpec (X := X) (Y := Spec (CommRingCat.of 𝕜)) f
      (isAffineOpen_top (Spec (CommRingCat.of 𝕜))) hU (le_top : U ≤ ⊤)
    simp only [Scheme.Hom.appLE] at h2
    change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
      (f.app ⊤ ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) = hU.fromSpec ≫ f
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact h2
  have h1 : CommRingCat.ofHom (algebraMap 𝕜 ↑(X.presheaf.obj (Opposite.op U))) =
      CommRingCat.ofHom φ := rfl
  have hF : F = hU.fromSpec ≫ f := (congrArg (fun t => Spec.map t) h1).trans hspec
  -- The two structure morphisms of `U` agree under `hU.isoSpec`.
  have hcompat : hU.isoSpec.hom ≫ F = U.ι ≫ f := by
    rw [hF, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
  have hmap : (U.ι ≫ f) = hU.isoSpec.hom ≫ F := hcompat.symm
  -- Base change of the affine model of `U` along `g` is (canonically) the affine model of `Q`.
  let Q' := pullback F g
  have h₁ : (U.ι ≫ f) ≫ 𝟙 (Spec (CommRingCat.of 𝕜)) = hU.isoSpec.hom ≫ F := by
    rw [hmap]; simp
  have h₂ : g ≫ 𝟙 (Spec (CommRingCat.of 𝕜)) = 𝟙 (Spec (CommRingCat.of (Polynomial 𝕜))) ≫ g := by
    simp
  haveI : IsIso (pullback.map ((U.ι) ≫ f) g F g hU.isoSpec.hom (𝟙 _) (𝟙 _) h₁ h₂) :=
    pullback.map_isIso _ _ _ _ _ _ _ _ _
  let eQ : Q ≅ Q' := asIso (pullback.map ((U.ι) ≫ f) g F g hU.isoSpec.hom (𝟙 _) (𝟙 _) h₁ h₂)
  -- `Q` is the pullback `U ×_X P`, whose global sections are those of `P` over `p ⁻¹ᵁ U`.
  have e₁ : Q ≅ ↑(p ⁻¹ᵁ U) :=
    (pullbackRightPullbackFstIso f g U.ι).symm ≪≫ pullbackSymmetry U.ι p ≪≫
      pullbackRestrictIsoRestrict p U
  have r₁ : Γ(P, p ⁻¹ᵁ U) ≃+* Γ(Q, ⊤) :=
    ((p ⁻¹ᵁ U).topIso.symm ≪≫ (Scheme.Γ.mapIso e₁.op)).commRingCatIsoToRingEquiv
  have r₂ : Γ(Q, ⊤) ≃+* Γ(Q', ⊤) :=
    (Scheme.Γ.mapIso eQ.op).symm.commRingCatIsoToRingEquiv
  -- The affine case: the global sections of `Q'` are `Γ(X, U) ⊗[𝕜] 𝕜[t] = Γ(X, U)[t]`.
  obtain ⟨r₃⟩ := sections_pullback_spec_polynomial 𝕜 ↑(X.presheaf.obj (Opposite.op U))
  exact ⟨r₁.trans (r₂.trans r₃)⟩

end Work.CrauderKatz
