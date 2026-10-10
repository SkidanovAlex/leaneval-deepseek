import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Prod.AlgMapResidue
import Submission.Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod` — the section of the cylinder and the fibre over a point

This file sets up the vocabulary used to compare a birational map `φ : X ⤏ Y` over `𝕜` with its
product `φ × id_{𝔸ᵏ}` on the cylinder `WX = 𝔸ᵏ ×_{Spec 𝕜} X`:

* `wPt k : Spec 𝕜 ⟶ 𝔸ᵏ` — the origin, the `𝕜`-rational point `tᵢ ↦ 0` of affine space;
* `sec k X : X ⟶ WProd X k` — the section of the projection `WX ⟶ X` over the origin (the
  inclusion of the fibre `{0} × X ≅ X`);
* `resStr X x : Spec κ(x) ⟶ Spec 𝕜` — the structure morphism of the residue field `κ(x)` of a
  point of a `𝕜`-scheme (written with `Work.CY3Stab.Prod.algMapResidue` so that
  `fromSpecResidueField_comp_structure_aux` applies definitionally);
* `fibL k X x = Spec κ(x)[t₁,…,t_k]` — the (affine) fibre of `WX ⟶ X` over `x`, with its two
  structure morphisms `fibL₁ : fibL ⟶ 𝔸ᵏ`, `fibL₂ : fibL ⟶ X` and the induced
  `rho : fibL ⟶ WX` (the generic point of `fibL` maps to the *cylinder point* of the fibre over
  `x` in `WX`, and the image of the zero section `zeroSec` is the point `sec x`);
* `fibL₀ : Spec κ(x) ⟶ WX` — the zero section of the fibre, identified with
  `fromSpecResidueField x ≫ sec` (`fibL₀_eq`).

The two key point formulae are `rho_bot_fst`/`rho_bot_snd` (the generic point of the fibre lies
over `(genericPoint 𝔸ᵏ, x)`) and `zeroSec_rho` (`ρ ∘ 0 = σ x`, i.e. the fibre of the section
`sec` at the origin is the zero section of the fibre over `x`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The origin of affine space**: the `𝕜`-point `Spec 𝕜 ⟶ 𝔸ᵏ` given by `tᵢ ↦ 0`. -/
noncomputable def wPt (k : ℕ) : Spec (CommRingCat.of 𝕜) ⟶ Work.CY3Stab.AffineK (𝕜 := 𝕜) k :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of 𝕜))) (fun _ => 0)

/-- The origin is a section of `𝔸ᵏ ⟶ Spec 𝕜`. -/
theorem wPt_over (k : ℕ) :
    wPt (𝕜 := 𝕜) k ≫ (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 _ := by
  rw [wPt]; exact AffineSpace.homOfVector_over _ _

/-- **The section of the cylinder over the origin**: the inclusion of the fibre `{0} × X`. -/
noncomputable def sec (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] :
    X ⟶ Work.CY3Stab.WProd (𝕜 := 𝕜) X k :=
  pullback.lift ((X ↘ Spec (CommRingCat.of 𝕜)) ≫ wPt k) (𝟙 X) (by
    rw [Category.assoc, wPt_over, Category.comp_id, Category.id_comp])

/-- The section is a section of the projection onto `X`. -/
theorem sec_proj (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] :
    sec (𝕜 := 𝕜) k X ≫ pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- The composite of the section with the projection onto `𝔸ᵏ` is the origin. -/
theorem sec_fst (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] :
    sec (𝕜 := 𝕜) k X ≫ pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) = (X ↘ Spec (CommRingCat.of 𝕜)) ≫ wPt k :=
  pullback.lift_fst _ _ _

/-- **The structure morphism of the residue field** `κ(x)` of a point of a `𝕜`-scheme. -/
noncomputable def resStr (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    Spec (X.residueField x) ⟶ Spec (CommRingCat.of 𝕜) :=
  Spec.map (Work.CY3Stab.Prod.algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x)

/-- `fromSpecResidueField x` composed with the structure morphism of `X` is `resStr X x`. -/
theorem fromSpecResidueField_eq_resStr (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    X.fromSpecResidueField x ≫ (X ↘ Spec (CommRingCat.of 𝕜)) = resStr X x :=
  _root_.Work.CY3Stab.Prod.fromSpecResidueField_comp_structure_aux (𝕜 := 𝕜) X x

/-- The `Spec 𝕜`-structure of `Spec (MvPolynomial (Fin k) 𝕜)` transported to `𝔸ᵏ`. -/
theorem affSpecIso_inv_over (k : ℕ) :
    (AffineSpace.SpecIso (Fin k) (CommRingCat.of 𝕜)).inv ≫
      (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : ↥(CommRingCat.of 𝕜) →+*
        MvPolynomial (Fin k) ↥(CommRingCat.of 𝕜))) :=
  AffineSpace.SpecIso_inv_over (CommRingCat.of 𝕜)

/-- **The fibre of the cylinder over `x`**, in the model `Spec κ(x)[t₁,…,t_k]`. -/
abbrev fibL (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) : Scheme.{0} :=
  Spec (CommRingCat.of (MvPolynomial (Fin k) ↥(X.residueField x)))

/-- The `𝔸ᵏ`-coordinate of the fibre over `x`: the base change
`Spec κ(x)[t] ⟶ Spec 𝕜[t] ≅ 𝔸ᵏ`. -/
noncomputable def fibL₁ (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    fibL (𝕜 := 𝕜) k X x ⟶ Work.CY3Stab.AffineK (𝕜 := 𝕜) k :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map
      (Work.CY3Stab.Prod.algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x).hom)) ≫
    (AffineSpace.SpecIso (Fin k) (CommRingCat.of 𝕜)).inv

/-- The `X`-coordinate of the fibre over `x`. -/
noncomputable def fibL₂ (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    fibL (𝕜 := 𝕜) k X x ⟶ X :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C)) ≫ X.fromSpecResidueField x

/-- The two coordinates of the fibre over `x` are compatible over `Spec 𝕜`. -/
theorem fibL_condition (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    fibL₁ (𝕜 := 𝕜) k X x ≫ (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) =
      fibL₂ (𝕜 := 𝕜) k X x ≫ (X ↘ Spec (CommRingCat.of 𝕜)) := by
  have h1 : fibL₁ (𝕜 := 𝕜) k X x ≫
      (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map
        (algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x).hom)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C :
          ↥(CommRingCat.of 𝕜) →+* MvPolynomial (Fin k) ↥(CommRingCat.of 𝕜))) := by
    rw [fibL₁, Category.assoc, affSpecIso_inv_over]
  have h2 : fibL₂ (𝕜 := 𝕜) k X x ≫ (X ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C :
        ↥(X.residueField x) →+* MvPolynomial (Fin k) ↥(X.residueField x))) ≫
        Spec.map (algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x) := by
    rw [fibL₂, Category.assoc, fromSpecResidueField_eq_resStr]
    rfl
  rw [h1, h2, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp

/-- **The map from the fibre over `x` to the cylinder** `𝔸ᵏ ×_{Spec 𝕜} X`. -/
noncomputable def rho (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    fibL (𝕜 := 𝕜) k X x ⟶ Work.CY3Stab.WProd (𝕜 := 𝕜) X k :=
  pullback.lift (fibL₁ (𝕜 := 𝕜) k X x) (fibL₂ (𝕜 := 𝕜) k X x)
    (fibL_condition (𝕜 := 𝕜) k X x)

/-- The first coordinate of `rho`. -/
theorem rho_fst (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    rho (𝕜 := 𝕜) k X x ≫ pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) = fibL₁ (𝕜 := 𝕜) k X x :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `rho`. -/
theorem rho_snd (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    rho (𝕜 := 𝕜) k X x ≫ pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) = fibL₂ (𝕜 := 𝕜) k X x :=
  pullback.lift_snd _ _ _

/-- **The zero section of the fibre**, i.e. the inclusion of the fibre of `WX ⟶ X` over `x`
matching the section `sec` over the origin. -/
noncomputable def fibL₀ (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    Spec (X.residueField x) ⟶ Work.CY3Stab.WProd (𝕜 := 𝕜) X k :=
  pullback.lift (resStr X x ≫ wPt k) (X.fromSpecResidueField x) (by
    rw [Category.assoc, wPt_over, Category.comp_id, fromSpecResidueField_eq_resStr])

/-- The zero section of the fibre is `fromSpecResidueField x ≫ sec`. -/
theorem fibL₀_eq (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    fibL₀ (𝕜 := 𝕜) k X x = X.fromSpecResidueField x ≫ sec (𝕜 := 𝕜) k X := by
  apply pullback.hom_ext
  · rw [fibL₀, Category.assoc, sec_fst, pullback.lift_fst, ← Category.assoc,
      fromSpecResidueField_eq_resStr]
  · rw [fibL₀, Category.assoc, sec_proj, Category.comp_id, pullback.lift_snd]

/-- **The zero section of the fibre scheme** `Spec κ(x) ⟶ Spec κ(x)[t]` given by `tᵢ ↦ 0`. -/
noncomputable def zeroSec (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    Spec (X.residueField x) ⟶ fibL (𝕜 := 𝕜) k X x :=
  Spec.map (CommRingCat.ofHom ((MvPolynomial.aeval
    (fun _ => (0 : ↥(X.residueField x)))).toRingHom))


/-- **The fibre restriction of a partial map.**  For a partial map
`a : WX.PartialMap WY` on the cylinder, `fibMap k a` is the partial map `X.PartialMap Y` obtained
by restricting `a` to the fibre of `WX ⟶ X` over the origin (the image of the section `sec`) and
projecting to `Y`.  The openness of the domain (`h`) is automatic when the domain of `a` meets
the section (then it contains the generic point of the irreducible `X`). -/
noncomputable def fibMap (k : ℕ) {X Y : Scheme.{0}} [X.Over (Spec (CommRingCat.of 𝕜))]
    [Y.Over (Spec (CommRingCat.of 𝕜))]
    (a : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).PartialMap (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k))
    (h : Dense (((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain : X.Opens) : Set X)) : X.PartialMap Y where
  domain := sec (𝕜 := 𝕜) k X ⁻¹ᵁ a.domain
  dense_domain := h
  hom := IsOpenImmersion.lift a.domain.ι (((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain).ι ≫ sec (𝕜 := 𝕜) k X)
      (by
        rw [Set.range_subset_iff]
        intro p
        exact ⟨⟨sec (𝕜 := 𝕜) k X ((sec (𝕜 := 𝕜) k X ⁻¹ᵁ a.domain).ι p), p.2⟩, rfl⟩) ≫ a.hom ≫
    pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (Y ↘ Spec (CommRingCat.of 𝕜))

/-- The domain of the fibre restriction. -/
@[simp]
theorem fibMap_domain (k : ℕ) {X Y : Scheme.{0}} [X.Over (Spec (CommRingCat.of 𝕜))]
    [Y.Over (Spec (CommRingCat.of 𝕜))]
    (a : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).PartialMap (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k))
    (h : Dense (((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain : X.Opens) : Set X)) :
    (fibMap (𝕜 := 𝕜) k a h).domain = sec (𝕜 := 𝕜) k X ⁻¹ᵁ a.domain := rfl

/-- The underlying morphism of the fibre restriction, in terms of the lift through the domain of
`a`. -/
theorem fibMap_hom (k : ℕ) {X Y : Scheme.{0}} [X.Over (Spec (CommRingCat.of 𝕜))]
    [Y.Over (Spec (CommRingCat.of 𝕜))]
    (a : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).PartialMap (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k))
    (h : Dense (((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain : X.Opens) : Set X)) :
    (fibMap (𝕜 := 𝕜) k a h).hom =
      IsOpenImmersion.lift a.domain.ι (((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain).ι ≫ sec (𝕜 := 𝕜) k X)
        (by
          rw [Set.range_subset_iff]
          intro p
          exact ⟨⟨sec (𝕜 := 𝕜) k X ((sec (𝕜 := 𝕜) k X ⁻¹ᵁ a.domain).ι p), p.2⟩, rfl⟩) ≫ a.hom ≫
      pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (Y ↘ Spec (CommRingCat.of 𝕜)) := rfl

/-- The lift through the domain of `a` composed with the inclusion of the domain is the section,
restricted to the preimage. -/
theorem fibMap_lift_fac (k : ℕ) {X Y : Scheme.{0}} [X.Over (Spec (CommRingCat.of 𝕜))]
    [Y.Over (Spec (CommRingCat.of 𝕜))]
    (a : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).PartialMap (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k))
    (h : Dense (((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain : X.Opens) : Set X)) :
    IsOpenImmersion.lift a.domain.ι (((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain).ι ≫ sec (𝕜 := 𝕜) k X)
        (by
          rw [Set.range_subset_iff]
          intro p
          exact ⟨⟨sec (𝕜 := 𝕜) k X ((sec (𝕜 := 𝕜) k X ⁻¹ᵁ a.domain).ι p), p.2⟩, rfl⟩) ≫ a.domain.ι =
      ((sec (𝕜 := 𝕜) k X) ⁻¹ᵁ a.domain).ι ≫ sec (𝕜 := 𝕜) k X :=
  IsOpenImmersion.lift_fac _ _ _


/-- The preimage of an open subscheme along a morphism (notation-free version of `⁻¹ᵁ`, so that
statements about it can be written without opening the `AlgebraicGeometry` scoped notation). -/
abbrev preim {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) : X.Opens := f ⁻¹ᵁ U

end

end Work.CY3Stab.Prod
