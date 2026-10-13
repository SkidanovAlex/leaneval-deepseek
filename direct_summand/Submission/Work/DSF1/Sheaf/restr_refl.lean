import Mathlib
import Submission.Work.DSF1.Sheaf.Beta

/-!
# `restr` at the identity inclusion

For an open `V` of a scheme `X`, the restriction map `restr (le_refl V)` of the Čech presheaf
`W ↦ (W.ι)_* 𝒪_W` (see `Submission/Work/DSF1/Sheaf/Beta.lean`) is the identity of `secSheaf V`.

The proof proceeds in three steps.

* The map `betaGen V V g : 𝒪_V ⟶ g_* 𝒪_V` (`g : V ⟶ V`, an open immersion) is the structure
  map; we only need the case `g = 𝟙 V`, where it is the canonical identification
  `(pushforwardId V).inv` of `𝒪_V` with its pushforward along the identity.
* Consequently the composite `restrAux V g hg := (V.ι)_* (betaGen V V g) ≫ (pushforwardCongr hg)`
  (which is `restr` for `g = X.homOfLE h` and `hg = Scheme.homOfLE_ι X h`) depends only on `g`;
  at `g = 𝟙 V` it is the identity because the pushforward along `𝟙 V ≫ V.ι = V.ι` is the
  pushforward along `V.ι` up to an isomorphism whose components are restriction maps of the
  structure sheaf along an inclusion of an open into itself, hence identity by thinness of
  `X.Opens`.
* Finally `X.homOfLE (le_refl V) = 𝟙 V` by `Scheme.homOfLE_rfl`, and we transport along this
  equation (`restrAux_congr`).
-/

namespace Work.DSF1.Sheaf

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace SheafOfModules

variable {X : Scheme.{u}}

set_option maxHeartbeats 1000000 in
/-- `betaGen V V (𝟙 V)` is the canonical identification of `𝒪_V` with its pushforward along the
identity morphism. -/
lemma betaGen_one (V : X.Opens) :
    betaGen V V (𝟙 V.toScheme) =
      (Scheme.Modules.pushforwardId V.toScheme).inv.app
        (SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  apply (SheafOfModules.unitHomEquiv _).injective
  have hL : (SheafOfModules.unitHomEquiv
      ((Scheme.Modules.pushforward (𝟙 V.toScheme)).obj
        (SheafOfModules.unit V.toScheme.ringCatSheaf)))
      (betaGen V V (𝟙 V.toScheme)) = betaSect V V (𝟙 V.toScheme) := by
    simp [betaGen]
  rw [hL]
  refine PresheafOfModules.sections_ext _ _ (fun W => ?_)
  erw [SheafOfModules.unitHomEquiv_apply_coe]

/-- An auxiliary model of `restr`: it only depends on the morphism `g : V ⟶ V` through which we
push forward, together with a proof that `g ≫ V.ι = V.ι` (which is what is needed to identify
`(V.ι)_* g_*` with `(V.ι)_*`). -/
noncomputable def restrAux (V : X.Opens) (g : V.toScheme ⟶ V.toScheme)
    (hg : g ≫ V.ι = V.ι) :
    Work.DSF1.secSheaf V ⟶ Work.DSF1.secSheaf V :=
  (Scheme.Modules.pushforward V.ι).map (betaGen V V g) ≫
    (Scheme.Modules.pushforwardCongr hg).hom.app (SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- `restrAux` only depends on the morphism `g`, not on the proof that `g ≫ V.ι = V.ι`
(which is a proof of a proposition). -/
lemma restrAux_congr (V : X.Opens) {g₁ g₂ : V.toScheme ⟶ V.toScheme} (e : g₁ = g₂)
    (h₁ : g₁ ≫ V.ι = V.ι) (h₂ : g₂ ≫ V.ι = V.ι) :
    restrAux V g₁ h₁ = restrAux V g₂ h₂ := by
  subst e
  rw [show h₂ = h₁ from Subsingleton.elim _ _]

set_option maxHeartbeats 1000000 in
/-- At `g = 𝟙 V` the auxiliary restriction map is the identity. -/
lemma restrAux_one (V : X.Opens) (hg₀ : 𝟙 V.toScheme ≫ V.ι = V.ι) :
    restrAux V (𝟙 V.toScheme) hg₀ = 𝟙 (Work.DSF1.secSheaf V) := by
  apply Scheme.Modules.hom_ext
  intro W
  -- The second factor of `restrAux` at `W` is the restriction of the structure sheaf of `V`
  -- along the inclusion `(𝟙 V ≫ V.ι) ⁻¹ᵁ W ⊆ V.ι ⁻¹ᵁ W`, which is the identity since the two
  -- opens are the same and `V.Opens` is a thin category.
  have key : ∀ (e' : ((𝟙 V.toScheme ≫ V.ι) ⁻¹ᵁ W) = (V.ι ⁻¹ᵁ W)),
      (Scheme.Modules.presheaf (SheafOfModules.unit V.toScheme.ringCatSheaf)).map
        (eqToHom e').op = 𝟙 _ := by
    intro e'
    rw [show eqToHom e' = 𝟙 _ from Subsingleton.elim _ _]
    erw [CategoryTheory.op_id]
    erw [CategoryTheory.Functor.map_id]
  erw [restrAux, Scheme.Modules.Hom.comp_app]
  erw [Scheme.Modules.pushforward_map_app]
  rw [betaGen_one V]
  erw [Scheme.Modules.pushforwardId_inv_app_app]
  erw [Category.id_comp]
  erw [Scheme.Modules.pushforwardCongr_hom_app_app]
  exact key _

set_option maxHeartbeats 1000000 in
theorem restr_refl (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens) :
    Work.DSF1.Sheaf.restr (X := X) (le_refl V) =
      CategoryTheory.CategoryStruct.id (Work.DSF1.secSheaf V) := by
  have h₁ : Work.DSF1.Sheaf.restr (X := X) (le_refl V) =
      restrAux V (X.homOfLE (le_refl V)) (Scheme.homOfLE_ι X (le_refl V)) := rfl
  rw [h₁, restrAux_congr V (Scheme.homOfLE_rfl X V)
    (Scheme.homOfLE_ι X (le_refl V)) (Category.id_comp V.ι)]
  exact restrAux_one V (Category.id_comp V.ι)

end Work.DSF1.Sheaf
