import Mathlib
import Submission.Work.SSGRoute.ec_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSGRoute

open CategoryTheory Representation
open SSGRoute.PTExt

/-!
# The orbit-supported inclusion of the idèles

This module constructs, for a place `w₀` of `L`, the inclusion

`H : ∏_{v ∈ Gal(L/k)·w₀} L_vˣ ↪ 𝕀_L`

of the idèles supported on the `Gal(L/k)`-orbit of `w₀` into all idèles, together with a left
inverse `r : 𝕀_L ⟶ ∏_{v ∈ Gal(L/k)·w₀} L_vˣ` (the cut-down map `x ↦ x|_{O}`), and shows that the
localisation of `H` at any place `v` outside the orbit of `w₀` is the zero morphism.  This is the
statement `Work.SSGRoute.HasOrbitSupportedInclusion`.

The inclusion is `inclSupported ≫ levelIncl` (`S := orbitStable k L w₀`), the pair of the inclusion
of the idèles supported on `S` into the level `𝕀_L^S` and the inclusion of the level into `𝕀_L`.
The cut-down map is `restrictTo` of `NK.HassePrinciple.IdeleLevel`, which fixes every element of
the supported module.
-/

noncomputable section

variable (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

/-- **The inclusion of the idèles supported on the orbit of `w₀` into all idèles**, i.e. the
composite `∏_{v ∈ O} L_vˣ ↪ 𝕀_L^O ↪ 𝕀_L`. -/
noncomputable def orbitSupportHom (w₀ : NK.GlobalCFT.Place L) :
    orbitSupportedRep k L w₀ ⟶ idelesK k L :=
  NK.HassePrinciple.inclSupported k L (NK.HassePrinciple.orbitStable k L w₀) ≫
    NK.HassePrinciple.levelIncl k L (NK.HassePrinciple.orbitStable k L w₀)

/-- **The cut-down map `𝕀_L → ∏_{v ∈ O} L_vˣ`**: the idèle `x` with all components outside the
orbit `O = Gal(L/k)·w₀` of `w₀` replaced by `1`. -/
noncomputable def orbitCutHom (w₀ : NK.GlobalCFT.Place L) :
    NK.GlobalCFT.Idele L →*
      ↥(NK.HassePrinciple.supportedSubgroup (NK.HassePrinciple.placeOrbit k L w₀)) where
  toFun x := ⟨NK.HassePrinciple.restrictTo k L (NK.HassePrinciple.placeOrbit k L w₀) x,
    NK.HassePrinciple.restrictTo_mem_supported k L (NK.HassePrinciple.placeOrbit k L w₀) x⟩
  map_one' := Subtype.ext
    (NK.HassePrinciple.restrictTo_one k L (NK.HassePrinciple.placeOrbit k L w₀))
  map_mul' x y := Subtype.ext
    (NK.HassePrinciple.restrictTo_mul k L (NK.HassePrinciple.placeOrbit k L w₀) x y)

/-- The cut-down map is `Gal(L/k)`-equivariant. -/
theorem orbitCutHom_smul (w₀ : NK.GlobalCFT.Place L) (σ : L ≃ₐ[k] L)
    (x : NK.GlobalCFT.Idele L) :
    orbitCutHom k L w₀ (σ • x) = σ • orbitCutHom k L w₀ x :=
  Subtype.ext (NK.HassePrinciple.restrictTo_smul k L (NK.HassePrinciple.placeOrbit k L w₀)
    (NK.HassePrinciple.orbit_smul_mem w₀) σ x)

/-- The cut-down map, packaged as a morphism of `Gal(L/k)`-representations
`𝕀_L ⟶ ∏_{v ∈ Gal(L/k)·w₀} L_vˣ`. -/
noncomputable def orbitCut (w₀ : NK.GlobalCFT.Place L) :
    idelesK k L ⟶ orbitSupportedRep k L w₀ :=
  NK.HassePrinciple.repHomOfMonoidHom (orbitCutHom k L w₀) (orbitCutHom_smul k L w₀)

/-- **The cut-down map is a left inverse of the orbit-supported inclusion.**  On an idèle
supported on the orbit, `restrictTo` is the identity. -/
theorem orbitCut_comp_orbitSupportHom (w₀ : NK.GlobalCFT.Place L) :
    orbitSupportHom k L w₀ ≫ orbitCut k L w₀ = 𝟙 (orbitSupportedRep k L w₀) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (orbitCut k L w₀).hom ((orbitSupportHom k L w₀).hom x) = x
  change Additive.ofMul (orbitCutHom k L w₀
      (((Additive.toMul x : ↥(NK.HassePrinciple.supportedSubgroup
        (NK.HassePrinciple.placeOrbit k L w₀))) : NK.GlobalCFT.Idele L))) =
    Additive.ofMul (Additive.toMul x : ↥(NK.HassePrinciple.supportedSubgroup
        (NK.HassePrinciple.placeOrbit k L w₀)))
  congr 1
  apply Subtype.ext
  show NK.HassePrinciple.restrictTo k L (NK.HassePrinciple.placeOrbit k L w₀)
      ((Additive.toMul x : ↥(NK.HassePrinciple.supportedSubgroup
        (NK.HassePrinciple.placeOrbit k L w₀))) : NK.GlobalCFT.Idele L) =
    ((Additive.toMul x : ↥(NK.HassePrinciple.supportedSubgroup
        (NK.HassePrinciple.placeOrbit k L w₀))) : NK.GlobalCFT.Idele L)
  exact NK.HassePrinciple.restrictTo_eq_self_of_mem_supported k L (Additive.toMul x).2

/-- **The localisation of the orbit-supported inclusion at a place outside the orbit is zero.**
At such a place `v` every idèle supported on the orbit has `v`-component `1`, and the
`v`-component map is the underlying function of `ideleToLocalUnits`. -/
theorem orbitSupportHom_res_eq_zero (w₀ : NK.GlobalCFT.Place L) (v : NK.GlobalCFT.Place L)
    (hv : ∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ v) :
    Rep.resMap (decompK (k := k) v).subtype (orbitSupportHom k L w₀) ≫
      NK.HassePrinciple.ideleToLocalUnits k L v = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (NK.HassePrinciple.ideleToLocalUnits k L v).hom
      ((Rep.resMap (decompK (k := k) v).subtype (orbitSupportHom k L w₀)).hom x) = 0
  rw [Rep.resMap_hom_apply]
  change Additive.ofMul (((Additive.toMul x : ↥(NK.HassePrinciple.supportedSubgroup
      (NK.HassePrinciple.placeOrbit k L w₀))) : NK.GlobalCFT.Idele L) v) = 0
  rw [ofMul_eq_zero]
  have hvnot : v ∉ NK.HassePrinciple.placeOrbit k L w₀ := by
    rintro ⟨σ, hσ⟩
    exact hv σ hσ
  exact (NK.HassePrinciple.mem_supportedSubgroup.mp (Additive.toMul x).2) v hvnot

/-- **An orbit-supported inclusion of the idèles, with a left inverse.**

`HasOrbitSupportedInclusion k L w₀` (defined in `Submission.Work.SSGRoute.ec_defs`, which also
defines `orbitSupportedRep k L w₀ := NK.HassePrinciple.supportedRep k L (orbitStable k L w₀)`, the
group of idèles supported on the `Gal(L/k)`-orbit of `w₀`, i.e. with all components outside the
orbit equal to `1`) states: there are a `Gal(L/k)`-morphism `H : orbitSupportedRep k L w₀ ⟶ 𝕀_L`
and a left inverse `r : 𝕀_L ⟶ orbitSupportedRep k L w₀` (`H ≫ r = 𝟙`), such that for every place
`v` outside the orbit of `w₀` the localisation of `H`,
`Rep.resMap (decompK v).subtype H ≫ ideleToLocalUnits k L v`, is the zero morphism.

Suggested construction: `H := NK.HassePrinciple.inclSupported k L S ≫ NK.HassePrinciple.levelIncl k L S`
for `S := NK.HassePrinciple.orbitStable k L w₀` (the inclusion of the idèles supported on the orbit
into all idèles); the support condition follows from `∀ v ∉ O, ∀ x ∈ W, x v = 1`
(`NK.HassePrinciple.mem_supportedSubgroup`) and the fact that the underlying function of
`NK.HassePrinciple.ideleToLocalUnits k L v` is the `v`-component map
(`NK.HassePrinciple.ideleComponentHom`).  For the left inverse take the cut-down map
`x ↦ NK.HassePrinciple.restrictTo k L S.carrier x` (`NK.HassePrinciple.restrictTo_mul`,
`NK.HassePrinciple.restrictTo_smul`, `NK.HassePrinciple.restrictTo_mem_supported`,
`NK.HassePrinciple.restrictTo_eq_self_of_mem_supported`), packaged as a morphism of representations
`NK.HassePrinciple.ideleRep k L ⟶ orbitSupportedRep k L w₀` (every element of the supported module
is fixed by it). -/
theorem exists_orbit_supported_inclusion (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) : HasOrbitSupportedInclusion k L w₀ := by
  refine ⟨orbitSupportHom k L w₀, ?_, orbitCut k L w₀, ?_⟩
  · intro v hv
    exact orbitSupportHom_res_eq_zero k L w₀ v hv
  · exact orbitCut_comp_orbitSupportHom k L w₀

end

end Work.SSGRoute
