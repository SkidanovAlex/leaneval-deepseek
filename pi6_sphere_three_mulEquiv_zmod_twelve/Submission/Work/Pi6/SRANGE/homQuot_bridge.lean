import Mathlib
import Submission.Work.Pi6.SRANGE.QuotModel
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The concrete model `Zᵢ ⧸ Bᵢ` of the homology, and isomorphisms of homology maps

For a chain complex `K` of `R`-modules, `Hᵢ(K)` is the quotient of the `i`-cycles by the
`i`-boundaries.  This file relates the categorical map `HomologicalComplex.homologyMap h i`
induced by a chain map `h : K ⟶ L` to the concrete map `Work.Pi6.SRANGE.homQuotMap R h i`
on those quotients:

* `Work.Pi6.SRANGE.isoToLinearEquiv`, `Work.Pi6.SRANGE.homQuotEquiv` — the linear equivalence
  `Zᵢ ⧸ Bᵢ ≃ Hᵢ(K)` (`Work.Pi6.SRANGE.homQuotEquiv_apply_mk` records it on the class of a cycle);
* `Work.Pi6.SRANGE.homQuotMap_mk` — `homQuotMap` on the class of a cycle;
* `Work.Pi6.SRANGE.homologyMap_cyc_class` — the class of a cycle is carried by `homologyMap` to
  the class of its image (this is the element level form of the naturality of the model);
* `Work.Pi6.SRANGE.homQuotEquiv_naturality` — the naturality square expressing that
  `homologyMap h i` is `homQuotMap R h i` transported across the models;
* `Work.Pi6.SRANGE.homQuot_bridge` — consequently `homologyMap h i` is an isomorphism if and
  only if the concrete map `homQuotMap R h i` is a bijection.

The concrete model itself lives in `Submission/Work/Pi6/SRANGE/QuotModel.lean`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.SRANGE

noncomputable section

variable {R : Type} [CommRing R]

/-- A `ModuleCat` isomorphism seen as a linear equivalence of the underlying modules. -/
def isoToLinearEquiv {M N : ModuleCat.{0} R} (e : M ≅ N) : ↥M ≃ₗ[R] ↥N where
  toFun := e.hom.hom
  map_add' := e.hom.hom.map_add
  map_smul' := e.hom.hom.map_smul
  invFun := e.inv.hom
  left_inv := homIso_inv_apply e
  right_inv := homIso_hom_apply e

theorem isoToLinearEquiv_apply {M N : ModuleCat.{0} R} (e : M ≅ N) (x : ↥M) :
    isoToLinearEquiv e x = e.hom.hom x := rfl

/-- **The concrete quotient model `Zᵢ ⧸ Bᵢ` of the homology `Hᵢ(K)`.** -/
def homQuotEquiv (K : ChainComplex (ModuleCat.{0} R) ℕ) (i : ℕ) :
    homQuot R K i ≃ₗ[R] ↥(K.homology i) :=
  (Submodule.quotEquivOfEq (cycBnd K i) (LinearMap.range (bndMap K i))
      (cycBnd_eq_range K i)).trans (isoToLinearEquiv (homQuotIso K i).symm)

/-- The class of a cycle `z` corresponds to the class of `z` in `Hᵢ(K)`. -/
theorem homQuotEquiv_apply_mk (K : ChainComplex (ModuleCat.{0} R) ℕ) (i : ℕ)
    (z : ↥(cycKer K i)) :
    homQuotEquiv K i (Submodule.Quotient.mk z)
      = (K.homologyπ i).hom ((cycIso K i).inv.hom z) := by
  rw [homQuotEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    isoToLinearEquiv_apply]
  change (homQuotIso K i).inv.hom (Submodule.Quotient.mk z) = _
  simpa only [Submodule.mkQ_apply] using homQuotIso_inv_apply K i z

/-- `homQuotMap` on the class of a cycle. -/
theorem homQuotMap_mk {K L : ChainComplex (ModuleCat.{0} R) ℕ} (h : K ⟶ L) (i : ℕ)
    (z : ↥(cycKer K i)) :
    homQuotMap R h i (Submodule.Quotient.mk z) = Submodule.Quotient.mk (restrictMap h i z) := by
  rw [homQuotMap, Submodule.mapQ_apply]

/-- **The class of a cycle is carried to the class of its image.**  If `f : Zᵢ(K) → Zᵢ(L)` is
conjugate to `h.f i` on the underlying elements, then the `homologyMap` of the class of `z ∈ Zᵢ(K)`
is the class of `f z`. -/
theorem homologyMap_cyc_class {K L : ChainComplex (ModuleCat.{0} R) ℕ} (h : K ⟶ L) (i : ℕ)
    (f : ↥(cycKer K i) →ₗ[R] ↥(cycKer L i))
    (hf : ∀ z, (f z : ↥(L.X i)) = (h.f i).hom z) (z : ↥(cycKer K i)) :
    (HomologicalComplex.homologyMap h i).hom
        ((K.homologyπ i).hom ((cycIso K i).inv.hom z))
      = (L.homologyπ i).hom ((cycIso L i).inv.hom (f z)) := by
  have h1 : (HomologicalComplex.homologyMap h i).hom
        ((K.homologyπ i).hom ((cycIso K i).inv.hom z))
      = (L.homologyπ i).hom
          ((HomologicalComplex.cyclesMap h i) ((cycIso K i).inv.hom z)) := by
    have hh := congrArg (fun (m : K.cycles i ⟶ L.homology i) =>
      ModuleCat.Hom.hom m ((cycIso K i).inv.hom z))
      (HomologicalComplex.homologyπ_naturality h i)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  rw [h1]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp (inferInstance : Mono (L.iCycles i))
  rw [show (L.iCycles i).hom ((HomologicalComplex.cyclesMap h i) ((cycIso K i).inv.hom z))
      = (h.f i).hom ((K.iCycles i).hom ((cycIso K i).inv.hom z)) from by
        have hh := congrArg (fun (m : K.cycles i ⟶ L.X i) =>
          ModuleCat.Hom.hom m ((cycIso K i).inv.hom z)) (HomologicalComplex.cyclesMap_i h i)
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh,
    ← cycIso_hom_val L i ((cycIso L i).inv.hom (f z)), homIso_hom_apply (cycIso L i) (f z),
    ← cycIso_hom_val K i ((cycIso K i).inv.hom z), homIso_hom_apply (cycIso K i) z]
  exact (hf z).symm

/-- **Naturality of the concrete model of the homology.**  The map `homologyMap h i` is, under the
identifications `Zᵢ ⧸ Bᵢ ≃ Hᵢ`, the concrete map `homQuotMap R h i`: the square

`Zᵢ(K) ⧸ Bᵢ(K) --homQuotMap--> Zᵢ(L) ⧸ Bᵢ(L)`

`        |                                   |`

`     Hᵢ(K) ----homologyMap h i--------> Hᵢ(L)`

commutes. -/
theorem homQuotEquiv_naturality {K L : ChainComplex (ModuleCat.{0} R) ℕ} (h : K ⟶ L) (i : ℕ)
    (x : homQuot R K i) :
    (HomologicalComplex.homologyMap h i).hom (homQuotEquiv K i x)
      = homQuotEquiv L i (homQuotMap R h i x) := by
  refine Submodule.Quotient.induction_on (cycBnd K i) x ?_
  intro z
  rw [homQuotEquiv_apply_mk, homQuotMap_mk, homQuotEquiv_apply_mk]
  exact homologyMap_cyc_class h i (restrictMap h i) (fun z => restrictMap_apply_val h i z) z

/-- **The bridge between `homologyMap` and the concrete model.**  A chain map induces an
isomorphism on `Hᵢ` if and only if the concrete map `Zᵢ ⧸ Bᵢ → Zᵢ' ⧸ Bᵢ'` is a bijection. -/
theorem homQuot_bridge (R : Type) [CommRing R] {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    (h : K ⟶ L) (i : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap h i) ↔
      Function.Bijective (Work.Pi6.SRANGE.homQuotMap R h i) := by
  have hnat : ∀ x : homQuot R K i,
      ⇑(HomologicalComplex.homologyMap h i) (⇑(homQuotEquiv K i) x)
        = ⇑(homQuotEquiv L i) (⇑(homQuotMap R h i) x) := fun x =>
    homQuotEquiv_naturality h i x
  have hkey : ⇑(HomologicalComplex.homologyMap h i) ∘ ⇑(homQuotEquiv K i)
      = ⇑(homQuotEquiv L i) ∘ ⇑(homQuotMap R h i) := funext hnat
  rw [ConcreteCategory.isIso_iff_bijective]
  rw [← Function.Bijective.of_comp_iff (⇑(HomologicalComplex.homologyMap h i))
    (homQuotEquiv K i).bijective]
  rw [← Function.Bijective.of_comp_iff' (homQuotEquiv L i).bijective
    (⇑(Work.Pi6.SRANGE.homQuotMap R h i))]
  rw [hkey]

end

end Work.Pi6.SRANGE
