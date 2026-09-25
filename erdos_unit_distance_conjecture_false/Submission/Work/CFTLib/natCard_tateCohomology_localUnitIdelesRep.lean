import Mathlib
import Submission.Work.CFTLib.NKHerbrand

/-!
# The unit idèles decompose over the fibres of the places of `K`

The group `localUnitIdeles L` of idèles of `L` all of whose components are local units
(`NK.GlobalCFTdeep.localUnitIdeles`) is the direct product, over the places `v` of `K`, of the
*unit parts of the fibres* `fiberUnits v = fiberIdeles v ⊓ localUnitIdeles L`
(`NK.GlobalCFTdeep.fiberUnits`):

  `localUnitIdeles L ≅ ∏_{v : Place K} fiberUnits v`.

The two maps are the projection `x ↦ (v ↦ x|_v)` (keeping the components above `v`) and the
gluing of a family, whose component at `w` is the component at `w` of the member of the family
indexed by the place of `K` below `w`.  Because every component of an element of `fiberUnits v`
is a local unit, the glued element is an idèle with *all* components local units, so no
finiteness assumption on the index type is needed.

The isomorphism is `Gal(L/K)`-equivariant for the diagonal action on the product and therefore
induces, through `NK.GlobalCFTdeep.Herbrand.tateCohomology_piRep` (Tate cohomology commutes with
products of representations), the identity

`Nat.card Ĥⁿ(Gal(L/K), 𝕀_L^unit) = Nat.card ∏_v Ĥⁿ(Gal(L/K), fiberUnits v)`

which is the main result of this file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Work.CFTLib

open NK.GlobalCFT NK.GlobalCFTdeep.Herbrand
open NK.RepresentationTheory.GroupCohomology (piRep piRep_ρ_apply)

attribute [local reducible] NK.GlobalCFTdeep.localUnitIdelesRep
attribute [local reducible] NK.GlobalCFTdeep.fiberUnitsRep
attribute [local reducible] NK.RepresentationTheory.GroupCohomology.piRep
attribute [local reducible] Rep.ofMulDistribMulAction
attribute [local reducible] Representation.ofMulDistribMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The place of `K` below a place of `L` -/

/-- The place of `K` below a given place of `L`. -/
noncomputable def luPlaceUnder (w : Place L) : Place K :=
  Classical.choose (Inclusion.globalCFT_exists_placeUnder w)

theorem luPlaceUnder_liesOver (w : Place L) :
    Place.LiesOver w (luPlaceUnder (K := K) w) :=
  Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder w)

theorem luPlaceUnder_eq {w : Place L} {v : Place K} (h : Place.LiesOver w v) :
    luPlaceUnder (K := K) w = v :=
  Inclusion.globalCFT_liesOver_unique (luPlaceUnder_liesOver w) h

/-! ## Gluing a family of fibre-supported idèles -/

/-- The `w`-component of the idèle glued from a family of elements of the unit parts of the
fibres: the `w`-component of the member of the family indexed by the place below `w`. -/
noncomputable def luGlueVal
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) (w : Place L) :
    (Place.localField L w)ˣ :=
  ((y (luPlaceUnder (K := K) w) :
      NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) (luPlaceUnder (K := K) w)) : Idele L) w

theorem luGlueVal_mem
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) (w : Place L) :
    luGlueVal (K := K) (L := L) y w ∈ Place.localUnits L w :=
  (NK.GlobalCFTdeep.mem_fiberUnits.mp (y (luPlaceUnder (K := K) w)).2).2 w

/-- **The gluing of a family of elements of the unit parts of the fibres**, as an idèle. -/
noncomputable def luGlueIdele
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) : Idele L :=
  ⟨luGlueVal (K := K) (L := L) y, Filter.Eventually.of_forall fun w => luGlueVal_mem y w⟩

theorem luGlueIdele_apply
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) (w : Place L) :
    luGlueIdele (K := K) (L := L) y w = luGlueVal (K := K) (L := L) y w := rfl

/-- The defining component formula for the glued idèle. -/
theorem luGlueIdele_apply_placeUnder
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) (w : Place L) :
    luGlueIdele (K := K) (L := L) y w =
      ((y (luPlaceUnder (K := K) w) :
        NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) (luPlaceUnder (K := K) w)) : Idele L) w :=
  rfl

theorem luGlueIdele_mem_localUnitIdeles
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) :
    luGlueIdele (K := K) (L := L) y ∈ NK.GlobalCFTdeep.localUnitIdeles L :=
  fun w => luGlueVal_mem y w

/-- The gluing, as an element of `localUnitIdeles L`. -/
noncomputable def luGlue
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) :
    NK.GlobalCFTdeep.localUnitIdeles L :=
  ⟨luGlueIdele (K := K) (L := L) y, luGlueIdele_mem_localUnitIdeles y⟩

/-! ## Cutting an idèle down to the fibre of a place of `K` -/

/-- **The projection to the fibre**: an idèle all of whose components are local units is sent to
its collection of fibres. -/
noncomputable def luProj (x : NK.GlobalCFTdeep.localUnitIdeles L) (v : Place K) :
    NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v :=
  ⟨fibreProj v (x : Idele L),
    fibreProj_mem_fiberUnits v (NK.GlobalCFTdeep.mem_localUnitIdeles.mp x.2)⟩

theorem luProj_val (x : NK.GlobalCFTdeep.localUnitIdeles L) (v : Place K) :
    ((luProj (K := K) (L := L) x v : NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) : Idele L) =
      fibreProj v (x : Idele L) := rfl

/-! ## The two maps are inverse to each other -/

theorem luGlue_luProj (x : NK.GlobalCFTdeep.localUnitIdeles L) :
    luGlue (K := K) (L := L) (luProj (K := K) (L := L) x) = x := by
  apply Subtype.ext
  apply Idele.ext
  intro w
  show luGlueIdele (K := K) (L := L) (luProj (K := K) (L := L) x) w = (x : Idele L) w
  rw [luGlueIdele_apply_placeUnder, luProj_val,
    fibreProj_apply_of_mem (luPlaceUnder_liesOver (K := K) w) (x : Idele L)]

theorem luProj_luGlue
    (y : (v : Place K) → NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) :
    luProj (K := K) (L := L) (luGlue (K := K) (L := L) y) = y := by
  funext v
  apply Subtype.ext
  apply Idele.ext
  intro w
  show (fibreProj v (luGlueIdele (K := K) (L := L) y)) w =
    ((y v : NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) : Idele L) w
  by_cases h : Place.LiesOver w v
  · rw [fibreProj_apply_of_mem h, luGlueIdele_apply_placeUnder, luPlaceUnder_eq h]
  · rw [fibreProj_apply_of_notMem h,
      (NK.GlobalCFTdeep.mem_fiberUnits.mp (y v).2).1 w h]

/-! ## Equivariance -/

theorem luProj_smul (σ : L ≃ₐ[K] L) (x : Idele L)
    (hx : x ∈ NK.GlobalCFTdeep.localUnitIdeles L) (v : Place K) :
    luProj (K := K) (L := L) ⟨σ • x, NK.GlobalCFTdeep.smul_mem_localUnitIdeles hx⟩ v =
      ⟨σ • ((luProj (K := K) (L := L) ⟨x, hx⟩ v : NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v) : Idele L),
        NK.GlobalCFTdeep.smul_mem_fiberUnits (luProj (K := K) (L := L) ⟨x, hx⟩ v).2⟩ := by
  apply Subtype.ext
  simp only [luProj_val]
  exact fibreProj_smul v σ x

/-! ## The `ℤ[Gal(L/K)]`-module isomorphism -/

/-- The projection to the family of fibres, as a `ℤ`-linear map. -/
noncomputable def luProjLinearMap :
    Additive (NK.GlobalCFTdeep.localUnitIdeles L) →ₗ[ℤ]
      ((v : Place K) → Additive (NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v)) where
  toFun x := fun v => Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul x) v)
  map_add' x y := by
    funext v
    show Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul (x + y)) v) =
      Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul x) v) +
        Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul y) v)
    rw [toMul_add, ← ofMul_mul]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    simp only [Subgroup.coe_mul, luProj_val, fibreProj_mul]
  map_smul' n x := by
    funext v
    show Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul (n • x)) v) =
      n • Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul x) v)
    rw [toMul_zsmul, ← ofMul_zpow]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    simp only [Subgroup.coe_zpow, luProj_val, fibreProj_zpow]

theorem localUnitIdelesRep_ρ_apply (σ : L ≃ₐ[K] L)
    (x : (NK.GlobalCFTdeep.localUnitIdelesRep (K := K) (L := L)).V) :
    (NK.GlobalCFTdeep.localUnitIdelesRep (K := K) (L := L)).ρ σ x =
      Additive.ofMul ⟨σ • ((Additive.toMul x : NK.GlobalCFTdeep.localUnitIdeles L) : Idele L),
        NK.GlobalCFTdeep.smul_mem_localUnitIdeles (Additive.toMul x).2⟩ := rfl

theorem luIsoPiRep :
    Nonempty (NK.GlobalCFTdeep.localUnitIdelesRep (K := K) (L := L) ≅
      piRep (fun v : Place K => NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v)) := by
  have hbij : Function.Bijective ⇑(luProjLinearMap (K := K) (L := L)) := by
    constructor
    · intro x y hxy
      have h2 : luProj (K := K) (L := L) (Additive.toMul x) = luProj (K := K) (L := L) (Additive.toMul y) := by
        funext v
        exact Additive.ofMul.injective (congrFun hxy v)
      have h3 := congrArg (luGlue) h2
      rw [luGlue_luProj, luGlue_luProj] at h3
      exact Additive.toMul.injective h3
    · intro y
      refine ⟨Additive.ofMul (luGlue (K := K) (L := L) y), ?_⟩
      funext v
      exact congrArg Additive.ofMul (congrFun (luProj_luGlue y) v)
  let e : Additive (NK.GlobalCFTdeep.localUnitIdeles L) ≃ₗ[ℤ]
      ((v : Place K) → Additive (NK.GlobalCFTdeep.fiberUnits (K := K) (L := L) v)) :=
    LinearEquiv.ofBijective (luProjLinearMap (K := K) (L := L)) hbij
  have he : ∀ σ : L ≃ₐ[K] L,
      e.toLinearMap ∘ₗ (NK.GlobalCFTdeep.localUnitIdelesRep (K := K) (L := L)).ρ σ =
        (piRep (fun v : Place K => NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v)).ρ σ ∘ₗ
          e.toLinearMap := by
    intro σ
    apply LinearMap.ext
    intro x
    funext v
    show Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul
          ((NK.GlobalCFTdeep.localUnitIdelesRep (K := K) (L := L)).ρ σ x)) v) =
        (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v).ρ σ
          (Additive.ofMul (luProj (K := K) (L := L) (Additive.toMul x) v))
    rw [localUnitIdelesRep_ρ_apply, fiberUnitsRep_ρ_apply]
    exact congrArg Additive.ofMul
      (luProj_smul (K := K) (L := L) σ
        ((Additive.toMul x : NK.GlobalCFTdeep.localUnitIdeles L) : Idele L)
        (Additive.toMul x : NK.GlobalCFTdeep.localUnitIdeles L).2 v)
  exact ⟨Rep.mkIso (Representation.Equiv.mk e he)⟩

/-! ## The main result -/

theorem natCard_tateCohomology_localUnitIdelesRep {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (n : ℤ) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.localUnitIdelesRep (K := K) (L := L)) n) =
      Nat.card ((v : NK.GlobalCFT.Place K) →
        tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) n) := by
  obtain ⟨e⟩ := luIsoPiRep (K := K) (L := L)
  calc Nat.card (tateCohomology (NK.GlobalCFTdeep.localUnitIdelesRep (K := K) (L := L)) n)
      = Nat.card (tateCohomology
          (piRep (fun v : Place K =>
            NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v)) n) :=
        Nat.card_congr
          (((tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) n).mapIso e).toLinearEquiv.toEquiv)
    _ = Nat.card ((v : Place K) →
          tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) n) :=
        tateCohomology_piRep
          (fun v : Place K => NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) n

end Work.CFTLib
