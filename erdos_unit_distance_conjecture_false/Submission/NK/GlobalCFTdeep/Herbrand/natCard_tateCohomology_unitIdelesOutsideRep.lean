import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.UnitIdelesDefs
import Submission.NK.RepresentationTheory.GroupCohomology.piCohomology_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_piRep

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory

set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.RepresentationTheory.GroupCohomology

attribute [local reducible] NK.RepresentationTheory.GroupCohomology.piRep
attribute [local reducible] NK.GlobalCFTdeep.fiberUnitsRep
attribute [local reducible] NK.GlobalCFTdeep.unitIdelesOutsideRep
attribute [local reducible] Rep.ofMulDistribMulAction
attribute [local reducible] Representation.ofMulDistribMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The place of `K` below a place of `L` outside `T` -/

/-- **The place of `K` below `w`**, for a place `w ∉ T`, as an element of the complement of
`S`.  Since `w ∉ T`, the place below `w` cannot lie in `S`. -/
noncomputable def placeUnderOut (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (w : Place L) (hw : w ∉ T) : {v : Place K // v ∉ S} :=
  ⟨Classical.choose (Inclusion.globalCFT_exists_placeUnder w),
    fun hvS => hw ((hTS w).mpr ⟨_, hvS,
      Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder w)⟩)⟩

theorem placeUnderOut_liesOver (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (w : Place L) (hw : w ∉ T) :
    Place.LiesOver w ((placeUnderOut S T hTS w hw : {v : Place K // v ∉ S}) : Place K) :=
  Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder w)

/-! ## Cutting an idèle down to the fibre of a place -/

/-- The underlying function of the idèle obtained from `x` by keeping only the components at the
places of `L` above `v`. -/
def fibreProjFun (v : Place K) (x : Idele L) : ∀ w : Place L, (Place.localField L w)ˣ := by
  intro w
  classical
  exact if Place.LiesOver w v then x w else 1

/-- **The idèle `x` cut down to the fibre of `v`**: same components as `x` above `v`, and `1`
elsewhere. -/
def fibreProj (v : Place K) (x : Idele L) : Idele L := by
  classical
  refine ⟨fibreProjFun v x, ?_⟩
  rw [Filter.eventually_cofinite]
  refine (Filter.eventually_cofinite.mp x.2).subset ?_
  intro w hw
  rw [Set.mem_ofPred_eq] at hw
  by_cases h : Place.LiesOver w v
  · rwa [show fibreProjFun v x w = x w from if_pos h] at hw
  · rw [show fibreProjFun v x w = 1 from if_neg h] at hw
    exact absurd (one_mem _) hw

theorem fibreProj_apply_of_mem {v : Place K} {w : Place L} (h : Place.LiesOver w v)
    (x : Idele L) : fibreProj v x w = x w := by
  classical
  change fibreProjFun v x w = x w
  exact if_pos h

theorem fibreProj_apply_of_notMem {v : Place K} {w : Place L} (h : ¬ Place.LiesOver w v)
    (x : Idele L) : fibreProj v x w = 1 := by
  classical
  change fibreProjFun v x w = 1
  exact if_neg h

/-- `fibreProj v` is multiplicative. -/
def fibreProjHom (v : Place K) : Idele L →* Idele L where
  toFun := fibreProj v
  map_one' := by
    classical
    ext w
    by_cases h : Place.LiesOver w v
    · rw [fibreProj_apply_of_mem h, Idele.one_apply]
    · rw [fibreProj_apply_of_notMem h, Idele.one_apply]
  map_mul' := by
    classical
    intro x y
    ext w
    by_cases h : Place.LiesOver w v
    · simp only [fibreProj_apply_of_mem h, Idele.mul_apply]
    · simp only [fibreProj_apply_of_notMem h, Idele.mul_apply, one_mul]

theorem fibreProjHom_apply (v : Place K) (x : Idele L) : fibreProjHom v x = fibreProj v x := rfl

theorem fibreProj_mul (v : Place K) (x y : Idele L) :
    fibreProj v (x * y) = fibreProj v x * fibreProj v y :=
  map_mul (fibreProjHom v) x y

theorem fibreProj_zpow (v : Place K) (x : Idele L) (n : ℤ) :
    fibreProj v (x ^ n) = fibreProj v x ^ n :=
  map_zpow (fibreProjHom v) x n

/-- The cut-down idèle lies in the unit part of the fibre of `v`. -/
theorem fibreProj_mem_fiberUnits (v : Place K) {x : Idele L}
    (hx : ∀ w : Place L, x w ∈ Place.localUnits L w) :
    fibreProj v x ∈ fiberUnits (K := K) (L := L) v := by
  rw [mem_fiberUnits]
  refine ⟨fun w hw => fibreProj_apply_of_notMem hw x, fun w => ?_⟩
  by_cases h : Place.LiesOver w v
  · rw [fibreProj_apply_of_mem h]; exact hx w
  · rw [fibreProj_apply_of_notMem h]; exact Subgroup.one_mem _

/-- The cut-down idèle is `Gal(L/K)`-equivariant. -/
theorem fibreProj_smul (v : Place K) (σ : L ≃ₐ[K] L) (x : Idele L) :
    fibreProj v (σ • x) = σ • fibreProj v x := by
  classical
  ext w
  rw [Idele.smul_apply]
  by_cases h : Place.LiesOver w v
  · rw [fibreProj_apply_of_mem h, Idele.smul_apply,
      fibreProj_apply_of_mem ((Place.liesOver_smul_iff (σ := σ⁻¹)).mpr h)]
  · rw [fibreProj_apply_of_notMem h,
      fibreProj_apply_of_notMem (fun hc => h ((Place.liesOver_smul_iff (σ := σ⁻¹)).mp hc)),
      map_one]

/-! ## The inverse: assembling a family of idèles into an idèle of `L` -/

/-- The underlying function of the idèle assembled from a family `y` of elements of the fibres:
at `w ∈ T` it is `1`, and at `w ∉ T` it is the `w`-component of the member of the family
indexed by the place below `w`. -/
def ofProdFunFun (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (y : ∀ v : {v : Place K // v ∉ S}, fiberUnits (K := K) (L := L) (v : Place K)) :
    ∀ w : Place L, (Place.localField L w)ˣ := by
  intro w
  classical
  exact if h : w ∈ T then 1 else ((y (placeUnderOut S T hTS w h) : Idele L) w)

/-- **The idèle assembled from a family in the fibres** (all of whose components are local
units). -/
def ofProdFun (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (y : ∀ v : {v : Place K // v ∉ S}, fiberUnits (K := K) (L := L) (v : Place K)) :
    Idele L := by
  classical
  refine ⟨ofProdFunFun S T hTS y, ?_⟩
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset Set.finite_empty ?_
  intro w hw
  rw [Set.mem_ofPred_eq] at hw
  by_cases h : w ∈ T
  · rw [show ofProdFunFun S T hTS y w = 1 from dif_pos h] at hw
    exact hw (one_mem _)
  · rw [show ofProdFunFun S T hTS y w =
        ((y (placeUnderOut S T hTS w h) : Idele L) w) from dif_neg h] at hw
    exact hw ((mem_fiberUnits.mp (y (placeUnderOut S T hTS w h)).2).2 w)

theorem ofProdFun_apply_of_mem {S : Finset (Place K)} {T : Set (Place L)}
    {hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v}
    {y : ∀ v : {v : Place K // v ∉ S}, fiberUnits (K := K) (L := L) (v : Place K)}
    {w : Place L} (hw : w ∈ T) : ofProdFun S T hTS y w = 1 := by
  classical
  change ofProdFunFun S T hTS y w = 1
  exact dif_pos hw

theorem ofProdFun_apply_of_notMem {S : Finset (Place K)} {T : Set (Place L)}
    {hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v}
    {y : ∀ v : {v : Place K // v ∉ S}, fiberUnits (K := K) (L := L) (v : Place K)}
    {w : Place L} (hw : w ∉ T) :
    ofProdFun S T hTS y w = ((y (placeUnderOut S T hTS w hw) : Idele L) w) := by
  classical
  change ofProdFunFun S T hTS y w = ((y (placeUnderOut S T hTS w hw) : Idele L) w)
  exact dif_neg hw

/-- The assembled idèle lies in the unit idèles outside `T`. -/
theorem ofProdFun_mem (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (y : ∀ v : {v : Place K // v ∉ S}, fiberUnits (K := K) (L := L) (v : Place K)) :
    ofProdFun S T hTS y ∈ unitIdelesOutside (L := L) T := by
  classical
  refine mem_unitIdelesOutside.mpr ⟨fun w hw => ofProdFun_apply_of_mem hw, fun w => ?_⟩
  by_cases h : w ∈ T
  · rw [ofProdFun_apply_of_mem h]; exact Subgroup.one_mem _
  · rw [ofProdFun_apply_of_notMem h]
    exact (mem_fiberUnits.mp (y (placeUnderOut S T hTS w h)).2).2 w

/-! ## The isomorphism `unitIdelesOutside T ≅ ∏_{v ∉ S} fiberUnits v` -/

section Iso

variable (S : Finset (Place K)) (T : Set (Place L))
variable (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
variable (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)

/-- **Restriction of a unit idèle outside `T` to the fibre of `v`**. -/
def unitIdelesToPiFun (x : unitIdelesOutside (L := L) T) :
    ∀ v : {v : Place K // v ∉ S}, fiberUnits (K := K) (L := L) (v : Place K) :=
  fun v => ⟨fibreProj (v : Place K) (x : Idele L), fibreProj_mem_fiberUnits _ x.2.2⟩

theorem unitIdelesToPiFun_val (x : unitIdelesOutside (L := L) T)
    (v : {v : Place K // v ∉ S}) :
    ((unitIdelesToPiFun S T x v : fiberUnits (K := K) (L := L) (v : Place K)) : Idele L) =
      fibreProj (v : Place K) (x : Idele L) := rfl

/-- The restriction is `Gal(L/K)`-equivariant. -/
theorem unitIdelesToPiFun_smul (σ : L ≃ₐ[K] L) (x : unitIdelesOutside (L := L) T)
    (v : {v : Place K // v ∉ S}) :
    unitIdelesToPiFun S T
        ⟨σ • (x : Idele L), smul_mem_unitIdelesOutside hT x.2⟩ v =
      ⟨σ • ((unitIdelesToPiFun S T x v : fiberUnits (K := K) (L := L)
          (v : Place K)) : Idele L),
        smul_mem_fiberUnits (unitIdelesToPiFun S T x v).2⟩ := by
  apply Subtype.ext
  exact fibreProj_smul (v : Place K) σ (x : Idele L)

theorem ofProdFun_unitIdelesToPiFun (x : unitIdelesOutside (L := L) T) :
    ofProdFun S T hTS (unitIdelesToPiFun S T x) = (x : Idele L) := by
  ext w
  by_cases hw : w ∈ T
  · rw [ofProdFun_apply_of_mem hw, x.2.1 w hw]
  · rw [ofProdFun_apply_of_notMem hw, unitIdelesToPiFun_val]
    rw [fibreProj_apply_of_mem (placeUnderOut_liesOver S T hTS w hw)]

theorem unitIdelesToPiFun_ofProdFun
    (y : ∀ v : {v : Place K // v ∉ S}, fiberUnits (K := K) (L := L) (v : Place K)) :
    unitIdelesToPiFun S T ⟨ofProdFun S T hTS y, ofProdFun_mem S T hTS y⟩ = y := by
  funext v
  apply Subtype.ext
  ext w
  by_cases hw : Place.LiesOver w (v : Place K)
  · rw [unitIdelesToPiFun_val, fibreProj_apply_of_mem hw]
    have hwT : w ∉ T := by
      intro hwT
      obtain ⟨v', hv'S, hv'⟩ := (hTS w).mp hwT
      exact v.2 (Inclusion.globalCFT_liesOver_unique hv' hw ▸ hv'S)
    rw [ofProdFun_apply_of_notMem hwT]
    rw [show placeUnderOut S T hTS w hwT = v from
      Subtype.ext (Inclusion.globalCFT_liesOver_unique
        (placeUnderOut_liesOver S T hTS w hwT) hw)]
  · rw [unitIdelesToPiFun_val, fibreProj_apply_of_notMem hw]
    rw [(mem_fiberUnits.mp (y v).2).1 w hw]

theorem unitIdelesOutsideRep_ρ_apply (σ : L ≃ₐ[K] L)
    (x : (unitIdelesOutsideRep (L := L) T hT).V) :
    (unitIdelesOutsideRep (L := L) T hT).ρ σ x =
      Additive.ofMul ⟨σ • ((Additive.toMul x : unitIdelesOutside (L := L) T) : Idele L),
        smul_mem_unitIdelesOutside hT (Additive.toMul x).2⟩ := rfl

theorem fiberUnitsRep_ρ_apply (v : Place K) (σ : L ≃ₐ[K] L)
    (y : (fiberUnitsRep (K := K) (L := L) v).V) :
    (fiberUnitsRep (K := K) (L := L) v).ρ σ y =
      Additive.ofMul ⟨σ • ((Additive.toMul y : fiberUnits (K := K) (L := L) v) : Idele L),
        smul_mem_fiberUnits (Additive.toMul y).2⟩ := rfl

/-- **The restriction map `unitIdelesOutside T ⟶ ∏_{v ∉ S} fiberUnits v`** as a
`ℤ`-linear map. -/
def unitIdelesToPiLinearMap :
    Additive (unitIdelesOutside (L := L) T) →ₗ[ℤ]
      ((v : {v : Place K // v ∉ S}) → Additive (fiberUnits (K := K) (L := L) (v : Place K))) :=
  { toFun := fun x => fun v => Additive.ofMul (unitIdelesToPiFun S T (Additive.toMul x) v)
    map_add' := by
      intro x y
      funext v
      show Additive.ofMul (unitIdelesToPiFun S T (Additive.toMul (x + y)) v) =
        Additive.ofMul (unitIdelesToPiFun S T (Additive.toMul x) v) +
          Additive.ofMul (unitIdelesToPiFun S T (Additive.toMul y) v)
      rw [toMul_add, ← ofMul_mul]
      apply congrArg Additive.ofMul
      apply Subtype.ext
      simp only [Subgroup.coe_mul, unitIdelesToPiFun_val, fibreProj_mul]
    map_smul' := by
      intro n x
      funext v
      show Additive.ofMul (unitIdelesToPiFun S T (Additive.toMul (n • x)) v) =
        n • Additive.ofMul (unitIdelesToPiFun S T (Additive.toMul x) v)
      rw [toMul_zsmul, ← ofMul_zpow]
      apply congrArg Additive.ofMul
      apply Subtype.ext
      simp only [Subgroup.coe_zpow, unitIdelesToPiFun_val, fibreProj_zpow] }

/-- **The isomorphism `unitIdelesOutside T ≅ ∏_{v ∉ S} fiberUnits v`** of
`ℤ[Gal(L/K)]`-modules. -/
theorem unitIdelesOutsideRep_iso_piRep
    (h : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    Nonempty (unitIdelesOutsideRep (L := L) T hT ≅
      piRep (fun v : {v : Place K // v ∉ S} =>
        fiberUnitsRep (K := K) (L := L) (v : Place K))) := by
  have hbij : Function.Bijective ⇑(unitIdelesToPiLinearMap S T) := by
    constructor
    · intro x y hxy
      have h2 : unitIdelesToPiFun S T (Additive.toMul x) =
          unitIdelesToPiFun S T (Additive.toMul y) := by
        funext v
        exact Additive.ofMul.injective (congrFun hxy v)
      have h3 := congrArg (ofProdFun S T h) h2
      rw [ofProdFun_unitIdelesToPiFun S T h (Additive.toMul x),
        ofProdFun_unitIdelesToPiFun S T h (Additive.toMul y)] at h3
      exact Additive.toMul.injective (Subtype.ext h3)
    · intro y
      refine ⟨Additive.ofMul ⟨ofProdFun S T h y, ofProdFun_mem S T h y⟩, ?_⟩
      funext v
      exact congrArg Additive.ofMul
        (congrFun (unitIdelesToPiFun_ofProdFun S T h y) v)
  let e : Additive (unitIdelesOutside (L := L) T) ≃ₗ[ℤ]
      ((v : {v : Place K // v ∉ S}) → Additive (fiberUnits (K := K) (L := L) (v : Place K))) :=
    LinearEquiv.ofBijective (unitIdelesToPiLinearMap S T) hbij
  have he : ∀ σ : L ≃ₐ[K] L, e.toLinearMap ∘ₗ
        (unitIdelesOutsideRep (L := L) T hT).ρ σ =
      (piRep (fun v : {v : Place K // v ∉ S} => fiberUnitsRep (K := K) (L := L)
        (v : Place K))).ρ σ ∘ₗ e.toLinearMap := by
    intro σ
    apply LinearMap.ext
    intro x
    funext v
    show Additive.ofMul (unitIdelesToPiFun S T
          (Additive.toMul ((unitIdelesOutsideRep (L := L) T hT).ρ σ x)) v) =
        (fiberUnitsRep (K := K) (L := L) (v : Place K)).ρ σ
          (Additive.ofMul (unitIdelesToPiFun S T (Additive.toMul x) v))
    rw [unitIdelesOutsideRep_ρ_apply, fiberUnitsRep_ρ_apply]
    exact congrArg Additive.ofMul
      (unitIdelesToPiFun_smul S T hT σ (Additive.toMul x) v)
  exact ⟨Rep.mkIso (Representation.Equiv.mk e he)⟩

end Iso

theorem natCard_tateCohomology_unitIdelesOutsideRep {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S)
    (n : ℤ) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) n) =
      Nat.card ((v : {v : NK.GlobalCFT.Place K // v ∉ S}) → tateCohomology
        (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : NK.GlobalCFT.Place K)) n) := by
  obtain ⟨e⟩ := unitIdelesOutsideRep_iso_piRep (K := K) (L := L) S T hT hTS
  calc Nat.card (tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) n)
      = Nat.card (tateCohomology (piRep (fun v : {v : NK.GlobalCFT.Place K // v ∉ S} =>
          NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : NK.GlobalCFT.Place K))) n) :=
        Nat.card_congr
          ((tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) n).mapIso e).toLinearEquiv.toEquiv
    _ = Nat.card ((v : {v : NK.GlobalCFT.Place K // v ∉ S}) → tateCohomology
          (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L)
            (v : NK.GlobalCFT.Place K)) n) :=
        tateCohomology_piRep (fun v : {v : NK.GlobalCFT.Place K // v ∉ S} =>
          NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : NK.GlobalCFT.Place K)) n

end NK.GlobalCFTdeep.Herbrand
