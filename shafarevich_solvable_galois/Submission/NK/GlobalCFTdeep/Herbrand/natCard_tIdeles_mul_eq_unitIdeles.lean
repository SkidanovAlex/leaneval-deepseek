import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.UnitIdelesDefs
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Herbrand-quotient identity for the decomposition `𝕀_{L,T} = ∏_{w|v} L_wˣ × ∏_{w ∉ T} U_w`

For a finite Galois extension `L/K` of number fields with cyclic Galois group and a
`Gal(L/K)`-stable set `T` of places of `L`, the `T`-idèles `𝕀_{L,T}` (idèles whose components
outside `T` are local units) fit into the short exact sequence

  `0 ⟶ ∏_{w ∉ T} U_w ⟶ 𝕀_{L,T} ⟶ ∏_{w ∈ T} L_wˣ ⟶ 0`

of `ℤ[Gal(L/K)]`-modules: the first map is the inclusion of the idèles which are `1` on `T`
(`unitIdelesOutside T`), the second is `x ↦ x · (supportedProj T x)⁻¹`, "keep the components on `T`
and put `1` outside `T`", which lands in the idèles supported on `T` (`supportedIdeles T`) and has
kernel exactly `unitIdelesOutside T`.

The Euler-characteristic (cardinality) identity attached to this sequence is the statement of
`natCard_tIdeles_mul_eq_unitIdeles`.

This file is deliberately self-contained: the short exact sequence and its exactness are built
here, on top of the delivered definitions `TIdeles`/`supportedIdeles`/`unitIdelesOutside` of
`Herbrand/UnitIdelesDefs.lean`, so that the target lemma does not depend on any work in progress.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand.NatCardSES

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### The projection "keep the components on `T`, put `1` outside `T`" -/

/-- The underlying function of `tdKeep T x`. -/
def tdKeepFun (T : Set (Place L)) (x : Idele L) :
    ∀ w : Place L, (Place.localField L w)ˣ := by
  intro w
  classical
  exact if w ∈ T then x w else 1

/-- The idèle obtained from `x` by keeping the components on `T` and putting `1` outside `T`. -/
def tdKeep (T : Set (Place L)) (x : Idele L) : Idele L := by
  classical
  refine ⟨tdKeepFun T x, ?_⟩
  rw [Filter.eventually_cofinite]
  refine (Filter.eventually_cofinite.mp x.2).subset ?_
  intro w hw
  rw [Set.mem_ofPred_eq] at hw
  by_cases h : w ∈ T
  · rw [show tdKeepFun T x w = x w from if_pos h] at hw
    exact hw
  · rw [show tdKeepFun T x w = 1 from if_neg h] at hw
    exact absurd (one_mem (Place.localUnits L w)) hw

theorem tdKeep_apply_of_mem {T : Set (Place L)} {w : Place L} (h : w ∈ T) (x : Idele L) :
    tdKeep T x w = x w := by
  classical
  change tdKeepFun T x w = x w
  exact if_pos h

theorem tdKeep_apply_of_notMem {T : Set (Place L)} {w : Place L} (h : w ∉ T) (x : Idele L) :
    tdKeep T x w = 1 := by
  classical
  change tdKeepFun T x w = 1
  exact if_neg h

/-- `tdKeep T` is a group homomorphism. -/
def tdKeepHom (T : Set (Place L)) : Idele L →* Idele L where
  toFun := tdKeep T
  map_one' := by
    ext w
    by_cases h : w ∈ T
    · simp only [tdKeep_apply_of_mem h, Idele.one_apply]
    · simp only [tdKeep_apply_of_notMem h, Idele.one_apply]
  map_mul' := by
    intro x y
    ext w
    by_cases h : w ∈ T
    · simp only [tdKeep_apply_of_mem h, Idele.mul_apply]
    · simp only [tdKeep_apply_of_notMem h, Idele.mul_apply, one_mul]

/-- `tdKeep` is `Gal(L/K)`-equivariant for a `Gal(L/K)`-stable `T`. -/
theorem tdKeep_smul {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) (x : Idele L) :
    tdKeep T (σ • x) = σ • tdKeep T x := by
  ext w
  rw [Idele.smul_apply]
  by_cases h : w ∈ T
  · rw [tdKeep_apply_of_mem h, Idele.smul_apply,
      tdKeep_apply_of_mem (hT (σ := σ⁻¹) h)]
  · rw [tdKeep_apply_of_notMem h,
      tdKeep_apply_of_notMem (fun hh => h (by simpa using hT (σ := σ) hh))]
    simp

/-- The projection lands in the idèles supported on `T`. -/
theorem tdKeep_mem_supportedIdeles (T : Set (Place L)) (x : Idele L) :
    tdKeep T x ∈ supportedIdeles (L := L) T :=
  fun w hw => tdKeep_apply_of_notMem hw x

/-- An idèle which is `1` on `T` is killed by the projection. -/
theorem tdKeep_eq_one_of_eq_one_on {T : Set (Place L)} {x : Idele L}
    (hx : ∀ w ∈ T, x w = 1) : tdKeep T x = 1 := by
  ext w
  by_cases h : w ∈ T
  · rw [tdKeep_apply_of_mem h, hx w h, Idele.one_apply]
  · rw [tdKeep_apply_of_notMem h, Idele.one_apply]

/-- The projection `𝕀_{L,T} → ∏_{w ∈ T} L_wˣ` as a group homomorphism. -/
def tdProjHom (T : Set (Place L)) :
    ↥(TIdeles T) →* ↥(supportedIdeles (L := L) T) where
  toFun x := ⟨tdKeep T (x : Idele L), tdKeep_mem_supportedIdeles T (x : Idele L)⟩
  map_one' := Subtype.ext (map_one (tdKeepHom T))
  map_mul' x y := Subtype.ext (map_mul (tdKeepHom T) (x : Idele L) (y : Idele L))

/-! ### The two morphisms of `ℤ[Gal(L/K)]`-modules -/

/-- **The projection `𝕀_{L,T} ⟶ ∏_{w ∈ T} L_wˣ`** of `ℤ[Gal(L/K)]`-modules. -/
def tdProjRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    tIdelesRep (L := L) T hT ⟶ supportedIdelesRep (L := L) T hT :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TIdeles T)
      (fun σ x hx => smul_mem_TIdeles hT hx)
  letI : MulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T)
      (fun σ x hx => smul_mem_supportedIdeles hT hx)
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (tdProjHom (L := L) T (Additive.toMul x))
      map_add' := by
        intro x y
        change Additive.ofMul (tdProjHom (L := L) T (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (tdProjHom (L := L) T (Additive.toMul x)) +
            Additive.ofMul (tdProjHom (L := L) T (Additive.toMul y))
        rw [map_mul]
        rfl
      map_smul' := by
        intro n x
        change Additive.ofMul (tdProjHom (L := L) T ((Additive.toMul x) ^ n)) =
          n • Additive.ofMul (tdProjHom (L := L) T (Additive.toMul x))
        rw [map_zpow]
        rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        apply Subtype.ext
        exact tdKeep_smul hT σ ((Additive.toMul x : ↥(TIdeles T)) : Idele L) }

/-- **The inclusion `∏_{w ∉ T} U_w ⟶ 𝕀_{L,T}`** of `ℤ[Gal(L/K)]`-modules. -/
def unitInclRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    unitIdelesOutsideRep (L := L) T hT ⟶ tIdelesRep (L := L) T hT :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (unitIdelesOutside T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (unitIdelesOutside T)
      (fun σ x hx => smul_mem_unitIdelesOutside hT hx)
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TIdeles T)
      (fun σ x hx => smul_mem_TIdeles hT hx)
  Rep.ofHom
    { toFun := fun x => Additive.ofMul
        (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T) (Additive.toMul x))
      map_add' := by
        intro x y
        change Additive.ofMul (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T)
            (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T) (Additive.toMul x)) +
            Additive.ofMul (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T) (Additive.toMul y))
        rw [map_mul]
        rfl
      map_smul' := by
        intro n x
        change Additive.ofMul (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T)
            ((Additive.toMul x) ^ n)) =
          n • Additive.ofMul
            (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T) (Additive.toMul x))
        rw [map_zpow]
        rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        apply Subtype.ext
        rfl }

/-! ### Short exactness -/

/-- The composite `∏_{w ∉ T} U_w ⟶ 𝕀_{L,T} ⟶ ∏_{w ∈ T} L_wˣ` is zero. -/
theorem unitIncl_comp_tdProj (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    unitInclRep (L := L) T hT ≫ tdProjRep (L := L) T hT = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Additive.ofMul.injective
  apply Subtype.ext
  show tdKeep T ((Additive.toMul x : ↥(unitIdelesOutside T)) : Idele L) = 1
  exact tdKeep_eq_one_of_eq_one_on (fun w hw => (Additive.toMul x).2.1 w hw)

/-- **Exactness in the middle**: a `T`-idèle killed by the projection is `1` on `T`. -/
theorem tdProj_eq_zero (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    {x : (tIdelesRep (L := L) T hT).V}
    (hx : (tdProjRep (L := L) T hT).hom x = 0) :
    ∃ y : (unitIdelesOutsideRep (L := L) T hT).V,
      (unitInclRep (L := L) T hT).hom y = x := by
  have h1 : tdProjHom (L := L) T (Additive.toMul x) = 1 := by
    have h2 : Additive.ofMul (tdProjHom (L := L) T (Additive.toMul x)) =
        (0 : Additive ↥(supportedIdeles (L := L) T)) := hx
    exact Additive.ofMul.injective (by simpa using h2)
  have h1' : tdKeep T ((Additive.toMul x : ↥(TIdeles T)) : Idele L) = 1 :=
    congrArg (fun q : ↥(supportedIdeles (L := L) T) => (q : Idele L)) h1
  have hone : ∀ w ∈ T, ((Additive.toMul x : ↥(TIdeles T)) : Idele L) w = 1 := by
    intro w hw
    have h3 := congrArg (fun z : Idele L => z w) h1'
    rwa [tdKeep_apply_of_mem hw, Idele.one_apply] at h3
  refine ⟨Additive.ofMul ⟨((Additive.toMul x : ↥(TIdeles T)) : Idele L), ?_⟩, ?_⟩
  · refine mem_unitIdelesOutside.mpr ⟨hone, fun w => ?_⟩
    by_cases h : w ∈ T
    · rw [hone w h]; exact one_mem _
    · exact (Additive.toMul x).2 w h
  · apply Additive.ofMul.injective
    apply Subtype.ext
    rfl

/-- The inclusion `∏_{w ∉ T} U_w ⟶ 𝕀_{L,T}` is injective. -/
theorem unitInclRep_injective (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    Function.Injective ⇑(Rep.Hom.hom (unitInclRep (L := L) T hT)) := by
  intro x y hxy
  have hxy' : Additive.ofMul (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T)
        (Additive.toMul x)) =
      Additive.ofMul (Subgroup.inclusion (unitIdelesOutside_le_TIdeles T)
        (Additive.toMul y)) := hxy
  have h2 : Subgroup.inclusion (unitIdelesOutside_le_TIdeles T) (Additive.toMul x) =
      Subgroup.inclusion (unitIdelesOutside_le_TIdeles T) (Additive.toMul y) :=
    Additive.ofMul.injective hxy'
  exact Additive.toMul.injective
    ((Subgroup.inclusion_injective (unitIdelesOutside_le_TIdeles T)) h2)

/-- The projection `𝕀_{L,T} ⟶ ∏_{w ∈ T} L_wˣ` is surjective. -/
theorem tdProjRep_surjective (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    Function.Surjective ⇑(Rep.Hom.hom (tdProjRep (L := L) T hT)) := by
  classical
  intro z
  set zz : Additive ↥(supportedIdeles (L := L) T) := z with hzz
  refine ⟨Additive.ofMul ⟨((Additive.toMul zz : ↥(supportedIdeles (L := L) T)) : Idele L), ?_⟩, ?_⟩
  · intro w hw
    rw [(Additive.toMul zz).2 w hw]
    exact one_mem _
  · apply Additive.ofMul.injective
    apply Subtype.ext
    show tdKeep T ((Additive.toMul zz : ↥(supportedIdeles (L := L) T)) : Idele L) =
      ((Additive.toMul zz : ↥(supportedIdeles (L := L) T)) : Idele L)
    ext w
    by_cases h : w ∈ T
    · rw [tdKeep_apply_of_mem h]
    · rw [tdKeep_apply_of_notMem h, (Additive.toMul zz).2 w h]

/-- **The short exact sequence** `0 ⟶ ∏_{w ∉ T} U_w ⟶ 𝕀_{L,T} ⟶ ∏_{w ∈ T} L_wˣ ⟶ 0` of
`ℤ[Gal(L/K)]`-modules. -/
abbrev ses (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    ShortComplex (Rep ℤ (L ≃ₐ[K] L)) where
  X₁ := unitIdelesOutsideRep (L := L) T hT
  X₂ := tIdelesRep (L := L) T hT
  X₃ := supportedIdelesRep (L := L) T hT
  f := unitInclRep (L := L) T hT
  g := tdProjRep (L := L) T hT
  zero := unitIncl_comp_tdProj (L := L) T hT

theorem ses_shortExact (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    (ses (L := L) T hT).ShortExact :=
  Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise _
    ((Rep.mono_iff_injective _).2 (unitInclRep_injective (L := L) T hT))
    ((Rep.epi_iff_surjective _).2 (tdProjRep_surjective (L := L) T hT))
    (fun x hx => tdProj_eq_zero (L := L) T hT hx)

end NK.GlobalCFTdeep.Herbrand.NatCardSES

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-- **The Herbrand-quotient identity attached to the decomposition
`𝕀_{L,T} = (∏_{w ∈ T} L_wˣ) × (∏_{w ∉ T} U_w)`.**

For a finite Galois extension `L/K` of number fields with cyclic Galois group, a `Gal(L/K)`-stable
set `T` of places of `L` and a finite set `S` of places of `K` whose fibres in `L` are exactly `T`,
the Euler-characteristic (cardinality) identity attached to the short exact sequence
`0 → ∏_{w ∉ T} U_w → 𝕀_{L,T} → ∏_{w ∈ T} L_wˣ → 0` holds:

`|Ĥ⁰(𝕀_{L,T})| · |Ĥ¹(∏_{w ∉ T} U_w)| · |Ĥ¹(∏_{w ∈ T} L_wˣ)|`
`  = |Ĥ⁰(∏_{w ∉ T} U_w)| · |Ĥ⁰(∏_{w ∈ T} L_wˣ)| · |Ĥ¹(𝕀_{L,T})|`. -/
theorem natCard_tIdeles_mul_eq_unitIdeles {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.tIdelesRep (L := L) T hT) 0) *
        Nat.card (tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) 1) *
        Nat.card (tateCohomology (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) 1)
      = Nat.card (tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) 0) *
        Nat.card (tateCohomology (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) 0) *
        Nat.card (tateCohomology (NK.GlobalCFTdeep.tIdelesRep (L := L) T hT) 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  -- The `CommGroup` structure refining the *ambient* `Group` structure, so that the
  -- `ℤ[Gal(L/K)]`-modules built from either structure are definitionally the same.
  exact @tateCohomology_mul_eq_of_shortExact_noFin (L ≃ₐ[K] L)
    { (inferInstance : Group (L ≃ₐ[K] L)) with
      mul_comm := by
        intro a b
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
        rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm] } _ _
    (NatCardSES.ses (L := L) T hT) (NatCardSES.ses_shortExact (L := L) T hT)

end NK.GlobalCFTdeep.Herbrand
