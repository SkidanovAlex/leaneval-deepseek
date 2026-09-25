import Mathlib
import Submission.Work.CFTLib.RelShafSESData
import Submission.Work.CFTLib.NKIdeles
import Submission.Work.CFTLib.oUnits_invariants_surjective
import Submission.Work.CFTLib.natCard_tateCohomology_localUnitIdelesRep
import Submission.Work.CFTLib.integralIdeles_principal_eq_units
import Submission.Work.CFTLib.idealClassMap_smul_apply

/-!
# The construction behind `Work.CFTLib.RelShafSESData`

The two short exact sequences of `ℤ[Gal(K/F)]`-modules

`1 → 𝒪_Kˣ → J_K → C'' → 1`,  `1 → C'' → C_K → Cl(𝓞 K) → 1`

cut out of the four-term idèle sequence `1 → 𝒪_Kˣ → J_K → C_K → Cl(𝓞 K) → 1` at
`C'' = im(J_K → C_K)`, together with their exactness.

The `Rep`-level exactness statements are obtained by reflecting along the faithful forgetful
functor `Rep ℤ G ⥤ ModuleCat ℤ`, which reduces them to elementwise statements about idèles.

Two environment quirks of the `Rep ℤ G` machinery have to be handled:

* the `Module ℤ`-instance diamond on the underlying types of a `Rep` (the structure field
  `Rep.hV2` versus the ambient `AddCommGroup.toIntModule`) is disambiguated by the local
  instance priority bump below;
* the underlying types of a `Rep` are only equal up to unfolding the definitions of the
  representations, so the `backward.isDefEq.respectTransparency` option is switched off, as in
  Mathlib's own `RepresentationTheory.Rep.Basic`.
-/

open scoped Classical
open NumberField CategoryTheory

noncomputable section

namespace Work.CFTLib

open NK.GlobalCFT

attribute [local instance 10000] Rep.hV2 Rep.hV1

set_option backward.isDefEq.respectTransparency false

namespace RelShafSES

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- The `Gal(K/F)`-action on the local-unit idèles `J_K = ∏_w 𝒪_{K_w}ˣ`.  The instance used to
build `jRep` is local to its definition; we install the same term globally so that the
equivariance lemmas can be stated. -/
noncomputable instance instMulDistribMulActionLocalUnitIdeles (F K : Type) [Field F]
    [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    MulDistribMulAction (K ≃ₐ[F] K) ↥(NK.GlobalCFTdeep.localUnitIdeles K) :=
  NK.GlobalCFTdeep.stableMulDistribMulAction (K ≃ₐ[F] K)
    (NK.GlobalCFTdeep.localUnitIdeles K)
    (fun σ x hx => NK.GlobalCFTdeep.smul_mem_localUnitIdeles hx)

/-! ## Idèle-level lemmas -/

/-- **The local-unit idèles are the integral idèles**: at an archimedean place every element is a
local unit. -/
theorem localUnitIdeles_eq_integralIdeles (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFTdeep.localUnitIdeles K = Idele.integralIdeles K := by
  refine le_antisymm NK.GlobalCFTdeep.localUnitIdeles_le_integralIdeles ?_
  intro x hx
  rw [NK.GlobalCFTdeep.mem_localUnitIdeles]
  rintro (w | q)
  · exact Place.mem_localUnits_ofInfinite
  · exact (Idele.mem_integralIdeles.mp hx) (Place.ofFinite q) (Place.isFinite_ofFinite q)

/-- The diagonal embedding `Kˣ → 𝕀_K` is injective. -/
theorem principalIdele_injective (K : Type) [Field K] [NumberField K] :
    Function.Injective (Idele.principalIdele K) := by
  intro x y h
  obtain ⟨v⟩ := (inferInstance : Nonempty (Place K))
  have hv : (Idele.principalIdele K x) v = (Idele.principalIdele K y) v := by rw [h]
  rw [Idele.principalIdele_apply, Idele.principalIdele_apply] at hv
  exact Units.map_injective (RingHom.injective (algebraMap K (Place.localField K v))) hv

/-- The principal idèle attached to a unit of `𝓞 K` is a local-unit idèle. -/
theorem principalIdele_units_mem (K : Type) [Field K] [NumberField K] (u : (𝓞 K)ˣ) :
    Idele.principalIdele K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
      ∈ NK.GlobalCFTdeep.localUnitIdeles K := by
  rw [localUnitIdeles_eq_integralIdeles]
  refine (Idele.idealOf_eq_one_iff _).mp ?_
  rw [Idele.idealOf_principalIdele]
  have h : (((Units.map (algebraMap (𝓞 K) K).toMonoidHom u : Kˣ) : K))
      = algebraMap (𝓞 K) K (u : 𝓞 K) := rfl
  rw [h, ← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit]
  rfl

/-- The diagonal embedding `𝒪_Kˣ → J_K` of the global units into the local-unit idèles,
as a monoid homomorphism. -/
def unitsToLocalUnitIdelesHom (K : Type) [Field K] [NumberField K] :
    (𝓞 K)ˣ →* NK.GlobalCFTdeep.localUnitIdeles K :=
  MonoidHom.codRestrict ((Idele.principalIdele K).comp
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom)) (NK.GlobalCFTdeep.localUnitIdeles K)
    (fun u => principalIdele_units_mem K u)

@[simp] theorem unitsToLocalUnitIdelesHom_apply (K : Type) [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) :
    ((unitsToLocalUnitIdelesHom K u : NK.GlobalCFTdeep.localUnitIdeles K) : Idele K)
      = Idele.principalIdele K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := rfl

/-- **The intertwining identity for `𝒪_Kˣ → J_K`.** -/
theorem unitsToLocalUnitIdelesHom_smul (g : K ≃ₐ[F] K) (u : (𝓞 K)ˣ) :
    unitsToLocalUnitIdelesHom K (g • u) =
      g • unitsToLocalUnitIdelesHom K u := by
  apply Subtype.ext
  show Idele.principalIdele K (Units.map (algebraMap (𝓞 K) K).toMonoidHom (g • u)) =
    g • Idele.principalIdele K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
  have h1 : (Units.map (algebraMap (𝓞 K) K).toMonoidHom (g • u) : Kˣ)
      = Units.map g.toMulEquiv.toMonoidHom
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := by
    ext
    show (algebraMap (𝓞 K) K) (((mapAlgEquivMonoidHom F K g) u : 𝓞 K))
      = g ((algebraMap (𝓞 K) K) (u : 𝓞 K))
    rfl
  rw [h1, ← NK.GlobalCFT.Galois.globalCFT_smul_principalIdele]

/-! ## A representation morphism out of an equivariant monoid homomorphism -/

section RepHom

variable {Γ M N : Type} [Group Γ] [CommGroup M] [CommGroup N]
  [MulDistribMulAction Γ M] [MulDistribMulAction Γ N]

/-- **A morphism of `ℤ[Γ]`-modules out of a `Γ`-equivariant monoid homomorphism**
`f : M →* N`: the induced additive map `Additive M →+ Additive N`, which intertwines the
actions by equivariance of `f`. -/
noncomputable def repHomOfMulDistribMulAction (f : M →* N)
    (hf : ∀ (σ : Γ) (x : M), f (σ • x) = σ • f x) :
    Rep.ofMulDistribMulAction Γ M ⟶ Rep.ofMulDistribMulAction Γ N :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (f (Additive.toMul x))
      map_add' := fun x y => by
        show Additive.ofMul (f (Additive.toMul (x + y))) =
          Additive.ofMul (f (Additive.toMul x)) + Additive.ofMul (f (Additive.toMul y))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        show Additive.ofMul (f (Additive.toMul (n • x))) =
          n • Additive.ofMul (f (Additive.toMul x))
        rw [toMul_zsmul, map_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (f (σ • Additive.toMul x)) =
          Additive.ofMul (σ • f (Additive.toMul x))
        rw [hf] }

@[simp] theorem repHomOfMulDistribMulAction_apply (f : M →* N)
    (hf : ∀ (σ : Γ) (x : M), f (σ • x) = σ • f x) (x : Additive M) :
    (repHomOfMulDistribMulAction f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

end RepHom

/-! ## The morphisms `𝒪_Kˣ → J_K → C_K` of `ℤ[Gal(K/F)]`-modules -/

/-- The equivariance of the quotient map `J_K → C_K`. -/
theorem mk_smul (g : K ≃ₐ[F] K) (x : ↥(NK.GlobalCFTdeep.localUnitIdeles K)) :
    IdeleClassGroup.mk K (g • (x : Idele K)) = g • IdeleClassGroup.mk K (x : Idele K) :=
  (IdeleClassGroup.smul_mk g (x : Idele K)).symm

/-- The equivariance of the ideal class map `C_K → Cl(𝓞 K)`. -/
theorem idealClassHom_smul (g : K ≃ₐ[F] K) (q : IdeleClassGroup K) :
    IdeleClassGroup.idealClassHom K (g • q)
      = clEquiv F K g (IdeleClassGroup.idealClassHom K q) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K q
  rw [IdeleClassGroup.smul_mk]
  have h1 : IdeleClassGroup.idealClassHom K (IdeleClassGroup.mk K (g • x))
      = IdeleClassGroup.idealClassMap K (g • x) :=
    QuotientGroup.lift_mk' _ _ _
  have h2 : IdeleClassGroup.idealClassHom K (IdeleClassGroup.mk K x)
      = IdeleClassGroup.idealClassMap K x :=
    QuotientGroup.lift_mk' _ _ _
  rw [h1, h2]
  exact idealClassMap_smul_apply (F := F) (K := K) g x

/-- The diagonal embedding `𝒪_Kˣ → J_K`, as a morphism of `ℤ[Gal(K/F)]`-modules. -/
def unitsToUnitIdeles (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : oUnitsRep F K ⟶ jRep F K :=
  repHomOfMulDistribMulAction (Γ := K ≃ₐ[F] K) (unitsToLocalUnitIdelesHom K)
    (fun g u => unitsToLocalUnitIdelesHom_smul (F := F) (K := K) g u)

@[simp] theorem unitsToUnitIdeles_apply (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] (u : Additive (𝓞 K)ˣ) :
    (unitsToUnitIdeles F K).hom u
      = Additive.ofMul (⟨Idele.principalIdele K
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom (Additive.toMul u)),
        principalIdele_units_mem K (Additive.toMul u)⟩ :
          ↥(NK.GlobalCFTdeep.localUnitIdeles K)) :=
  repHomOfMulDistribMulAction_apply _ _ u

/-- The quotient map `J_K → C_K`, as a morphism of `ℤ[Gal(K/F)]`-modules. -/
def unitIdelesToClassGroup (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : jRep F K ⟶ IdeleClassGroup.rep F K :=
  repHomOfMulDistribMulAction (Γ := K ≃ₐ[F] K)
    ((IdeleClassGroup.mk K).comp (NK.GlobalCFTdeep.localUnitIdeles K).subtype)
    (fun g x => mk_smul (F := F) (K := K) g x)

@[simp] theorem unitIdelesToClassGroup_apply (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] (x : Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K)) :
    (unitIdelesToClassGroup F K).hom x = Additive.ofMul (IdeleClassGroup.mk K
      ((Additive.toMul x : ↥(NK.GlobalCFTdeep.localUnitIdeles K)) : Idele K)) :=
  repHomOfMulDistribMulAction_apply _ _ x

/-- The ideal class map `C_K → Cl(𝓞 K)`, as a morphism of `ℤ[Gal(K/F)]`-modules. -/
def classGroupToClRep (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : IdeleClassGroup.rep F K ⟶ clRep F K :=
  repHomOfMulDistribMulAction (Γ := K ≃ₐ[F] K) (IdeleClassGroup.idealClassHom K)
    (fun g q => idealClassHom_smul (F := F) (K := K) g q)

@[simp] theorem classGroupToClRep_apply (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] (v : Additive (IdeleClassGroup K)) :
    (classGroupToClRep F K).hom v
      = Additive.ofMul (IdeleClassGroup.idealClassHom K (Additive.toMul v)) :=
  repHomOfMulDistribMulAction_apply _ _ v

/-! ## The intermediate module `C'' = im(J_K → C_K)` -/

/-- The range of `J_K → C_K` inside `C_K`. -/
abbrev rangeSubmodule (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Submodule ℤ (IdeleClassGroup.rep F K) :=
  LinearMap.range (unitIdelesToClassGroup F K).hom.toLinearMap

theorem mem_rangeSubmodule_iff (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (x : Additive (IdeleClassGroup K)) :
    x ∈ rangeSubmodule F K ↔ ∃ y, (unitIdelesToClassGroup F K).hom y = x :=
  LinearMap.mem_range

/-- The range of `J_K → C_K` is `Gal(K/F)`-stable. -/
theorem rangeSubmodule_le_comap (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (g : K ≃ₐ[F] K) :
    rangeSubmodule F K ≤ (rangeSubmodule F K).comap ((IdeleClassGroup.rep F K).ρ g) := by
  intro x hx
  rw [Submodule.mem_comap]
  obtain ⟨y, rfl⟩ := (mem_rangeSubmodule_iff F K x).mp hx
  exact (mem_rangeSubmodule_iff F K _).mpr ⟨(jRep F K).ρ g y,
    Rep.hom_comm_apply (unitIdelesToClassGroup F K) g y⟩

/-- **The intermediate module** `C'' = im(J_K → C_K)`, as a `ℤ[Gal(K/F)]`-module. -/
abbrev Cpp (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    Rep ℤ (K ≃ₐ[F] K) :=
  (IdeleClassGroup.rep F K).subrepresentation (rangeSubmodule F K) (rangeSubmodule_le_comap F K)

/-- The inclusion `C'' → C_K` of `ℤ[Gal(K/F)]`-modules. -/
def ses2f (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    Cpp F K ⟶ IdeleClassGroup.rep F K :=
  (IdeleClassGroup.rep F K).subtype (rangeSubmodule F K) (rangeSubmodule_le_comap F K)

@[simp] theorem ses2f_apply (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (w : ↥(rangeSubmodule F K)) :
    ((ses2f F K).hom w : Additive (IdeleClassGroup K)) = w.1 := rfl

/-- The action on `C''`. -/
theorem Cpp_ρ_apply (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (g : K ≃ₐ[F] K) (w : ↥(rangeSubmodule F K)) :
    (Cpp F K).ρ g w = ⟨(IdeleClassGroup.rep F K).ρ g w.1,
      rangeSubmodule_le_comap F K g w.2⟩ := rfl

/-- The map `J_K → C''`. -/
def jToRange (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K) →+ ↥(rangeSubmodule F K) where
  toFun x := ⟨(unitIdelesToClassGroup F K).hom x, (mem_rangeSubmodule_iff F K _).mpr ⟨x, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

@[simp] theorem jToRange_apply (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (x : Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K)) :
    jToRange F K x
      = ⟨(unitIdelesToClassGroup F K).hom x, (mem_rangeSubmodule_iff F K _).mpr ⟨x, rfl⟩⟩ := rfl

/-- The intertwining identity for `J_K → C''`. -/
theorem jToRange_intertwine (g : K ≃ₐ[F] K)
    (v : Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K)) :
    (jToRange F K) ((jRep F K).ρ g v) = (Cpp F K).ρ g ((jToRange F K) v) := by
  have h : (Cpp F K).ρ g (jToRange F K v)
      = ⟨(unitIdelesToClassGroup F K).hom ((jRep F K).ρ g v),
          (mem_rangeSubmodule_iff F K _).mpr ⟨(jRep F K).ρ g v, rfl⟩⟩ := by
    rw [Cpp_ρ_apply]
    refine Subtype.ext ?_
    show (IdeleClassGroup.rep F K).ρ g (jToRange F K v).1
      = (unitIdelesToClassGroup F K).hom ((jRep F K).ρ g v)
    rw [show (jToRange F K v).1 = (unitIdelesToClassGroup F K).hom v from rfl]
    exact (Rep.hom_comm_apply (unitIdelesToClassGroup F K) g v).symm
  rw [h]
  rfl

/-- The map `J_K → C''` as a morphism of `ℤ[Gal(K/F)]`-modules. -/
def ses1g (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    jRep F K ⟶ Cpp F K :=
  Rep.ofHom
    { toFun := fun x => jToRange F K x
      map_add' := fun x y => map_add (jToRange F K) x y
      map_smul' := fun n x => (jToRange F K).map_zsmul n x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show jToRange F K ((jRep F K).ρ σ x) = (Cpp F K).ρ σ (jToRange F K x)
        exact jToRange_intertwine (F := F) (K := K) σ x }

@[simp] theorem ses1g_apply (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (x : Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K)) :
    (ses1g F K).hom x
      = ⟨(unitIdelesToClassGroup F K).hom x, (mem_rangeSubmodule_iff F K _).mpr ⟨x, rfl⟩⟩ := rfl

/-- The composite `J_K → C_K → Cl(𝓞 K)` is zero. -/
theorem unitIdelesToClassGroup_comp_classGroupToClRep (F K : Type) [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] :
    unitIdelesToClassGroup F K ≫ classGroupToClRep F K = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rw [Rep.hom_comp, Rep.zero_hom]
  apply LinearMap.ext
  intro x
  show (classGroupToClRep F K).hom ((unitIdelesToClassGroup F K).hom x) = 0
  rw [unitIdelesToClassGroup_apply, classGroupToClRep_apply, ofMul_eq_zero]
  exact IdeleClassGroup.idealClassMap_eq_one_of_mem_integralIdeles
    (NK.GlobalCFTdeep.localUnitIdeles_le_integralIdeles (Additive.toMul x).2)

/-! ## The two short complexes -/

theorem ses1_zero (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : unitsToUnitIdeles F K ≫ ses1g F K = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rw [Rep.hom_comp, Rep.zero_hom]
  apply LinearMap.ext
  intro x
  show (ses1g F K).hom ((unitsToUnitIdeles F K).hom x) = 0
  refine Subtype.ext ?_
  show (unitIdelesToClassGroup F K).hom ((unitsToUnitIdeles F K).hom x) = 0
  rw [unitsToUnitIdeles_apply, unitIdelesToClassGroup_apply, toMul_ofMul, ofMul_eq_zero]
  exact QuotientGroup.eq_one_iff _ |>.mpr (Idele.mem_principalSubgroup.mpr ⟨_, rfl⟩)

theorem ses2_zero (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : ses2f F K ≫ classGroupToClRep F K = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rw [Rep.hom_comp, Rep.zero_hom]
  apply LinearMap.ext
  intro x
  show (classGroupToClRep F K).hom x.1 = 0
  obtain ⟨y, hy⟩ := (mem_rangeSubmodule_iff F K x.1).mp x.2
  rw [← hy]
  rw [← Rep.comp_apply, unitIdelesToClassGroup_comp_classGroupToClRep]
  simp

/-- **The short complex** `𝒪_Kˣ → J_K → C''`. -/
def ses1 (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    ShortComplex (Rep ℤ (K ≃ₐ[F] K)) :=
  ShortComplex.mk (unitsToUnitIdeles F K) (ses1g F K) (ses1_zero F K)

/-- **The short complex** `C'' → C_K → Cl(𝓞 K)`. -/
def ses2 (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    ShortComplex (Rep ℤ (K ≃ₐ[F] K)) :=
  ShortComplex.mk (ses2f F K) (classGroupToClRep F K) (ses2_zero F K)

/-! ## Exactness -/

theorem unitsToUnitIdeles_injective (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] : Function.Injective (unitsToUnitIdeles F K).hom := by
  intro x y h
  rw [unitsToUnitIdeles_apply, unitsToUnitIdeles_apply] at h
  have h2 := congrArg (fun t : Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K) =>
    ((Additive.toMul t : ↥(NK.GlobalCFTdeep.localUnitIdeles K)) : Idele K)) h
  simp only [toMul_ofMul, Subtype.coe_mk] at h2
  have h1 : Units.map (algebraMap (𝓞 K) K).toMonoidHom (Additive.toMul x)
      = Units.map (algebraMap (𝓞 K) K).toMonoidHom (Additive.toMul y) :=
    principalIdele_injective K h2
  have h3 : Additive.toMul x = Additive.toMul y :=
    Units.map_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K) h1
  rw [← ofMul_toMul x, ← ofMul_toMul y]
  exact congrArg Additive.ofMul h3

theorem ses1g_surjective_aux (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (y : ↥(rangeSubmodule F K)) : ∃ x, (ses1g F K).hom x = y := by
  obtain ⟨x, hx⟩ := (mem_rangeSubmodule_iff F K _).mp y.2
  refine ⟨x, ?_⟩
  rw [ses1g_apply]
  exact Subtype.ext hx

theorem ses1g_surjective (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Function.Surjective (ses1g F K).hom :=
  ses1g_surjective_aux F K

theorem ses1_exact_aux (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (x : Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K))
    (hx : (ses1g F K).hom x = 0) :
    ∃ y : Additive (𝓞 K)ˣ, (unitsToUnitIdeles F K).hom y = x := by
  have hj : (unitIdelesToClassGroup F K).hom x = 0 := by
    have h := hx
    rw [ses1g_apply] at h
    simpa using (Subtype.ext_iff.mp h)
  have hmk : IdeleClassGroup.mk K
      ((Additive.toMul x : ↥(NK.GlobalCFTdeep.localUnitIdeles K)) : Idele K) = 1 := by
    have h := hj
    rw [unitIdelesToClassGroup_apply, ofMul_eq_zero] at h
    exact h
  obtain ⟨u, hu⟩ := integralIdeles_principal_eq_units
    ((Additive.toMul x : ↥(NK.GlobalCFTdeep.localUnitIdeles K)) : Idele K)
    (NK.GlobalCFTdeep.localUnitIdeles_le_integralIdeles (Additive.toMul x).2) hmk
  refine ⟨(Additive.ofMul u : Additive (𝓞 K)ˣ), ?_⟩
  rw [unitsToUnitIdeles_apply, toMul_ofMul]
  have hx2 : x = Additive.ofMul (⟨Idele.principalIdele K
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom u),
      principalIdele_units_mem K u⟩ : ↥(NK.GlobalCFTdeep.localUnitIdeles K)) := by
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext hu
  rw [hx2]

theorem ses1_exact (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : (ses1 F K).Exact :=
  (forget₂ (Rep ℤ (K ≃ₐ[F] K)) (ModuleCat ℤ)).reflects_exact_of_faithful (ses1 F K)
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => ses1_exact_aux F K x hx)

theorem ses2f_injective (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Function.Injective (ses2f F K).hom := by
  intro x y h
  exact Subtype.ext h

theorem classGroupToClRep_surjective (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] : Function.Surjective (classGroupToClRep F K).hom := by
  intro y
  obtain ⟨q, hq⟩ := IdeleClassGroup.idealClassHom_surjective K (Additive.toMul y)
  refine ⟨(Additive.ofMul q : Additive (IdeleClassGroup K)), ?_⟩
  rw [classGroupToClRep_apply, toMul_ofMul]
  exact congrArg Additive.ofMul hq

theorem ses2_exact_aux (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (x : Additive (IdeleClassGroup K))
    (hx : (classGroupToClRep F K).hom x = 0) :
    ∃ y : ↥(rangeSubmodule F K), (ses2f F K).hom y = x := by
  have hker : (IdeleClassGroup.idealClassHom K) (Additive.toMul x) = 1 := by
    have h := hx
    rw [classGroupToClRep_apply, ofMul_eq_zero] at h
    exact h
  have hx' : Additive.toMul x ∈ (IdeleClassGroup.idealClassHom K).ker := by
    rw [MonoidHom.mem_ker]; exact hker
  rw [IdeleClassGroup.ker_idealClassHom] at hx'
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx'
  have ha' : a ∈ NK.GlobalCFTdeep.localUnitIdeles K := by
    rw [localUnitIdeles_eq_integralIdeles]; exact ha
  have hy : (unitIdelesToClassGroup F K).hom (Additive.ofMul (⟨a, ha'⟩ :
      ↥(NK.GlobalCFTdeep.localUnitIdeles K))) = x := by
    rw [unitIdelesToClassGroup_apply]
    show Additive.ofMul (IdeleClassGroup.mk K a) = x
    rw [hax]
    rfl
  exact ⟨⟨x, (mem_rangeSubmodule_iff F K x).mpr ⟨(Additive.ofMul (⟨a, ha'⟩ :
    ↥(NK.GlobalCFTdeep.localUnitIdeles K)) : Additive ↥(NK.GlobalCFTdeep.localUnitIdeles K)),
      hy⟩⟩, rfl⟩

theorem ses2_exact (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : (ses2 F K).Exact :=
  (forget₂ (Rep ℤ (K ≃ₐ[F] K)) (ModuleCat ℤ)).reflects_exact_of_faithful (ses2 F K)
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => ses2_exact_aux F K x hx)

theorem ses1_shortExact (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : (ses1 F K).ShortExact where
  exact := ses1_exact F K
  mono_f := (Rep.mono_iff_injective _).2 (unitsToUnitIdeles_injective F K)
  epi_g := (Rep.epi_iff_surjective _).2 (ses1g_surjective F K)

theorem ses2_shortExact (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : (ses2 F K).ShortExact where
  exact := ses2_exact F K
  mono_f := (Rep.mono_iff_injective _).2 (ses2f_injective F K)
  epi_g := (Rep.epi_iff_surjective _).2 (classGroupToClRep_surjective F K)

end RelShafSES

end Work.CFTLib
