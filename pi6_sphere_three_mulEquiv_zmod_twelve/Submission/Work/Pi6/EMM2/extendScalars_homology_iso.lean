import Mathlib
import Submission.Work.Pi6.EMM2.expTensTF
import Submission.Work.Pi6.SRANGE.isZero_homology_baseChange_of_torsionFree
import Submission.Work.Pi6.SRANGE.intR_map_injective_of_torsionFree
import Submission.Work.Pi6.SRANGE.intR_map_ker_eq_range
import Submission.Work.Pi6.SRANGE.homQuot_bridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 100000

attribute [-instance] AddCommGroup.toIntModule
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

/-!
# Change of rings `ℤ → R` for the homology of a chain complex of free `ℤ`-modules, in one degree

For a commutative ring `R`, a chain complex `K` of free `ℤ`-modules and a degree `m` in which the
homology `H_m(K)` is torsion-free, the `(m+1)`-st homology of the coefficient extension
`K ⊗[ℤ] R` is the extension of scalars of `H_{m+1}(K)`:

`H_{m+1}(K ⊗[ℤ] R) ≅ R ⊗[ℤ] H_{m+1}(K)`.

The same statement over `ℤ` (`Work.Pi6.EMM2.expTens_homology_iso`) is proved by the
cycles/boundaries route: with `Z_{m+1} = ker d_{m+1}` and `B_{m+1} = im d_{m+2}` one identifies

`H_{m+1}(K ⊗ R) = (Z_{m+1} ⊗ R) / (B_{m+1} ⊗ R) ≅ (Z_{m+1}/B_{m+1}) ⊗ R = H_{m+1}(K) ⊗ R`.

Here the same argument is run in the `R`-linear world, using the base-change toolkit of
`Work.Pi6.SRANGE` (`bcMap`, right exactness `intR_map_ker_eq_range`, injectivity of the base change
of an inclusion with torsion-free cokernel `intR_map_injective_of_torsionFree` and the concrete
model `Work.Pi6.SRANGE.homQuot` of the homology).
-/

namespace Work.Pi6.EMM2

noncomputable section

/-! ## Torsion-freeness of the structural quotients -/

/-- `K_{m+1} ⧸ Z_{m+1}` is torsion-free: it is (isomorphic to) the `m`-boundaries, a submodule of
the free module `K_m`. -/
theorem extScal_tf_quot_uctZ (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i)) :
    Module.IsTorsionFree ℤ
      (↥(K.X (m + 1)) ⧸ LinearMap.range (Work.Cohomology.uctZ K (m + 1)).subtype) := by
  rw [Submodule.range_subtype]
  exact isTorsionFree_quot_uctZ K (m + 1) hfree

/-- `Z_m ⧸ B_m` is torsion-free, being `H_m(K)`. -/
theorem extScal_tf_quot_uctH (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Module.IsTorsionFree ℤ (↥(Work.Cohomology.uctZ K m) ⧸
      LinearMap.range (Submodule.inclusion (Work.Cohomology.uctB_le_uctZ K m))) := by
  rw [Work.Pi6.EMM2.range_inclusion_eq_uctH]
  exact isTorsionFree_quot_uctH K m hTF

/-! ## Injectivity of the base changes of the inclusions `B_m ⊆ Z_m ⊆ K_m` -/

/-- The base change of the inclusion `B_m ⊆ Z_m` is injective: the cokernel `Z_m ⧸ B_m ≅ H_m(K)`
is torsion-free, hence flat over `ℤ`. -/
theorem extScal_bcMap_inclusion_injective (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Function.Injective (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom
      (Submodule.inclusion (Work.Cohomology.uctB_le_uctZ K m)))) := by
  haveI hF : Module.Free ℤ (K.X m) := hfree m
  haveI : Module.IsTorsionFree ℤ ↥(Work.Cohomology.uctZ K m) :=
    isTorsionFree_subtype (Work.Cohomology.uctZ K m)
  refine Work.Pi6.SRANGE.intR_map_injective_of_torsionFree R
    (Submodule.inclusion (Work.Cohomology.uctB_le_uctZ K m)) ?_ inferInstance ?_
  · intro x y hxy
    have h := congrArg (fun z : ↥(Work.Cohomology.uctZ K m) => (z : ↥(K.X m))) hxy
    simpa using h
  · convert extScal_tf_quot_uctH K m hTF using 1
    exact Subsingleton.elim _ _

/-- The base change of the inclusion `Z_m ⊆ K_m` is injective: the cokernel `K_m ⧸ Z_m` is
torsion-free (it is the `(m-1)`-boundaries inside the free `K_{m-1}`). -/
theorem extScal_bcMap_uctZ_subtype_injective (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i)) :
    Function.Injective (Work.Pi6.SRANGE.bcMap R
      (ModuleCat.ofHom (Work.Cohomology.uctZ K m).subtype)) := by
  haveI hF : Module.Free ℤ (K.X m) := hfree m
  haveI : Module.IsTorsionFree ℤ ↥(K.X m) := inferInstance
  refine Work.Pi6.SRANGE.intR_map_injective_of_torsionFree R
    (Work.Cohomology.uctZ K m).subtype (Submodule.subtype_injective _) inferInstance ?_
  rw [Submodule.range_subtype]
  convert isTorsionFree_quot_uctZ K m hfree using 1
  exact Subsingleton.elim _ _

/-- The base change of the inclusion `B_m ⊆ K_m` is injective. -/
theorem extScal_bcMap_uctB_subtype_injective (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Function.Injective (Work.Pi6.SRANGE.bcMap R
      (ModuleCat.ofHom (Work.Cohomology.uctB K m).subtype)) := by
  have hfac : ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctB K m))
      = ModuleCat.ofHom (Submodule.inclusion (Work.Cohomology.uctB_le_uctZ K m))
        ≫ ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctZ K m)) := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  rw [hfac, Work.Pi6.SRANGE.bcMap_comp_tf]
  exact (extScal_bcMap_uctZ_subtype_injective R K m hfree).comp
    (extScal_bcMap_inclusion_injective R K m hfree hTF)

/-! ## The kernel of the base-changed differential in degree `m+1` -/

/-- **`ker (d_{m+1} ⊗ R) = Z_{m+1} ⊗ R`**, i.e. the base-changed cycles are the base change of
the cycles (here the torsion-freeness of `H_m` enters, through the injectivity of
`B_m ⊗ R → K_m ⊗ R`). -/
theorem extScal_ker_d_eq_range_uctZ (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    LinearMap.ker (Work.Pi6.SRANGE.bcMap R (K.d (m + 1) m))
      = LinearMap.range (Work.Pi6.SRANGE.bcMap R
          (ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctZ K (m + 1))))) := by
  set g : ↥(K.X (m + 1)) →ₗ[ℤ] ↥(Work.Cohomology.uctB K m) :=
    ((K.d (m + 1) m).hom).codRestrict _ (fun x => ⟨x, rfl⟩) with hgdef
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, Subtype.ext rfl⟩
  have hfac : ModuleCat.ofHom ((K.d (m + 1) m).hom)
      = ModuleCat.ofHom g ≫ ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctB K m)) := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  have hcomp : Work.Pi6.SRANGE.bcMap R (K.d (m + 1) m)
      = (Work.Pi6.SRANGE.bcMap R
          (ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctB K m)))).comp
        (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom g)) := by
    rw [← Work.Pi6.SRANGE.bcMap_comp_tf]
    exact congrArg (fun z => Work.Pi6.SRANGE.bcMap R z) hfac
  rw [hcomp, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.mpr (extScal_bcMap_uctB_subtype_injective R K m hfree hTF),
    Submodule.comap_bot]
  have hk : LinearMap.range (Submodule.subtype (Work.Cohomology.uctZ K (m + 1)))
      = LinearMap.ker g := by
    rw [Submodule.range_subtype]
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      exact Subtype.ext hx
    · intro hx
      exact congrArg Subtype.val hx
  exact Work.Pi6.SRANGE.intR_map_ker_eq_range R g hgsurj
    (Submodule.subtype (Work.Cohomology.uctZ K (m + 1))) hk

/-! ## The range of the base-changed differential in degree `m+2` -/

/-- **`im (d_{m+2} ⊗ R) = B_{m+1} ⊗ R`** (right exactness of `- ⊗[ℤ] R`, no flatness needed). -/
theorem extScal_range_d_eq_range_uctB (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ) :
    LinearMap.range (Work.Pi6.SRANGE.bcMap R (K.d (m + 2) (m + 1)))
      = LinearMap.range (Work.Pi6.SRANGE.bcMap R
          (ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctB K (m + 1))))) := by
  set g : ↥(K.X (m + 2)) →ₗ[ℤ] ↥(Work.Cohomology.uctB K (m + 1)) :=
    ((K.d (m + 2) (m + 1)).hom).codRestrict _ (fun x => ⟨x, rfl⟩) with hgdef
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, Subtype.ext rfl⟩
  have hfac : ModuleCat.ofHom ((K.d (m + 2) (m + 1)).hom)
      = ModuleCat.ofHom g ≫ ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctB K (m + 1))) := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  have hcomp : Work.Pi6.SRANGE.bcMap R (K.d (m + 2) (m + 1))
      = (Work.Pi6.SRANGE.bcMap R
          (ModuleCat.ofHom (Submodule.subtype (Work.Cohomology.uctB K (m + 1))))).comp
        (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom g)) := by
    rw [← Work.Pi6.SRANGE.bcMap_comp_tf]
    exact congrArg (fun z => Work.Pi6.SRANGE.bcMap R z) hfac
  rw [hcomp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (Work.Pi6.SRANGE.bcMap_surjective _ hgsurj), Submodule.map_top]

/-! ## The main theorem -/

theorem extendScalars_homology_iso (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ) (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Nonempty ((((ModuleCat.extendScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K).homology (m + 1) ≅
      (ModuleCat.extendScalars (Int.castRingHom R)).obj (K.homology (m + 1))) := by
  classical
  let F : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} R := ModuleCat.extendScalars (Int.castRingHom R)
  let C : ChainComplex (ModuleCat.{0} R) ℕ := Work.Pi6.SRANGE.baseChange R K
  set Z : Submodule ℤ ↥(K.X (m + 1)) := Work.Cohomology.uctZ K (m + 1) with hZdef
  set B : Submodule ℤ ↥(K.X (m + 1)) := Work.Cohomology.uctB K (m + 1) with hBdef
  have hBZ : B ≤ Z := Work.Cohomology.uctB_le_uctZ K (m + 1)
  set ι : ↥B →ₗ[ℤ] ↥Z := Submodule.inclusion hBZ with hιdef
  -- the map `Z ⊗ R → C_{m+1}` and its injectivity
  set f : ↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ ↥Z)) →ₗ[R] ↥(C.X (m + 1)) :=
    Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom (Submodule.subtype Z)) with hfdef
  have hfinj : Function.Injective f := by
    rw [hfdef]
    exact extScal_bcMap_uctZ_subtype_injective R K (m + 1) hfree
  -- the cycles of `C` in degree `m+1`
  have hcyc : LinearMap.ker (Work.Pi6.SRANGE.bcMap R (K.d (m + 1) m))
      = LinearMap.range f := by
    rw [hfdef]
    exact extScal_ker_d_eq_range_uctZ R K m hfree hTF
  -- `f` lands in the cycles
  have hmem : ∀ y : ↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ ↥Z)),
      f y ∈ Work.Pi6.SRANGE.cycKer C (m + 1) := by
    intro y
    have h1 : f y ∈ LinearMap.ker (Work.Pi6.SRANGE.bcMap R (K.d (m + 1) m)) := by
      rw [hcyc]
      exact ⟨y, rfl⟩
    change f y ∈ LinearMap.ker (C.d (m + 1) (m + 1 - 1)).hom
    rw [Work.Pi6.SRANGE.baseChange_d_eq_bcMap]
    exact h1
  -- the quotient map `Z ⊗ R → Z ⧸ B ⊗ R` of the `Φ`-route
  set Ψ : ↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ ↥Z)) →ₗ[R]
      Work.Pi6.SRANGE.homQuot R C (m + 1) :=
    (Submodule.mkQ (Work.Pi6.SRANGE.cycBnd C (m + 1))).comp (f.codRestrict _ hmem) with hΨdef
  -- the range of the boundary inclusion is the image of `B ⊗ R`
  have hmap : LinearMap.range (Work.Pi6.SRANGE.bcMap R
        (ModuleCat.ofHom (Submodule.subtype B)))
      = Submodule.map f (LinearMap.range (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom ι))) := by
    have hb : ModuleCat.ofHom (Submodule.subtype B)
        = ModuleCat.ofHom ι ≫ ModuleCat.ofHom (Submodule.subtype Z) := by
      apply ModuleCat.hom_ext
      ext x
      rfl
    rw [hb, Work.Pi6.SRANGE.bcMap_comp_tf, LinearMap.range_comp]
  -- the kernel of `Ψ` is the image of `B ⊗ R → Z ⊗ R`
  have hker : LinearMap.ker Ψ
      = LinearMap.range (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom ι)) := by
    ext y
    rw [hΨdef, LinearMap.mem_ker]
    show Submodule.Quotient.mk ((f.codRestrict (Work.Pi6.SRANGE.cycKer C (m + 1)) hmem) y) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change f y ∈ LinearMap.range ((C.d (m + 2) (m + 1)).hom) ↔ _
    rw [Work.Pi6.SRANGE.baseChange_d_eq_bcMap (R := R),
      extScal_range_d_eq_range_uctB R K m, hmap]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rwa [hfinj hxy] at hx
    · exact fun hy => ⟨y, hy, rfl⟩
  -- `Ψ` is surjective
  have hsurj : Function.Surjective Ψ := by
    intro w
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      (p := Work.Pi6.SRANGE.cycBnd C (m + 1)) w
    have hz : (z : ↥(C.X (m + 1))) ∈ LinearMap.range f := by
      rw [← hcyc]
      exact z.2
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, ?_⟩
    rw [hΨdef]
    show Submodule.Quotient.mk ((f.codRestrict _ hmem) y) = Submodule.Quotient.mk z
    exact congrArg Submodule.Quotient.mk (Subtype.ext hy)
  -- the quotient map onto `Z ⧸ B` and its kernel
  let qmap : ↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ ↥Z)) →ₗ[R]
      ↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ (↥Z ⧸ LinearMap.range ι))) :=
    Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom (Submodule.mkQ (LinearMap.range ι)))
  have hqsurj : Function.Surjective qmap :=
    Work.Pi6.SRANGE.bcMap_surjective _ (Submodule.mkQ_surjective _)
  have hkerQ : LinearMap.ker qmap
      = LinearMap.range (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom ι)) :=
    Work.Pi6.SRANGE.intR_map_ker_eq_range R (Submodule.mkQ (LinearMap.range ι))
      (Submodule.mkQ_surjective _) ι (Submodule.ker_mkQ _).symm
  -- the two steps of the quotient computation
  have hstepA : (↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ ↥Z)) ⧸
      LinearMap.range (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom ι)))
      ≃ₗ[R] Work.Pi6.SRANGE.homQuot R C (m + 1) :=
    (Submodule.quotEquivOfEq (LinearMap.range (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom ι)))
      (LinearMap.ker Ψ) hker.symm).trans (LinearMap.quotKerEquivOfSurjective Ψ hsurj)
  have hstepB : (↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ ↥Z)) ⧸
      LinearMap.range (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom ι)))
      ≃ₗ[R] ↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ (↥Z ⧸ LinearMap.range ι))) :=
    (Submodule.quotEquivOfEq (LinearMap.range (Work.Pi6.SRANGE.bcMap R (ModuleCat.ofHom ι)))
      (LinearMap.ker qmap) hkerQ.symm).trans (LinearMap.quotKerEquivOfSurjective qmap hqsurj)
  -- the homology of `K` itself
  obtain ⟨eK⟩ := Work.Cohomology.homology_iso_H K (m + 1)
  have hq : LinearMap.range ι = Work.Cohomology.uctH K (m + 1) := by
    rw [hιdef]
    exact Work.Pi6.EMM2.range_inclusion_eq_uctH K (m + 1)
  have hstepC : ↥(Work.Pi6.SRANGE.BC R (ModuleCat.of ℤ (↥Z ⧸ LinearMap.range ι)))
      ≃ₗ[R] ↥(F.obj (K.homology (m + 1))) :=
    Work.Pi6.SRANGE.isoToLinearEquiv (F.mapIso
      (LinearEquiv.toModuleIso (Submodule.quotEquivOfEq _ _ hq) ≪≫ eK.symm))
  exact ⟨LinearEquiv.toModuleIso
    (((Work.Pi6.SRANGE.homQuotEquiv C (m + 1)).symm.trans hstepA.symm).trans
      (hstepB.trans hstepC))⟩

end

end Work.Pi6.EMM2
