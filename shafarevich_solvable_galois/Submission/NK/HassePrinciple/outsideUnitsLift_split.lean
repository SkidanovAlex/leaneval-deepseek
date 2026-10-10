import Mathlib.Order.CompletePartialOrder
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.NK.HassePrinciple.supportedLift_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HassePrinciple

open NK.RepresentationTheory.GroupCohomology
open CategoryTheory Representation
open NK.GlobalCFT

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- The generic `ULift.module` instance competes with the module structure stored in a
representation; prefer the structure instances, as intended. -/
attribute [local instance 10000] Rep.hV1 Rep.hV2

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The orbit of a place outside `S` -/

-- extensionality of `Γ`-stable sets of places is `NK.HassePrinciple.GStableSet.ext`, proved in
-- `Submission.NK.HassePrinciple.supportedLift_split`

/-- **The orbit of a place `v ∉ S`**, as an element of the index set `orbitIndexOut S`. -/
noncomputable def orbitOfOut (S : GStableSet K L) (v : Place L) (hv : v ∉ S.carrier) :
    orbitIndexOut (K := K) (L := L) S :=
  ⟨orbitStable K L v, isOrbit_orbitStable v, by
    rw [Set.disjoint_left]
    intro w hw hwS
    obtain ⟨σ, rfl⟩ := mem_placeOrbit.mp hw
    exact hv (by have := S.smul_mem' σ⁻¹ hwS; rwa [inv_smul_smul] at this)⟩

theorem orbitOfOut_carrier (S : GStableSet K L) (v : Place L) (hv : v ∉ S.carrier) :
    (orbitOfOut S v hv).1.carrier = placeOrbit K L v := rfl

theorem mem_orbitOfOut (S : GStableSet K L) (v : Place L) (hv : v ∉ S.carrier) :
    v ∈ (orbitOfOut S v hv).1.carrier :=
  show v ∈ placeOrbit K L v from mem_placeOrbit.mpr ⟨1, one_smul _ _⟩

/-- The orbits of `σ • v` and of `v` coincide. -/
theorem placeOrbit_smul_eq (σ : L ≃ₐ[K] L) (v : Place L) :
    placeOrbit K L (σ • v) = placeOrbit K L v := by
  ext w
  rw [mem_placeOrbit, mem_placeOrbit]
  exact ⟨fun ⟨g, hg⟩ => ⟨g * σ, by rw [mul_smul, hg]⟩,
         fun ⟨g, hg⟩ => ⟨g * σ⁻¹, by rw [mul_smul, inv_smul_smul, hg]⟩⟩

/-- The index `orbitOfOut` only depends on the orbit of the place. -/
theorem orbitOfOut_eq_of_mem {S : GStableSet K L} {v w : Place L}
    (hv : v ∉ S.carrier) (hw : w ∉ S.carrier) (h : w ∈ placeOrbit K L v) :
    orbitOfOut S w hw = orbitOfOut S v hv := by
  apply Subtype.ext
  apply GStableSet.ext
  show placeOrbit K L w = placeOrbit K L v
  obtain ⟨σ, rfl⟩ := mem_placeOrbit.mp h
  exact placeOrbit_smul_eq σ v

/-! ## The assembly of the orbit components -/

/-- **The idèle underlying the section**: `x v = (y (orbit of v)) v` for `v ∉ S` and `x v = 1`
for `v ∈ S`.  Its components are all local units, so no finiteness hypothesis is needed. -/
noncomputable def outsideUnitsSectionIdele (S : GStableSet K L)
    (y : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier)) : Idele L := by
  classical
  refine ⟨fun v => if hv : v ∈ S.carrier then 1 else (y (orbitOfOut S v hv) : Idele L) v, ?_⟩
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset Set.finite_empty ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  exact hv (by
    by_cases h : v ∈ S.carrier
    · rw [dif_pos h]; exact Subgroup.one_mem _
    · rw [dif_neg h]; exact (mem_orbitUnitsSubgroup.mp (y (orbitOfOut S v h)).2).2 v)

theorem outsideUnitsSectionIdele_of_mem (S : GStableSet K L)
    (y : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier)) {v : Place L} (hv : v ∈ S.carrier) :
    outsideUnitsSectionIdele S y v = 1 := by
  classical
  rw [show outsideUnitsSectionIdele S y v =
      (if h : v ∈ S.carrier then 1 else (y (orbitOfOut S v h) : Idele L) v) from rfl, dif_pos hv]

theorem outsideUnitsSectionIdele_of_notMem (S : GStableSet K L)
    (y : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier)) {v : Place L} (hv : v ∉ S.carrier) :
    outsideUnitsSectionIdele S y v = (y (orbitOfOut S v hv) : Idele L) v := by
  classical
  rw [show outsideUnitsSectionIdele S y v =
      (if h : v ∈ S.carrier then 1 else (y (orbitOfOut S v h) : Idele L) v) from rfl, dif_neg hv]

theorem outsideUnitsSectionIdele_supported (S : GStableSet K L)
    (y : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier))
    (v : Place L) (hv : v ∉ S.compl.carrier) :
    outsideUnitsSectionIdele S y v = 1 := by
  have hv' : v ∈ S.carrier := by simpa using hv
  exact outsideUnitsSectionIdele_of_mem S y hv'

theorem outsideUnitsSectionIdele_mem_localUnits (S : GStableSet K L)
    (y : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier)) (v : Place L) :
    outsideUnitsSectionIdele S y v ∈ Place.localUnits L v := by
  by_cases h : v ∈ S.carrier
  · rw [outsideUnitsSectionIdele_of_mem S y h]
    exact Subgroup.one_mem _
  · rw [outsideUnitsSectionIdele_of_notMem S y h]
    exact (mem_orbitUnitsSubgroup.mp (y (orbitOfOut S v h)).2).2 v

/-- **The section `∏_{O ∩ S = ∅} U_O ⟶ U_S`** assembling the orbit components. -/
noncomputable def outsideUnitsSection (S : GStableSet K L) :
    (∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier)) →*
      ↥(orbitUnitsSubgroup (K := K) S.compl.carrier) where
  toFun y := ⟨outsideUnitsSectionIdele S y,
    mem_orbitUnitsSubgroup.mpr ⟨fun v hv => outsideUnitsSectionIdele_supported S y v hv,
      fun v => outsideUnitsSectionIdele_mem_localUnits S y v⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Idele.ext
    intro v
    by_cases h : v ∈ S.carrier
    · rw [outsideUnitsSectionIdele_of_mem S _ h]
      simp
    · rw [outsideUnitsSectionIdele_of_notMem S _ h]
      simp
  map_mul' y y' := by
    apply Subtype.ext
    apply Idele.ext
    intro v
    by_cases h : v ∈ S.carrier
    · rw [outsideUnitsSectionIdele_of_mem S _ h]
      simp only [Subgroup.coe_mul, Idele.mul_apply]
      rw [outsideUnitsSectionIdele_of_mem S y h, outsideUnitsSectionIdele_of_mem S y' h]
      simp
    · rw [outsideUnitsSectionIdele_of_notMem S _ h]
      simp only [Subgroup.coe_mul, Idele.mul_apply]
      rw [outsideUnitsSectionIdele_of_notMem S y h, outsideUnitsSectionIdele_of_notMem S y' h]
      simp [Pi.mul_apply]

theorem outsideUnitsSection_coe (S : GStableSet K L)
    (y : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier)) :
    ((outsideUnitsSection S y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)
      = outsideUnitsSectionIdele S y := rfl

theorem orbitUnitsSubgroup_coe_smul (O : GStableSet K L) (σ : L ≃ₐ[K] L)
    (x : ↥(orbitUnitsSubgroup (K := K) O.carrier)) :
    ((σ • x : ↥(orbitUnitsSubgroup (K := K) O.carrier)) : Idele L) = σ • (x : Idele L) := rfl

/-- **`Γ`-equivariance of the assembly.** -/
theorem outsideUnitsSection_smul (S : GStableSet K L) (σ : L ≃ₐ[K] L)
    (y : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ↥(orbitUnitsSubgroup (K := K) O.1.carrier)) :
    outsideUnitsSection S (fun O => σ • y O) = σ • outsideUnitsSection S y := by
  apply Subtype.ext
  apply Idele.ext
  intro v
  by_cases h : v ∈ S.carrier
  · rw [outsideUnitsSection_coe, outsideUnitsSectionIdele_of_mem S _ h]
    rw [orbitUnitsSubgroup_coe_smul, smul_apply_eq_actVal]
    rw [outsideUnitsSection_coe, outsideUnitsSectionIdele_of_mem S y (S.smul_mem' σ⁻¹ h)]
    rw [actVal_one, cast_one]
  · rw [outsideUnitsSection_coe, outsideUnitsSectionIdele_of_notMem S _ h]
    rw [orbitUnitsSubgroup_coe_smul, smul_apply_eq_actVal]
    rw [orbitUnitsSubgroup_coe_smul, smul_apply_eq_actVal]
    have h' : σ⁻¹ • v ∉ S.carrier := fun hv => h (by
      have := S.smul_mem' σ hv
      rwa [smul_inv_smul] at this)
    rw [outsideUnitsSection_coe, outsideUnitsSectionIdele_of_notMem S y h']
    have hO : orbitOfOut S (σ⁻¹ • v) h' = orbitOfOut S v h :=
      orbitOfOut_eq_of_mem h h' (mem_placeOrbit.mpr ⟨σ⁻¹, rfl⟩)
    rw [hO]

/-- **The retraction identity**: assembling the components of the projections of `z` recovers
`z`. -/
theorem outsideUnitsSection_projOrbitUnits (S : GStableSet K L)
    (z : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) :
    outsideUnitsSection S (fun O => projOrbitUnits K L S O.1 z) = z := by
  apply Subtype.ext
  apply Idele.ext
  intro v
  show outsideUnitsSectionIdele S (fun O => projOrbitUnits K L S O.1 z) v = (z : Idele L) v
  by_cases h : v ∈ S.carrier
  · rw [outsideUnitsSectionIdele_of_mem S _ h]
    exact ((mem_orbitUnitsSubgroup.mp z.2).1 v (by simpa using h)).symm
  · rw [outsideUnitsSectionIdele_of_notMem S _ h]
    show (restrictTo K L (orbitOfOut S v h).1.carrier (z : Idele L)) v = (z : Idele L) v
    rw [restrictTo_apply_of_mem K L _ (z : Idele L) (mem_orbitOfOut S v h)]

/-! ## The section as a morphism of representations -/

/-- The multiplicative component of an element of the representation `∏_O U_O`. -/
noncomputable def phi (S : GStableSet K L)
    (x : (piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).V) :
    (O : orbitIndexOut (K := K) (L := L) S) → ↥(orbitUnitsSubgroup (K := K) O.1.carrier) :=
  fun O => Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from x O)

theorem phi_add (S : GStableSet K L)
    (x y : (piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).V) :
    phi S (x + y) = phi S x * phi S y := by
  funext O
  exact toMul_add (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from x O)
    (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from y O)

theorem phi_zsmul (S : GStableSet K L) (z : ℤ)
    (x : (piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).V) :
    phi S (z • x) = (phi S x) ^ z := by
  funext O
  exact toMul_zsmul z (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from x O)

/-- The action of the pointwise product representation on `phi`. -/
theorem phi_ρ_apply (S : GStableSet K L) (σ : L ≃ₐ[K] L)
    (x : (piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).V)
    (O : orbitIndexOut (K := K) (L := L) S) :
    phi S ((piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).ρ σ x) O
      = σ • phi S x O := by
  show Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from
      ((piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).ρ σ x) O)
    = σ • Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from x O)
  have h1 : ((piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).ρ σ x) O
      = (orbitUnitsRep K L O.1).ρ σ (x O) :=
    piRep_ρ_apply (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1) σ x O
  have step1 : Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from
        ((piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).ρ σ x) O)
      = Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from
        (orbitUnitsRep K L O.1).ρ σ (x O)) :=
    congrArg (fun y : (orbitUnitsRep K L O.1).V =>
      Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from y)) h1
  have h2 := orbitUnitsRep_ρ_apply (K := K) (L := L) (O := O.1) σ (x O)
  have step2 : Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from
        (orbitUnitsRep K L O.1).ρ σ (x O))
      = σ • Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from x O) := by
    rw [h2]
    rfl
  exact step1.trans step2

theorem phi_ρ (S : GStableSet K L) (σ : L ≃ₐ[K] L)
    (x : (piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).V) :
    phi S ((piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1)).ρ σ x)
      = fun O => σ • phi S x O := by
  funext O
  exact phi_ρ_apply S σ x O

/-- **The section `∏_{O ∩ S = ∅} U_O ⟶ U_S` as a morphism of representations.** -/
noncomputable def outsideUnitsSectionHom (S : GStableSet K L) :
    piRep (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1) ⟶
      outsideUnitsRep K L S :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (outsideUnitsSection S (phi S x))
      map_add' := fun x y => by
        show Additive.ofMul (outsideUnitsSection S (phi S (x + y))) =
          Additive.ofMul (outsideUnitsSection S (phi S x)) +
            Additive.ofMul (outsideUnitsSection S (phi S y))
        rw [phi_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul (outsideUnitsSection S (phi S (z • x))) =
          z • Additive.ofMul (outsideUnitsSection S (phi S x))
        rw [phi_zsmul, map_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (outsideUnitsSection S
            (phi S ((piRep (fun O : orbitIndexOut (K := K) (L := L) S =>
              orbitUnitsRep K L O.1)).ρ σ x))) =
          (orbitUnitsRep K L S.compl).ρ σ (Additive.ofMul (outsideUnitsSection S (phi S x)))
        rw [orbitUnitsRep_ρ_apply, phi_ρ, outsideUnitsSection_smul]
        rfl }

/-- **The section is a left inverse of the lift.** -/
theorem outsideUnitsSectionHom_comp (S : GStableSet K L) :
    outsideUnitsLift K L S ≫ outsideUnitsSectionHom S = 𝟙 (outsideUnitsRep K L S) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show Additive.ofMul (outsideUnitsSection S (phi S ((outsideUnitsLift K L S).hom x))) = x
  have hfun : phi S ((outsideUnitsLift K L S).hom x)
      = fun O : orbitIndexOut (K := K) (L := L) S => projOrbitUnits K L S O.1 (Additive.toMul x) := by
    funext O
    show Additive.toMul (show Additive ↥(orbitUnitsSubgroup (K := K) O.1.carrier) from
        ((outsideUnitsLift K L S).hom x) O)
      = projOrbitUnits K L S O.1 (Additive.toMul x)
    rw [show ((outsideUnitsLift K L S).hom x) O = (projOrbitUnitsHom K L S O.1).hom x from rfl]
    rw [show (projOrbitUnitsHom K L S O.1).hom x
        = (repHomOfMonoidHom (projOrbitUnits K L S O.1)
            (projOrbitUnits_smul K L S O.1)).hom x from rfl]
    rw [repHomOfMonoidHom_apply]
    rfl
  rw [hfun, outsideUnitsSection_projOrbitUnits]
  rfl

end

/-- **The orbit decomposition of `∏_{v ∉ S} 𝒪_vˣ` splits.**

Let `Γ = Gal(L/K)` and let `S` be a `Γ`-stable set of places.  Write
`U_S = ∏_{v ∉ S} 𝒪_vˣ` for the idèles supported outside `S` all of whose components are local
units (realised as `NK.HassePrinciple.outsideUnitsRep K L S`, whose underlying group is
`NK.HassePrinciple.orbitUnitsSubgroup S.compl.carrier`), and for an orbit `O` disjoint from `S`
write `U_O = ∏_{v ∈ O} 𝒪_vˣ` (`orbitUnitsRep K L O`).

`NK.HassePrinciple.outsideUnitsLift K L S : U_S ⟶ ∏ᶜ_O U_O` is the `Γ`-map whose `O`-component
is the projection `U_S ⟶ U_O` (`NK.HassePrinciple.projOrbitUnitsHom K L S O`).  The claim is
that it is a split monomorphism.

Suggested construction of `s`: given `y : ∀ O, U_O`, assemble the idèle `x` with
`x v := (y (orbit of v)) v` for `v ∉ S` and `x v := 1` for `v ∈ S`.  All the components of `x`
are local units, so `x` is an idèle with **no** restriction on the set of exceptional places; in
particular no finiteness hypothesis on `S` is needed, and the assembly is well defined.  The
retraction identity is componentwise (using the `Γ`-stability of `S` to see that the orbit of a
place outside `S` is disjoint from `S`). -/
theorem outsideUnitsLift_split {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : NK.HassePrinciple.GStableSet K L) :
    ∃ s : NK.RepresentationTheory.GroupCohomology.piRep
              (fun O : NK.HassePrinciple.orbitIndexOut (K := K) (L := L) S =>
                NK.HassePrinciple.orbitUnitsRep K L O.1) ⟶
            NK.HassePrinciple.outsideUnitsRep K L S,
      CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.outsideUnitsLift K L S) s =
        CategoryTheory.CategoryStruct.id (NK.HassePrinciple.outsideUnitsRep K L S) := by
  exact ⟨outsideUnitsSectionHom S, outsideUnitsSectionHom_comp S⟩

end NK.HassePrinciple
