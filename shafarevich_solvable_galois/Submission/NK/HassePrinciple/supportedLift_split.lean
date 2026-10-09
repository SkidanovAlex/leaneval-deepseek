import Mathlib
import Submission.NK.HassePrinciple.IdeleLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HassePrinciple

open NK.RepresentationTheory.GroupCohomology
open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The orbit of a place as an index of the orbit decomposition -/

/-- Two `Gal(L/K)`-stable sets of places with the same carrier are equal. -/
theorem GStableSet.ext {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {S T : GStableSet K L} (h : S.carrier = T.carrier) : S = T := by
  cases S with
  | mk c p => cases T with
  | mk c' p' =>
    simp only at h
    subst h
    exact congrArg (fun q => (⟨c, q⟩ : GStableSet K L)) (Subsingleton.elim p p')

/-- The `Gal(L/K)`-orbit of a place does not change under translation of the place. -/
theorem placeOrbit_smul (σ : L ≃ₐ[K] L) (v : Place L) :
    placeOrbit K L (σ • v) = placeOrbit K L v := by
  ext w
  simp only [mem_placeOrbit]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g * σ, by rw [mul_smul, hg]⟩
  · rintro ⟨g, hg⟩
    exact ⟨g * σ⁻¹, by rw [mul_smul, inv_smul_smul, hg]⟩

theorem orbitStable_smul (σ : L ≃ₐ[K] L) (v : Place L) :
    orbitStable K L (σ • v) = orbitStable K L v :=
  GStableSet.ext (placeOrbit_smul σ v)

/-- **The orbit of `v` as an element of the index set of the orbit decomposition of `S`**, for a
place `v` of the stable set `S`. -/
def orbitIndexOf (S : GStableSet K L) (v : Place L) (hv : v ∈ S.carrier) :
    orbitIndexIn (K := K) (L := L) S :=
  ⟨orbitStable K L v, fun w hw => by
      obtain ⟨σ, hσ⟩ := mem_placeOrbit.mp hw
      rw [← hσ]
      exact S.smul_mem' σ hv,
    ⟨v, rfl⟩⟩

/-- The index of a place of `S` only depends on the orbit of the place. -/
theorem orbitIndexOf_smul (S : GStableSet K L) (v : Place L) (hv : v ∈ S.carrier)
    (τ : L ≃ₐ[K] L) (hv' : τ • v ∈ S.carrier) :
    orbitIndexOf S (τ • v) hv' = orbitIndexOf S v hv := by
  apply Subtype.ext
  exact GStableSet.ext (placeOrbit_smul τ v)

/-! ## Gluing a family of orbit-supported idèles -/

/-- The component at `v` of the gluing of a family of idèles supported on the orbits contained
in `S`: the component at `v` of the member of the family indexed by the orbit of `v`. -/
noncomputable def glueVal (S : GStableSet K L)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    (v : Place L) : (Place.localField L v)ˣ := by
  classical
  exact if hv : v ∈ S.carrier then
    ((y (orbitIndexOf S v hv) : ↥(supportedSubgroup (orbitIndexOf S v hv).1.carrier)) :
      Idele L) v
  else 1

theorem glueVal_of_mem (S : GStableSet K L)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    {v : Place L} (hv : v ∈ S.carrier) :
    glueVal S y v = ((y (orbitIndexOf S v hv) :
      ↥(supportedSubgroup (orbitIndexOf S v hv).1.carrier)) : Idele L) v := by
  classical
  rw [glueVal]
  exact dif_pos hv

theorem glueVal_of_notMem (S : GStableSet K L)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    {v : Place L} (hv : v ∉ S.carrier) : glueVal S y v = 1 := by
  classical
  rw [glueVal]
  exact dif_neg hv

/-- **The gluing of a family of idèles supported on the orbits inside `S`**: the idèle whose
component at `v` is the component at `v` of the member of the family indexed by the orbit of
`v`, and which is `1` outside `S`.  It is an idèle because its components are non-units only on
the finite set `S`. -/
noncomputable def glue (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier)) :
    Idele L :=
  ⟨fun v => glueVal S y v, by
    rw [Filter.eventually_cofinite]
    exact hS.subset (fun v hv => by
      by_contra h
      exact hv (by
        show glueVal S y v ∈ Place.localUnits L v
        rw [glueVal_of_notMem S y h]
        exact Subgroup.one_mem _))⟩

theorem glue_apply (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    (v : Place L) : glue S hS y v = glueVal S y v := rfl

/-- The gluing of a family of idèles supported on the orbits inside `S`, as an element of
`∏_{v ∈ S} L_vˣ`. -/
noncomputable def glueSub (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier)) :
    ↥(supportedSubgroup S.carrier) :=
  ⟨glue S hS y, fun _ hv => glueVal_of_notMem S y hv⟩

@[simp] theorem glueSub_apply (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    (v : Place L) : ((glueSub S hS y : ↥(supportedSubgroup S.carrier)) : Idele L) v =
      glueVal S y v := rfl

theorem glueSub_apply_of_mem (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    {v : Place L} (hv : v ∈ S.carrier) :
    ((glueSub S hS y : Idele L)) v = ((y (orbitIndexOf S v hv) : Idele L)) v :=
  glueVal_of_mem S y hv

theorem glueSub_apply_of_notMem (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    {v : Place L} (hv : v ∉ S.carrier) :
    ((glueSub S hS y : Idele L)) v = 1 :=
  glueVal_of_notMem S y hv

/-! ## The gluing is multiplicative, additive and equivariant -/

theorem glueSub_mul_apply (S : GStableSet K L) (hS : S.carrier.Finite)
    (y z : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier)) :
    glueSub S hS (fun O => y O * z O) = glueSub S hS y * glueSub S hS z := by
  apply Subtype.ext
  apply Idele.ext
  intro v
  by_cases hv : v ∈ S.carrier
  · rw [glueSub_apply_of_mem S hS (fun O => y O * z O) hv]
    show ((y (orbitIndexOf S v hv) : Idele L)) v * ((z (orbitIndexOf S v hv) : Idele L)) v
      = ((glueSub S hS y : Idele L)) v * ((glueSub S hS z : Idele L)) v
    rw [glueSub_apply_of_mem S hS y hv, glueSub_apply_of_mem S hS z hv]
  · rw [glueSub_apply_of_notMem S hS (fun O => y O * z O) hv]
    show (1 : (Place.localField L v)ˣ)
      = ((glueSub S hS y : Idele L)) v * ((glueSub S hS z : Idele L)) v
    rw [glueSub_apply_of_notMem S hS y hv, glueSub_apply_of_notMem S hS z hv, mul_one]

theorem glueSub_zpow_apply (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    (n : ℤ) :
    glueSub S hS (fun O => y O ^ n) = glueSub S hS y ^ n := by
  apply Subtype.ext
  apply Idele.ext
  intro v
  by_cases hv : v ∈ S.carrier
  · rw [glueSub_apply_of_mem S hS (fun O => y O ^ n) hv]
    show (((y (orbitIndexOf S v hv) : Idele L)) v) ^ n
      = (((glueSub S hS y : Idele L)) v) ^ n
    rw [glueSub_apply_of_mem S hS y hv]
  · rw [glueSub_apply_of_notMem S hS (fun O => y O ^ n) hv]
    show (1 : (Place.localField L v)ˣ) = (((glueSub S hS y : Idele L)) v) ^ n
    rw [glueSub_apply_of_notMem S hS y hv, one_zpow]

/-- **The gluing is `Gal(L/K)`-equivariant.** -/
theorem glueSub_smul (S : GStableSet K L) (hS : S.carrier.Finite) (σ : L ≃ₐ[K] L)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier)) :
    glueSub S hS (fun O => σ • y O) = σ • glueSub S hS y := by
  apply Subtype.ext
  apply Idele.ext
  intro v
  by_cases hv : v ∈ S.carrier
  · have hσv : σ⁻¹ • v ∈ S.carrier := S.smul_mem' σ⁻¹ hv
    rw [glueSub_apply_of_mem S hS (fun O => σ • y O) hv]
    show (σ • ((y (orbitIndexOf S v hv) : Idele L))) v
      = (σ • ((glueSub S hS y : Idele L))) v
    rw [smul_apply_eq_actVal, smul_apply_eq_actVal]
    congr 1
    rw [glueSub_apply_of_mem S hS y hσv, orbitIndexOf_smul S v hv σ⁻¹ hσv]
  · have hσv : σ⁻¹ • v ∉ S.carrier := fun h => hv (by
      have h' := S.smul_mem' σ h
      rwa [smul_inv_smul] at h')
    rw [glueSub_apply_of_notMem S hS (fun O => σ • y O) hv]
    show (1 : (Place.localField L v)ˣ) = (σ • ((glueSub S hS y : Idele L))) v
    rw [smul_apply_eq_actVal, glueSub_apply_of_notMem S hS y hσv, actVal_one, cast_one]

/-! ## The gluing inverts the projection onto the orbit components -/

/-- **The gluing of the projections of an idèle supported on `S` is the idèle itself.** -/
theorem glueSub_projSupported (S : GStableSet K L) (hS : S.carrier.Finite)
    (x : ↥(supportedSubgroup S.carrier)) :
    glueSub S hS (fun O : orbitIndexIn (K := K) (L := L) S =>
      projSupported K L S O.1 x) = x := by
  apply Subtype.ext
  apply Idele.ext
  intro v
  by_cases hv : v ∈ S.carrier
  · rw [glueSub_apply_of_mem S hS (fun O => projSupported K L S O.1 x) hv]
    show (restrictTo K L (placeOrbit K L v) (x : Idele L)) v = (x : Idele L) v
    rw [restrictTo_apply_of_mem K L (placeOrbit K L v) (x : Idele L) (MulAction.mem_orbit_self v)]
  · rw [glueSub_apply_of_notMem S hS (fun O => projSupported K L S O.1 x) hv]
    exact (mem_supportedSubgroup.mp x.2 v hv).symm

/-! ## The underlying idèle families of the product representation -/

/-- The underlying subgroup element of an element of the representation `A_O`. -/
noncomputable def toSubO (S : GStableSet K L) (O : orbitIndexIn (K := K) (L := L) S)
    (x : (supportedRep K L O.1).V) : ↥(supportedSubgroup O.1.carrier) := Additive.toMul x

/-- The underlying idèle of an element of the representation `A_S`. -/
noncomputable def toSub (S : GStableSet K L) (x : (supportedRep K L S).V) :
    ↥(supportedSubgroup S.carrier) := Additive.toMul x

/-- The idèle family underlying an element of the product representation `∏_{O ⊆ S} A_O`. -/
noncomputable def famOfPi (S : GStableSet K L)
    (x : (NK.RepresentationTheory.GroupCohomology.piRep
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).V) :
    ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier) :=
  fun O => Additive.toMul (x O)

/-- The inverse construction to `famOfPi`. -/
noncomputable def piOfFam (S : GStableSet K L)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier)) :
    (NK.RepresentationTheory.GroupCohomology.piRep
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).V :=
  fun O => Additive.ofMul (y O)

theorem famOfPi_piOfFam (S : GStableSet K L)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier)) :
    famOfPi S (piOfFam S y) = y := rfl

theorem piOfFam_famOfPi (S : GStableSet K L)
    (x : (NK.RepresentationTheory.GroupCohomology.piRep
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).V) :
    piOfFam S (famOfPi S x) = x := rfl

/-- The map `famOfPi` carries addition to multiplication. -/
theorem famOfPi_add (S : GStableSet K L)
    (x y : (NK.RepresentationTheory.GroupCohomology.piRep
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).V) :
    famOfPi S (x + y) = famOfPi S x * famOfPi S y := by
  funext O
  rfl

/-- The map `famOfPi` carries integer multiples to powers. -/
theorem famOfPi_zsmul (S : GStableSet K L)
    (x : (NK.RepresentationTheory.GroupCohomology.piRep
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).V) (z : ℤ) :
    famOfPi S (z • x) = (famOfPi S x) ^ z := by
  funext O
  rfl

/-- The map `famOfPi` is `Gal(L/K)`-equivariant. -/
theorem famOfPi_smul (S : GStableSet K L) (σ : L ≃ₐ[K] L)
    (x : (NK.RepresentationTheory.GroupCohomology.piRep
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).V) :
    famOfPi S ((NK.RepresentationTheory.GroupCohomology.piRep
        (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).ρ σ x)
      = fun O => σ • famOfPi S x O := by
  funext O
  change toSubO S O (((NK.RepresentationTheory.GroupCohomology.piRep
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1)).ρ σ x) O)
    = σ • toSubO S O (x O)
  rw [NK.RepresentationTheory.GroupCohomology.piRep_ρ_apply,
    NK.HassePrinciple.supportedRep_ρ_apply]
  rfl

/-- The value of the projection `projSupportedHom` on an element. -/
theorem projSupportedHom_apply (S O : GStableSet K L) (x : (supportedRep K L S).V) :
    (projSupportedHom K L S O).hom x
      = Additive.ofMul (projSupported K L S O (Additive.toMul x)) := rfl

/-- The component of the lift `supportedLift` at an orbit. -/
theorem supportedLift_hom_apply (S : GStableSet K L) (x : (supportedRep K L S).V)
    (O : orbitIndexIn (K := K) (L := L) S) :
    (supportedLift K L S).hom x O = (projSupportedHom K L S O.1).hom x := rfl

/-- The idèle family underlying the image of `x` under `supportedLift`: the projections of `x` to
the orbits contained in `S`. -/
theorem famOfPi_supportedLift (S : GStableSet K L) (x : (supportedRep K L S).V) :
    famOfPi S ((supportedLift K L S).hom x)
      = fun O : orbitIndexIn (K := K) (L := L) S =>
          projSupported K L S O.1 (toSub S x) := by
  funext O
  change toSubO S O ((supportedLift K L S).hom x O) = projSupported K L S O.1 (toSub S x)
  rw [supportedLift_hom_apply, projSupportedHom_apply]
  rfl

/-! ## Multiplicativity and powers in the algebraic form -/

theorem glueSub_mul (S : GStableSet K L) (hS : S.carrier.Finite)
    (y z : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier)) :
    glueSub S hS (y * z) = glueSub S hS y * glueSub S hS z :=
  glueSub_mul_apply S hS y z

theorem glueSub_zpow (S : GStableSet K L) (hS : S.carrier.Finite)
    (y : ∀ O : orbitIndexIn (K := K) (L := L) S, ↥(supportedSubgroup O.1.carrier))
    (n : ℤ) :
    glueSub S hS (y ^ n) = glueSub S hS y ^ n :=
  glueSub_zpow_apply S hS y n

end

/-- **The orbit decomposition of `∏_{v ∈ S} L_vˣ` splits.**

Let `Γ = Gal(L/K)` and let `S` be a finite `Γ`-stable set of places.  Write
`A_S = ∏_{v ∈ S} L_vˣ` for the idèles supported on `S` (realised as
`NK.HassePrinciple.supportedRep K L S`, whose underlying group is
`NK.HassePrinciple.supportedSubgroup S.carrier`), and for an orbit `O ⊆ S` write
`A_O = ∏_{v ∈ O} L_vˣ` (`supportedRep K L O`).

`NK.HassePrinciple.supportedLift K L S : A_S ⟶ ∏ᶜ_O A_O` is the `Γ`-map whose `O`-component is
the projection `A_S ⟶ A_O` (`NK.HassePrinciple.projSupportedHom K L S O`).  The claim is that
this map is a split monomorphism: it has a left inverse `s` (a `Γ`-map with `s ∘ lift = id`).

Suggested construction of `s`: given `y : ∀ O, A_O`, assemble the idèle `x` with
`x v := (y (orbit of v)) v` for `v ∈ S` and `x v := 1` for `v ∉ S`.  Then `x` lies in `A_S`:
its components are non-units only in `S`, which is finite (`hS`), and the fact that each `y O` is an
idèle gives the finiteness of the set of exceptional places.  The retraction identity is then
componentwise, using that `S` is `Γ`-stable (so that `orbit of v ⊆ S` for `v ∈ S`), and the
`Γ`-equivariance of `s` follows from the corresponding property of the projections. -/
theorem supportedLift_split {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : NK.HassePrinciple.GStableSet K L)
    (hS : S.carrier.Finite) :
    ∃ s : NK.RepresentationTheory.GroupCohomology.piRep
              (fun O : NK.HassePrinciple.orbitIndexIn (K := K) (L := L) S =>
                NK.HassePrinciple.supportedRep K L O.1) ⟶
            NK.HassePrinciple.supportedRep K L S,
      CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.supportedLift K L S) s =
        CategoryTheory.CategoryStruct.id (NK.HassePrinciple.supportedRep K L S) := by
  classical
  refine ⟨Rep.ofHom ?_, ?_⟩
  · refine
      { toFun := fun x => Additive.ofMul (glueSub S hS (famOfPi S x))
        map_add' := ?_
        map_smul' := ?_
        isIntertwining' := ?_ }
    · intro x y
      show Additive.ofMul (glueSub S hS (famOfPi S (x + y))) =
        Additive.ofMul (glueSub S hS (famOfPi S x)) +
          Additive.ofMul (glueSub S hS (famOfPi S y))
      rw [famOfPi_add, glueSub_mul, ofMul_mul]
    · intro n x
      obtain ⟨z⟩ := n
      show Additive.ofMul (glueSub S hS (famOfPi S (z • x))) =
        z • Additive.ofMul (glueSub S hS (famOfPi S x))
      rw [famOfPi_zsmul, glueSub_zpow, ofMul_zpow]
    · intro σ
      apply LinearMap.ext
      intro x
      show Additive.ofMul (glueSub S hS (famOfPi S
            ((NK.RepresentationTheory.GroupCohomology.piRep
              (fun O : NK.HassePrinciple.orbitIndexIn (K := K) (L := L) S =>
                NK.HassePrinciple.supportedRep K L O.1)).ρ σ x)))
          = (NK.HassePrinciple.supportedRep K L S).ρ σ
              (Additive.ofMul (glueSub S hS (famOfPi S x)))
      rw [show (NK.HassePrinciple.supportedRep K L S).ρ σ
            (Additive.ofMul (glueSub S hS (famOfPi S x)))
          = Additive.ofMul (σ • Additive.toMul
              (Additive.ofMul (glueSub S hS (famOfPi S x)))) from
        NK.HassePrinciple.supportedRep_ρ_apply (O := S) (g := σ)
          (x := Additive.ofMul (glueSub S hS (famOfPi S x)))]
      rw [show Additive.toMul (Additive.ofMul (glueSub S hS (famOfPi S x)))
          = glueSub S hS (famOfPi S x) from rfl]
      rw [famOfPi_smul, glueSub_smul]
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show Additive.ofMul (glueSub S hS (famOfPi S
        ((NK.HassePrinciple.supportedLift K L S).hom x))) = x
    rw [famOfPi_supportedLift]
    rw [glueSub_projSupported S hS (toSub S x)]
    rfl

end NK.HassePrinciple
