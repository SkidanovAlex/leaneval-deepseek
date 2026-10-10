import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.injective_h2_units_of_subsingleton_h1_classGroupRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation
open scoped NumberField
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NK.HassePrinciple

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The action of the decomposition group on the local units -/

/-- **The local action of an element of the decomposition group of `w` on the local units
`L_wˣ`**: transport of units along the local automorphism `localAutHom w σ`. -/
noncomputable def localUnitsEquiv (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    (Place.localField L w)ˣ ≃* (Place.localField L w)ˣ :=
  Units.mapEquiv (localAutHom (K := K) w σ).toMulEquiv

@[simp]
theorem coe_localUnitsEquiv (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (u : (Place.localField L w)ˣ) :
    ((localUnitsEquiv (K := K) w σ u : (Place.localField L w)ˣ) : Place.localField L w)
      = localAutHom (K := K) w σ (u : Place.localField L w) :=
  Units.coe_mapEquiv _ _

theorem localUnitsEquiv_one (w : Place L) :
    localUnitsEquiv (K := K) w 1 = 1 := by
  ext u
  rw [coe_localUnitsEquiv]
  show (localAutHom (K := K) w 1) (u : Place.localField L w) = (u : Place.localField L w)
  rw [map_one]
  rfl

theorem localUnitsEquiv_mul (w : Place L) (σ τ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    localUnitsEquiv (K := K) w (σ * τ) =
      localUnitsEquiv (K := K) w σ * localUnitsEquiv (K := K) w τ := by
  ext u
  rw [coe_localUnitsEquiv]
  show (localAutHom (K := K) w (σ * τ)) (u : Place.localField L w) =
    (localAutHom (K := K) w σ) ((localAutHom (K := K) w τ) (u : Place.localField L w))
  rw [map_mul]
  rfl

/-- **The action of the decomposition group `Γ_w` on the local units `L_wˣ`.** -/
noncomputable instance instMulDistribMulActionLocalUnits (w : Place L) :
    MulDistribMulAction (MulAction.stabilizer (L ≃ₐ[K] L) w) ((Place.localField L w)ˣ) where
  smul σ u := localUnitsEquiv (K := K) w σ u
  one_smul u := by
    change localUnitsEquiv (K := K) w 1 u = u
    rw [localUnitsEquiv_one]
    rfl
  mul_smul σ τ u := by
    change localUnitsEquiv (K := K) w (σ * τ) u =
      localUnitsEquiv (K := K) w σ (localUnitsEquiv (K := K) w τ u)
    rw [localUnitsEquiv_mul]
    rfl
  smul_mul σ u v := by
    change localUnitsEquiv (K := K) w σ (u * v) =
      localUnitsEquiv (K := K) w σ u * localUnitsEquiv (K := K) w σ v
    rw [map_mul]
  smul_one σ := by
    change localUnitsEquiv (K := K) w σ 1 = 1
    rw [map_one]

/-- **The local units `L_wˣ` as a `CoeffInt`-linear representation of the decomposition group
`Γ_w = MulAction.stabilizer (L ≃ₐ[K] L) w`.** -/
noncomputable def localUnitsRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    Rep CoeffInt (MulAction.stabilizer (L ≃ₐ[K] L) w) :=
  Rep.ofDistribMulAction CoeffInt _ (Additive ((Place.localField L w)ˣ))

/-! ## The coefficient map `Lˣ → L_wˣ` -/

/-- The embedding of the global units of `L` into the local units at `w`, as a monoid
homomorphism. -/
noncomputable def unitsToLocalUnitsHom (w : Place L) :
    Lˣ →* (Place.localField L w)ˣ :=
  Units.map ((algebraMap L (Place.localField L w)).toMonoidHom)

/-- **The embedding `Lˣ ↪ L_wˣ`, as a morphism of `Γ_w`-representations.**  The equivariance is
`NK.HassePrinciple.localAut_algebraMap`. -/
noncomputable def unitsToLocalUnits (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (unitsRep K L) ⟶
      localUnitsRep K L w :=
  Rep.ofHom
    { toFun := ⇑(unitsToLocalUnitsHom w).toAdditive
      map_add' := fun x y => map_add (unitsToLocalUnitsHom w).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul (unitsToLocalUnitsHom w).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (unitsToLocalUnitsHom w
            (Units.map σ.1.toMonoidHom (Additive.toMul x)))
          = Additive.ofMul (localUnitsEquiv (K := K) w σ
              (unitsToLocalUnitsHom w (Additive.toMul x)))
        congr 1
        apply Units.ext
        simp only [unitsToLocalUnitsHom, localUnitsEquiv, Units.coe_map]
        exact (localAut_algebraMap (K := K) w σ ((Additive.toMul x : Lˣ) : L)).symm }

/-- Computation rule for `unitsToLocalUnits`. -/
theorem unitsToLocalUnits_apply (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) (u : Lˣ) :
    (unitsToLocalUnits K L w).hom (Additive.ofMul u) =
      Additive.ofMul (unitsToLocalUnitsHom w u) := rfl

/-! ## The localisation of `H²(Γ, Lˣ)` -/

/-- **The localisation of `H²(Γ, Lˣ)` at the place `w`**: restrict along `Γ_w ≤ Γ` and then apply
the coefficient map `Lˣ → L_wˣ`.  This is the `w`-component of the relative Hasse–Brauer–Noether
localisation `H²(Γ, Lˣ) → ∏_w H²(Γ_w, L_wˣ)`. -/
noncomputable def locUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    groupCohomology (unitsRep K L) 2 ⟶ groupCohomology (localUnitsRep K L w) 2 :=
  (groupCohomology.resNatTrans CoeffInt
    (G := MulAction.stabilizer (L ≃ₐ[K] L) w) (H := L ≃ₐ[K] L)
    (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype 2).app (unitsRep K L) ≫
  groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
    (unitsToLocalUnits K L w) 2

/-- **Local triviality of a class of `H²(Γ, Lˣ)`** (coarse form): the class has vanishing
localisation at every place of `L`. -/
def locUnitsTrivial (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (a : groupCohomology (unitsRep K L) 2) : Prop :=
  ∀ w : Place L, (locUnits K L w).hom a = 0

/-- **The relative Hasse–Brauer–Noether theorem** (Milne, *CFT*, VII.7.1): a class of
`H²(Gal(L/K), Lˣ) = Br(L/K)` whose localisation at every place of `L` vanishes is zero.

This is the form of the Hasse principle that the classical theory derives from the Hasse norm
theorem.  The local groups `Γ_w = Gal(L/K)_w` here are the *decomposition* groups of the extension
`L/K`, which contain the local Galois groups `Gal(L_w/K_v)`; consequently the vanishing hypothesis
is *stronger* than the classical one, which is exactly the direction the chapter needs (see
README §12.2). -/
def HBNUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Prop :=
  ∀ a : groupCohomology (unitsRep K L) 2, locUnitsTrivial K L a → a = 0

/-! ## The same layer for the idèles -/

/-- The `w`-component of an idèle, as a monoid homomorphism. -/
noncomputable def ideleComponentHom (w : Place L) : Idele L →* (Place.localField L w)ˣ where
  toFun y := y w
  map_one' := rfl
  map_mul' x y := Idele.mul_apply x y w

/-- **The `w`-component of an idèle, as a morphism of `Γ_w`-representations**: the idèle group
`𝕀_L` restricted to the decomposition group of `w` maps to the local units `L_wˣ` by evaluation at
`w`.  (This is the inverse of the identification of Shapiro's lemma
`𝕀_L ≅ ⊕_w Coind_{Γ_w}^Γ L_wˣ`.) -/
noncomputable def ideleToLocalUnits (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (ideleRep K L) ⟶
      localUnitsRep K L w :=
  Rep.ofHom
    { toFun := ⇑(ideleComponentHom w).toAdditive
      map_add' := fun x y => map_add (ideleComponentHom w).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul (ideleComponentHom w).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (ideleComponentHom w (σ.1 • (Additive.toMul x : Idele L)))
          = Additive.ofMul (localUnitsEquiv (K := K) w σ
              (ideleComponentHom w (Additive.toMul x)))
        congr 1
        exact smul_apply_stabilizer w σ (Additive.toMul x) }

/-- **The localisation of `H²(Γ, 𝕀_L)` at the place `w`**. -/
noncomputable def ideleLoc (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    groupCohomology (ideleRep K L) 2 ⟶ groupCohomology (localUnitsRep K L w) 2 :=
  (groupCohomology.resNatTrans CoeffInt
    (G := MulAction.stabilizer (L ≃ₐ[K] L) w) (H := L ≃ₐ[K] L)
    (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype 2).app (ideleRep K L) ≫
  groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
    (ideleToLocalUnits K L w) 2

/-- **The localisation theorem for the idèles** (Shapiro's lemma for the idèles): a class of
`H²(Gal(L/K), 𝕀_L)` whose localisation at every place of `L` vanishes is zero.

Since `𝕀_L` is a direct sum of the induced modules `Ind_{Γ_w}^Γ L_wˣ` (over the `Γ`-orbits of the
places of `L`, with the `Γ_w`-action `localUnitsEquiv`), this is Shapiro's lemma
`H^n(Γ, Coind_{Γ_w}^Γ L_wˣ) ≅ H^n(Γ_w, L_wˣ)` together with the orbit decomposition of the places.
See README §8.4 item 2 and §12.5. -/
def HBNIdele (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Prop :=
  ∀ a : groupCohomology (ideleRep K L) 2,
    (∀ w : Place L, (ideleLoc K L w).hom a = 0) → a = 0

/-- **The map on `H²` induced by the principal idèles `Lˣ ↪ 𝕀_L`.** -/
noncomputable def unitsToIdeleH2 (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    groupCohomology (unitsRep K L) 2 ⟶ groupCohomology (ideleRep K L) 2 :=
  groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (ideleIncl K L) 2

/-- **The compatibility of the localisation of the units with the localisation of the idèles**
along the principal idèles `Lˣ ↪ 𝕀_L`: for every place `w` and every class `a` of `H²(Γ, Lˣ)`,
the `w`-component of the relative Hasse–Brauer–Noether localisation of `a` equals the `w`-component
of the idèle localisation of the image of `a`. -/
def LocUnitsCompatible (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  ∀ (w : Place L) (a : groupCohomology (unitsRep K L) 2),
    (locUnits K L w).hom a = (ideleLoc K L w).hom ((unitsToIdeleH2 K L).hom a)

end NK.HassePrinciple
