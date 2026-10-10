import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.NK.HassePrinciple.LocalUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The local units as a `Γ_w`-representation

The first layer of the proof of `hbnIdele`: the subgroup `𝒪_wˣ ⊆ L_wˣ` of local units is stable
under the decomposition group `Γ_w = MulAction.stabilizer (L ≃ₐ[K] L) w`, hence is a
`CoeffInt`-linear representation of `Γ_w`.
-/

/-- Transport of membership in the local units along an equality of places. -/
theorem mem_localUnits_of_eq' {a b : Place L} (h : a = b) (x : (Place.localField L a)ˣ) :
    x ∈ Place.localUnits L a ↔ (h ▸ x) ∈ Place.localUnits L b := by cases h; rfl

/-- The transport of units along an equality of places agrees with `Units.map` of
`RingEquiv.cast`. -/
theorem units_map_cast {a b : Place L} (h : a = b) (y : (Place.localField L a)ˣ) :
    Units.map (RingEquiv.cast (R := fun v : Place L => Place.localField L v) h).toMonoidHom y
      = (h ▸ y) := by cases h; rfl

/-- **The local units are stable under the decomposition group**: `localUnitsEquiv w σ` maps
`𝒪_wˣ` onto itself. -/
theorem localUnitsEquiv_mem (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (u : (Place.localField L w)ˣ) :
    localUnitsEquiv (K := K) w σ u ∈ Place.localUnits L w ↔ u ∈ Place.localUnits L w := by
  have hσ : σ.1 • w = w := MulAction.mem_stabilizer_iff.mp σ.2
  have h1 : u ∈ Place.localUnits L w ↔
      (Units.map (Place.localRingEquiv σ.1 w).toMonoidHom u) ∈ Place.localUnits L (σ.1 • w) :=
    Place.localRingEquiv_mem_localUnits σ.1 w u
  have key : localUnitsEquiv (K := K) w σ u
      = Units.map (RingEquiv.cast (R := fun v : Place L => Place.localField L v) hσ).toMonoidHom
          (Units.map (Place.localRingEquiv σ.1 w).toMonoidHom u) := by
    ext
    rw [coe_localUnitsEquiv]
    simp only [localAutHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map]
    rw [localAut_apply, show (MulAction.mem_stabilizer_iff.mp σ.2) = hσ from Subsingleton.elim _ _]
    rfl
  rw [key, units_map_cast hσ]
  exact (mem_localUnits_of_eq' hσ _).symm.trans h1.symm

/-- **The action of `Γ_w` on the local units**, as a `MulDistribMulAction` on the subgroup
`𝒪_wˣ ⊆ L_wˣ`. -/
noncomputable instance instMulDistribMulActionLocalUnitsSub (w : Place L) :
    MulDistribMulAction (MulAction.stabilizer (L ≃ₐ[K] L) w) ↥(Place.localUnits L w) where
  smul σ u := ⟨localUnitsEquiv (K := K) w σ u.1, (localUnitsEquiv_mem (K := K) w σ u.1).mpr u.2⟩
  one_smul u := by
    apply Subtype.ext
    show localUnitsEquiv (K := K) w 1 u.1 = u.1
    rw [localUnitsEquiv_one]
    rfl
  mul_smul σ τ u := by
    apply Subtype.ext
    show localUnitsEquiv (K := K) w (σ * τ) u.1
      = localUnitsEquiv (K := K) w σ (localUnitsEquiv (K := K) w τ u.1)
    rw [localUnitsEquiv_mul]
    rfl
  smul_mul σ u v := by
    apply Subtype.ext
    show localUnitsEquiv (K := K) w σ (u.1 * v.1)
      = localUnitsEquiv (K := K) w σ u.1 * localUnitsEquiv (K := K) w σ v.1
    rw [map_mul]
  smul_one σ := by
    apply Subtype.ext
    show localUnitsEquiv (K := K) w σ 1 = 1
    rw [map_one]

noncomputable def localUnitsSubRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    Rep CoeffInt (MulAction.stabilizer (L ≃ₐ[K] L) w) :=
  Rep.ofDistribMulAction CoeffInt _ (Additive ↥(Place.localUnits L w))

/-- **The inclusion `𝒪_wˣ ↪ L_wˣ` of local units into the local field's units**, as a morphism of
`Γ_w`-representations. -/
noncomputable def localUnitsIncl (w : Place L) :
    localUnitsSubRep K L w ⟶ localUnitsRep K L w :=
  Rep.ofHom
    { toFun := fun u =>
        Additive.ofMul ((Additive.toMul u : ↥(Place.localUnits L w)) : (Place.localField L w)ˣ)
      map_add' := fun x y => by
        show Additive.ofMul ((↑(Additive.toMul (x + y)) : (Place.localField L w)ˣ))
          = Additive.ofMul ((↑(Additive.toMul x) : (Place.localField L w)ˣ))
            + Additive.ofMul ((↑(Additive.toMul y) : (Place.localField L w)ˣ))
        rw [toMul_add, Subgroup.coe_mul, ofMul_mul]
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul ((↑(Additive.toMul (z • x)) : (Place.localField L w)ˣ))
          = z • Additive.ofMul ((↑(Additive.toMul x) : (Place.localField L w)ˣ))
        rw [toMul_zsmul, Subgroup.coe_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        rfl }

end

end NK.HassePrinciple
