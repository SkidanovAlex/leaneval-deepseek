import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unit idèles and the unit part of a fibre

This file collects the `ℤ[Gal(L/K)]`-modules whose Herbrand quotients enter Milne's
Proposition 2.7 (the computation `h(𝕀_{L,T}) = ∏_{v ∈ S} [L_w : K_v]`):

* `localUnitIdeles L` — the idèles all of whose components are local units (the "integral
  idèles" in the sense that at an archimedean place every element is a local unit);
* `fiberUnits v` — the *unit part of the fibre of `v`*: those idèles supported on the places
  above `v` all of whose components are local units;
* `unitIdelesOutside T` — the idèles which are `1` on `T` and local units outside `T`; for
  `T ⊇ T_∞` this is Milne's `∏_{w ∉ T, w finite} U_w`, whose Herbrand quotient is `1`
  (Milne III.2.5);
* `unityIdelesRep` — the same object for `T = T_∞`, i.e. the unit idèles `∏_{w finite} U_w`
  of the delivered chapter (`NK.GlobalCFT.Idele.unityIdeles`).

All of them are stable under `Gal(L/K)` and are recorded here as `Rep ℤ (L ≃ₐ[K] L)`-modules.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The Galois action preserves infinitude of a place. -/
@[simp] theorem isInfinite_smul (σ : L ≃ₐ[K] L) (w : Place L) :
    (σ • w).IsInfinite ↔ w.IsInfinite := by
  cases w <;> simp [Place.IsInfinite]

/-- The Galois action preserves finiteness of a place. -/
@[simp] theorem isFinite_smul (σ : L ≃ₐ[K] L) (w : Place L) :
    (σ • w).IsFinite ↔ w.IsFinite := by
  cases w <;> simp [Place.IsFinite, Place.IsInfinite]

/-! ### The idèles all of whose components are local units -/

/-- The idèles all of whose components are local units.  (At an archimedean place every element
is a local unit, so this is the same subgroup as `Idele.integralIdeles`.) -/
def localUnitIdeles (L : Type*) [Field L] [NumberField L] : Subgroup (Idele L) where
  carrier := {x | ∀ w : Place L, x w ∈ Place.localUnits L w}
  one_mem' := fun w => Subgroup.one_mem _
  mul_mem' := fun hx hy w => by
    rw [Idele.mul_apply]; exact mul_mem (hx w) (hy w)
  inv_mem' := fun hx w => by
    rw [Idele.inv_apply]; exact inv_mem (hx w)

@[simp] theorem mem_localUnitIdeles {x : Idele L} :
    x ∈ localUnitIdeles L ↔ ∀ w : Place L, x w ∈ Place.localUnits L w := Iff.rfl

theorem localUnitIdeles_le_integralIdeles :
    localUnitIdeles L ≤ Idele.integralIdeles L :=
  fun x hx w _ => hx w

/-- The local units are stable under the local isomorphism, in the inverse direction. -/
theorem mem_localUnits_of_map_symm {σ : L ≃ₐ[K] L} {w : Place L}
    {u : (Place.localField L (σ • w))ˣ} (hu : u ∈ Place.localUnits L (σ • w)) :
    Units.map (Place.localRingEquiv σ w).symm.toMonoidHom u ∈ Place.localUnits L w := by
  refine (Place.localRingEquiv_mem_localUnits σ w _).mpr ?_
  have h : Units.map (Place.localRingEquiv σ w).toMonoidHom
      (Units.map (Place.localRingEquiv σ w).symm.toMonoidHom u) = u := by
    ext; simp
  rw [h]; exact hu

/-- The idèles all of whose components are local units are stable under `Gal(L/K)`. -/
theorem smul_mem_localUnitIdeles {σ : L ≃ₐ[K] L} {x : Idele L} (hx : x ∈ localUnitIdeles L) :
    σ • x ∈ localUnitIdeles L := by
  intro w
  rw [Idele.smul_apply]
  exact mem_localUnits_of_map_symm (σ := σ⁻¹) (w := w) (hx (σ⁻¹ • w))

/-- The idèles all of whose components are local units, as a `ℤ[Gal(L/K)]`-module. -/
def localUnitIdelesRep : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (localUnitIdeles L) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (localUnitIdeles L)
      (fun σ x hx => smul_mem_localUnitIdeles hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (localUnitIdeles L)

/-! ### The unit part of the fibre of a place of `K` -/

/-- **The unit part of the fibre of `v`**: the idèles supported on the places of `L` above `v`
all of whose components are local units.  For `v` finite this is Milne's `∏_{w | v} U_w`. -/
def fiberUnits (v : Place K) : Subgroup (Idele L) :=
  fiberIdeles (K := K) (L := L) v ⊓ localUnitIdeles L

@[simp] theorem mem_fiberUnits {v : Place K} {x : Idele L} :
    x ∈ fiberUnits (K := K) (L := L) v ↔
      (∀ w : Place L, ¬ Place.LiesOver w v → x w = 1) ∧
        (∀ w : Place L, x w ∈ Place.localUnits L w) := by
  rw [fiberUnits, Subgroup.mem_inf, mem_fiberIdeles, mem_localUnitIdeles]

theorem smul_mem_fiberUnits {v : Place K} {σ : L ≃ₐ[K] L} {x : Idele L}
    (hx : x ∈ fiberUnits (K := K) (L := L) v) : σ • x ∈ fiberUnits (K := K) (L := L) v :=
  mem_fiberUnits.mpr ⟨fun w hw => smul_mem_fiberIdeles v hx.1 w hw,
    fun w => smul_mem_localUnitIdeles hx.2 w⟩

/-- **The unit part of the fibre of `v`, as a `ℤ[Gal(L/K)]`-module.** -/
def fiberUnitsRep (v : Place K) : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (fiberUnits (K := K) (L := L) v) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (fiberUnits (K := K) (L := L) v)
      (fun σ x hx => smul_mem_fiberUnits hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (fiberUnits (K := K) (L := L) v)

/-! ### The unit idèles of `L` (`T = T_∞`) -/

/-- The unit idèles `∏_{w finite} U_w` of `L` (`Idele.unityIdeles`) are stable under
`Gal(L/K)`. -/
theorem smul_mem_unityIdeles {σ : L ≃ₐ[K] L} {x : Idele L} (hx : x ∈ Idele.unityIdeles L) :
    σ • x ∈ Idele.unityIdeles L := by
  have hx' := (Idele.mem_unityIdeles (K := L)).mp hx
  refine (Idele.mem_unityIdeles (K := L)).mpr ⟨?_, ?_⟩
  · intro w hw
    rw [Idele.smul_apply, hx'.1 (σ⁻¹ • w) (by simpa using hw), map_one]
  · intro w hw
    rw [Idele.smul_apply]
    exact mem_localUnits_of_map_symm (σ := σ⁻¹) (w := w)
      (hx'.2 (σ⁻¹ • w) (by simpa using hw))

/-- **The unit idèles of `L`, as a `ℤ[Gal(L/K)]`-module.**  This is the module `∏_{w finite} U_w`
whose Herbrand quotient is `1` (Milne III.2.5). -/
def unityIdelesRep : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (Idele.unityIdeles L) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (Idele.unityIdeles L)
      (fun σ x hx => smul_mem_unityIdeles hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (Idele.unityIdeles L)

/-! ### The idèles which are `1` on `T` and local units outside `T` -/

/-- **The unit idèles outside `T`**: the idèles which are `1` on `T` and are local units at every
other place.  For `T` a set of places containing all the archimedean places, this is Milne's
`∏_{w ∉ T, w finite} U_w`, whose Herbrand quotient is `1` (Milne III.2.5). -/
def unitIdelesOutside (T : Set (Place L)) : Subgroup (Idele L) where
  carrier := {x | (∀ w ∈ T, x w = 1) ∧ (∀ w : Place L, x w ∈ Place.localUnits L w)}
  one_mem' := ⟨fun w _ => rfl, fun w => Subgroup.one_mem _⟩
  mul_mem' := fun hx hy => ⟨fun w hw => by
      rw [Idele.mul_apply, hx.1 w hw, hy.1 w hw, one_mul],
    fun w => by rw [Idele.mul_apply]; exact mul_mem (hx.2 w) (hy.2 w)⟩
  inv_mem' := fun hx => ⟨fun w hw => by
      rw [Idele.inv_apply, hx.1 w hw, inv_one],
    fun w => by rw [Idele.inv_apply]; exact inv_mem (hx.2 w)⟩

@[simp] theorem mem_unitIdelesOutside {T : Set (Place L)} {x : Idele L} :
    x ∈ unitIdelesOutside T ↔ (∀ w ∈ T, x w = 1) ∧
      (∀ w : Place L, x w ∈ Place.localUnits L w) := Iff.rfl

/-- The unit idèles outside `T` are `T`-idèles. -/
theorem unitIdelesOutside_le_TIdeles (T : Set (Place L)) :
    unitIdelesOutside T ≤ TIdeles T :=
  fun x hx w hw => hx.2 w

/-- The unit idèles outside `T` are stable under `Gal(L/K)` when `T` is. -/
theorem smul_mem_unitIdelesOutside {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    {σ : L ≃ₐ[K] L} {x : Idele L} (hx : x ∈ unitIdelesOutside T) :
    σ • x ∈ unitIdelesOutside T := by
  refine mem_unitIdelesOutside.mpr ⟨?_, fun w => ?_⟩
  · intro w hw
    rw [Idele.smul_apply]
    have h2 : x (σ⁻¹ • w) = 1 := hx.1 (σ⁻¹ • w) (hT (σ := σ⁻¹) hw)
    rw [h2, map_one]
  · rw [Idele.smul_apply]
    exact mem_localUnits_of_map_symm (σ := σ⁻¹) (w := w) (hx.2 (σ⁻¹ • w))

/-- **The unit idèles outside `T`, as a `ℤ[Gal(L/K)]`-module.** -/
def unitIdelesOutsideRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (unitIdelesOutside T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (unitIdelesOutside T)
      (fun σ x hx => smul_mem_unitIdelesOutside hT hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitIdelesOutside T)

end NK.GlobalCFTdeep
