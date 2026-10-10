import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RamificationDeep

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The natural ring homomorphism `𝔬 = A ∩ K → A`, `k ↦ algebraMap K L k`. -/
def comapHom (A : ValuationSubring L) : ↥(A.comap (algebraMap K L)) →+* ↥A where
  toFun k := ⟨algebraMap K L (k : K), ValuationSubring.mem_comap.mp k.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem comapHom_apply (A : ValuationSubring L) (k : ↥(A.comap (algebraMap K L))) :
    (comapHom A k).1 = algebraMap K L (k : K) := rfl

@[simp]
theorem algebraMap_subtypeMem_apply (A : ValuationSubring L) (z : ↥A) :
    algebraMap ↥A L z = z.1 := rfl

theorem comapHom_injective (A : ValuationSubring L) :
    Function.Injective (comapHom A : ↥(A.comap (algebraMap K L)) → ↥A) := by
  intro x y h
  have h2 : algebraMap K L (x : K) = algebraMap K L (y : K) := by
    rw [← comapHom_apply, ← comapHom_apply, h]
  exact Subtype.ext (FaithfulSMul.algebraMap_injective K L h2)

/-- `A` is an algebra over `𝔬 = A ∩ K` via the natural map. -/
instance instAlgebraComap (A : ValuationSubring L) : Algebra ↥(A.comap (algebraMap K L)) ↥A :=
  (comapHom A).toAlgebra

@[simp]
theorem algebraMap_comap_apply (A : ValuationSubring L) (k : ↥(A.comap (algebraMap K L))) :
    algebraMap ↥(A.comap (algebraMap K L)) ↥A k = comapHom A k := rfl

@[simp]
theorem coe_algebraMap_comap_apply (A : ValuationSubring L) (k : ↥(A.comap (algebraMap K L))) :
    (algebraMap ↥(A.comap (algebraMap K L)) ↥A k).1 = algebraMap K L (k : K) := rfl

/-- `L` is an algebra over `𝔬 = A ∩ K` via `𝔬 → K → L`. -/
instance instAlgebraComapL (A : ValuationSubring L) : Algebra ↥(A.comap (algebraMap K L)) L :=
  ((algebraMap K L).comp (A.comap (algebraMap K L)).toSubring.subtype).toAlgebra

@[simp]
theorem algebraMap_comap_L_apply (A : ValuationSubring L) (k : ↥(A.comap (algebraMap K L))) :
    (algebraMap ↥(A.comap (algebraMap K L)) L) k = algebraMap K L (k : K) := rfl

instance instIsScalarTowerComapK (A : ValuationSubring L) :
    IsScalarTower ↥(A.comap (algebraMap K L)) K L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance instIsScalarTowerComapA (A : ValuationSubring L) :
    IsScalarTower ↥(A.comap (algebraMap K L)) ↥A L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end NK.RamificationDeep
