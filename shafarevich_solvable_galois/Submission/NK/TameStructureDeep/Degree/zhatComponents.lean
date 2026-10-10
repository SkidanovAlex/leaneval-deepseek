import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.TameStructure.ProCyclic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep.Degree

open NK.TameStructure.ProCyclic

noncomputable section

/-- The reduction `Multiplicative ℤ →* Multiplicative (ZMod d)`, `ofAdd k ↦ ofAdd (k mod d)`. -/
def toZModHom (d : ℕ) : Multiplicative ℤ →* Multiplicative (ZMod d) where
  toFun x := Multiplicative.ofAdd (((Multiplicative.toAdd x : ℤ) : ZMod d))
  map_one' := by rw [toAdd_one, Int.cast_zero, ofAdd_zero]
  map_mul' a b := by
    rw [toAdd_mul]
    show Multiplicative.ofAdd
      ((((Multiplicative.toAdd a : ℤ) + (Multiplicative.toAdd b : ℤ) : ℤ) : ZMod d)) = _
    rw [Int.cast_add, ofAdd_add]

theorem toZModHom_apply (d : ℕ) (k : ℤ) :
    toZModHom d (Multiplicative.ofAdd k) = Multiplicative.ofAdd ((k : ZMod d)) := rfl

/-- The kernel of the reduction map is `dℤ`. -/
theorem ker_toZModHom (d : ℕ) (hd : d ≠ 0) :
    (toZModHom d).ker = (mZ d hd).toSubgroup := by
  ext x
  rw [MonoidHom.mem_ker, ← ofAdd_toAdd x, mem_mZ, toZModHom_apply]
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem toZModHom_surjective (d : ℕ) (hd : d ≠ 0) : Function.Surjective (toZModHom d) := by
  haveI : NeZero d := ⟨hd⟩
  intro y
  refine ⟨Multiplicative.ofAdd (((Multiplicative.toAdd y).val : ℕ) : ℤ), ?_⟩
  rw [toZModHom_apply]
  have h1 : (((((Multiplicative.toAdd y).val : ℕ) : ℤ)) : ZMod d) =
      Multiplicative.toAdd y := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [h1, ofAdd_toAdd]

/-- **The `d`-th component of `Ẑ`**, read as an element of `Multiplicative (ZMod d)`. -/
def zmodQuotEquiv (d : ℕ) (hd : d ≠ 0) :
    ((Multiplicative ℤ) ⧸ (mZ d hd).toSubgroup) ≃* Multiplicative (ZMod d) :=
  QuotientGroup.liftEquiv (mZ d hd).toSubgroup (toZModHom_surjective d hd)
    (ker_toZModHom d hd).symm

@[simp]
theorem zmodQuotEquiv_mk (d : ℕ) (hd : d ≠ 0) (x : Multiplicative ℤ) :
    zmodQuotEquiv d hd (QuotientGroup.mk' _ x) = toZModHom d x := rfl

/-- The `d`-th component of `Ẑ` as a homomorphism onto `Multiplicative (ZMod d)`. -/
def compHomZMod (d : ℕ) (hd : d ≠ 0) :
    NK.LocalAnabelian.Zhat →* Multiplicative (ZMod d) :=
  (zmodQuotEquiv d hd).toMonoidHom.comp (compHom d hd)

@[simp]
theorem compHomZMod_apply (d : ℕ) (hd : d ≠ 0) (z : NK.LocalAnabelian.Zhat) :
    compHomZMod d hd z = zmodQuotEquiv d hd (compHom d hd z) := rfl

/-- The index subgroups of the completion diagram are nested: `dℤ ≤ eℤ` when `e ∣ d`. -/
theorem mZ_le_mZ {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) (h : e ∣ d) :
    (mZ d hd).toSubgroup ≤ (mZ e he).toSubgroup := by
  intro x hx
  rw [← ofAdd_toAdd x, mem_mZ] at hx ⊢
  exact dvd_trans (by exact_mod_cast h) hx

end

end NK.TameStructureDeep.Degree
