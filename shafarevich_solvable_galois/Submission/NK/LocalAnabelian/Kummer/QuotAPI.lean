import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Submission.NK.LocalAnabelian.Kummer.Quot
import Submission.NK.LocalAnabelian.Kummer.kummerField_eq_of_div_mem_powSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

noncomputable section

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']

/-- The Kummer field of a class is the Kummer field of any of its representatives. -/
theorem kummerFieldQuot_mk (p : ℕ) (a : kˣ) :
    kummerFieldQuot (K' := K') p (QuotientGroup.mk a) = kummerField (K' := K') p a :=
  Kummer.kummerField_eq_of_div_mem_powSubgroup (K' := K') p
    (QuotientGroup.leftRel_apply.mp
      (Quotient.exact (Quotient.out_eq (QuotientGroup.mk a))))

/-- The Kummer field of a class, evaluated on a representative. -/
theorem kummerFieldQuot_eq_kummerField (p : ℕ) {x : KummerGroup p k} (a : kˣ)
    (h : QuotientGroup.mk a = x) :
    kummerFieldQuot (K' := K') p x = kummerField (K' := K') p a := by
  rw [← h, kummerFieldQuot_mk]

/-- A class is trivial exactly when its representative is a `p`-th power. -/
theorem kummerGroup_mk_eq_one_iff {p : ℕ} (a : kˣ) :
    QuotientGroup.mk a = (1 : KummerGroup p k) ↔ a ∈ powSubgroup p k := by
  constructor
  · intro h
    have hrel : a⁻¹ * 1 ∈ powSubgroup p k :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact h)
    simpa using (powSubgroup p k).inv_mem_iff.mp (by simpa using hrel)
  · intro h
    refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
    simpa using (powSubgroup p k).inv_mem_iff.mpr h

/-- A nontrivial class has a representative which is not a `p`-th power. -/
theorem notMem_powSubgroup_of_out_ne_one {p : ℕ} {x : KummerGroup p k} (hx : x ≠ 1) :
    Quotient.out x ∉ powSubgroup p k := by
  intro h
  apply hx
  rw [← Quotient.out_eq x]
  exact (kummerGroup_mk_eq_one_iff (p := p) (Quotient.out x)).mpr h

/-- The Kummer class group has exponent `p`. -/
theorem kummerGroup_pow_self (p : ℕ) (x : KummerGroup p k) : x ^ p = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow (powSubgroup p k) a p]
  exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨a, rfl⟩)

end

end NK.LocalAnabelian
