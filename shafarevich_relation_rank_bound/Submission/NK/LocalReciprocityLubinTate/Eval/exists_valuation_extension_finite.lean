import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
import Submission.Commons.RingTheory.Valuation.hasExtension_comap_of_comap_eq
import Submission.NK.LocalReciprocityLubinTate.Eval.nonempty_orderIso_valueGroupZero_of_localField
import Submission.NK.LocalReciprocityLubinTate.Eval.nonempty_orderIso_of_finite_quotient
import Submission.NK.LocalReciprocityLubinTate.Eval.finite_quotient_valueGroup_of_finiteDimensional

universe u

namespace NK.LocalReciprocityLubinTate.Eval

open scoped WithZero

theorem exists_valuation_extension_finite (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ w : Valuation L (WithZero (Multiplicative ℤ)),
      Valuation.HasExtension (ValuativeRel.valuation K) w := by
  obtain ⟨W, hW⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq (L := L)
    ((ValuativeRel.valuation K).valuationSubring)
  have hfin : Finite (W.ValueGroupˣ ⧸
      MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass (W.valuation.comap (algebraMap K L)))) :=
    (finite_quotient_valueGroup_of_finiteDimensional W).1
  have hiso : Nonempty (WithZero (MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass (W.valuation.comap (algebraMap K L)))) ≃*o
      WithZero (Multiplicative ℤ)) := nonempty_orderIso_valueGroupZero_of_localField W hW
  obtain ⟨φ⟩ := nonempty_orderIso_of_finite_quotient _ hfin hiso
  have hmono : Monotone (⇑φ.toMonoidWithZeroHom) :=
    fun _ _ h => (φ.map_le_map_iff').mpr h
  let w : Valuation L (WithZero (Multiplicative ℤ)) := W.valuation.map φ.toMonoidWithZeroHom hmono
  have key : ∀ a : W.ValueGroup, φ.toMonoidWithZeroHom a ≤ 1 ↔ a ≤ 1 := fun a => by
    rw [← map_one φ.toMonoidWithZeroHom]
    exact φ.map_le_map_iff'
  have hmap : w.valuationSubring = W := by
    ext x
    rw [Valuation.mem_valuationSubring_iff]
    show (W.valuation.map φ.toMonoidWithZeroHom hmono) x ≤ 1 ↔ x ∈ W
    rw [Valuation.map_apply, ← ValuationSubring.valuation_le_one_iff (A := W) x]
    exact key (W.valuation x)
  refine ⟨w, ?_⟩
  refine ⟨?_⟩
  rw [Valuation.isEquiv_iff_valuationSubring]
  have hcomap : (w.comap (algebraMap K L)).valuationSubring
      = (ValuativeRel.valuation K).valuationSubring := by
    rw [Commons.RingTheory.Valuation.valuationSubring_comap, hmap, hW]
  exact hcomap.symm

end NK.LocalReciprocityLubinTate.Eval
