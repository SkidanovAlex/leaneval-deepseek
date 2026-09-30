import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Multiplying an element of the ring of integers by an integer (via the
`ℤ`-algebra structure on `𝓞 F`) and then viewing it in `F` is the same as
multiplying the integer cast into `F` by the element. -/
lemma coe_intSMul_ringOfIntegers {F : Type*} [Field F] [NumberField F]
    (c : ℤ) (z : NumberField.RingOfIntegers F) :
    ((algebraMap ℤ (NumberField.RingOfIntegers F) c * z : NumberField.RingOfIntegers F) : F)
      = (c : F) * (z : F) := by
  change algebraMap (NumberField.RingOfIntegers F) F
      (algebraMap ℤ (NumberField.RingOfIntegers F) c * z) = _
  rw [map_mul]
  congr 1

theorem exists_int_mul_mem_fin {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (y : Fin N → F)
    (h : ∀ j, ∃ m : ℤ, m ≠ 0 ∧ ∃ z : NumberField.RingOfIntegers F,
      (z : F) = (m : F) * y j) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ z : Fin N → NumberField.RingOfIntegers F,
      ∀ j, (z j : F) = (m : F) * y j := by
  -- For every `j` pick a nonzero denominator `mm j` and a numerator `z j`.
  choose mm hm z hz using h
  -- The common denominator is the product of the individual denominators.
  refine ⟨∏ j, mm j, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => hm j)
  · refine ⟨fun j => algebraMap ℤ (NumberField.RingOfIntegers F)
        (∏ k ∈ Finset.univ.erase j, mm k) * z j, ?_⟩
    intro j
    -- `∏_{k ≠ j} mm k * mm j = ∏_k mm k`
    have hsplit : (∏ k ∈ Finset.univ.erase j, mm k) * mm j = ∏ k, mm k :=
      Finset.prod_erase_mul _ _ (Finset.mem_univ j)
    calc (((algebraMap ℤ (NumberField.RingOfIntegers F)
            (∏ k ∈ Finset.univ.erase j, mm k) * z j : NumberField.RingOfIntegers F)) : F)
        = ((∏ k ∈ Finset.univ.erase j, mm k : ℤ) : F) * (z j : F) :=
          coe_intSMul_ringOfIntegers _ _
      _ = ((∏ k ∈ Finset.univ.erase j, mm k : ℤ) : F) * ((mm j : F) * y j) := by rw [hz j]
      _ = (((∏ k ∈ Finset.univ.erase j, mm k) * mm j : ℤ) : F) * y j := by push_cast; ring
      _ = ((∏ k, mm k : ℤ) : F) * y j := by rw [hsplit]

end Work.BW
