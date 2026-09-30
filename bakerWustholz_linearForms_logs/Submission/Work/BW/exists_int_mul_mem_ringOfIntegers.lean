import Mathlib
import Submission.Work.BW.exists_int_mul_mem_fin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- Every element of a number field has a nonzero integer multiple in the ring of integers.

This is the statement that `𝒪_F` is a full `ℤ`-lattice in `F`: it says that `F` is the
localization of `𝒪_F` at the nonzero integers, which Mathlib records as the instance
`IsLocalization (Algebra.algebraMapSubmonoid (𝒪 F) ℤ⁰) F`. -/
theorem exists_int_mul_mem_ringOfIntegers_single (F : Type*) [Field F] [NumberField F] (x : F) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ z : NumberField.RingOfIntegers F,
      (z : F) = (m : F) * x := by
  obtain ⟨⟨y, s⟩, hs⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers F)
      (nonZeroDivisors ℤ)) x
  obtain ⟨m, hm, hms⟩ := (Submonoid.mem_map).mp s.2
  have hs' : x * ((s : NumberField.RingOfIntegers F) : F) = (y : F) := hs
  have hms' : (m : NumberField.RingOfIntegers F) = (s : NumberField.RingOfIntegers F) := hms
  refine ⟨m, ?_, y, ?_⟩
  · intro h0
    exact one_ne_zero (hm.1 1 (by rw [h0, zero_mul]))
  · rw [← hs', ← hms']
    rw [show ((m : NumberField.RingOfIntegers F) : F) = (m : F) from
      (IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers F) F m).symm, mul_comm]

theorem exists_int_mul_mem_ringOfIntegers {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (y : Fin N → F) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ z : Fin N → NumberField.RingOfIntegers F,
      ∀ j, (z j : F) = (m : F) * y j :=
  exists_int_mul_mem_fin y fun j => exists_int_mul_mem_ringOfIntegers_single F (y j)

end Work.BW
