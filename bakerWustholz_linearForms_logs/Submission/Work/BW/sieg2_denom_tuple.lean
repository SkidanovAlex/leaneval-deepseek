import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Clearing denominators in a finite tuple in a number field

Given a finite family `a : Fin n → F` of elements of a number field `F`, there is a
nonzero element `d` of the ring of integers `𝓞 F` which clears all denominators at
once: `d * a j ∈ 𝓞 F` for every `j`.

This is the statement that `F` is the fraction field of `𝓞 F`, together with the
standard "clear denominators of a finite family" construction
(`IsLocalization.exist_integer_multiples`).
-/

namespace Work.BW

open NumberField

theorem sieg2_denom_tuple {F : Type*} [Field F] [NumberField F] {n : ℕ}
    (a : Fin n → F) :
    ∃ d : NumberField.RingOfIntegers F, d ≠ 0 ∧
      ∃ b : Fin n → NumberField.RingOfIntegers F,
        ∀ j, ((b j : NumberField.RingOfIntegers F) : F) = (d : F) * a j := by
  classical
  -- `F` is the fraction field of its ring of integers, so finitely many denominators
  -- can be cleared simultaneously.
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) Finset.univ a
  -- `hd j` states that `(d : 𝓞 F) • a j` lies in the image of `𝓞 F → F`.
  have hd' : ∀ j : Fin n, ∃ c : 𝓞 F,
      algebraMap (𝓞 F) F c = (d : 𝓞 F) • a j :=
    fun j => RingHom.mem_rangeS.mp (hd j (Finset.mem_univ j))
  choose b hb using hd'
  refine ⟨d, ?_, b, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp d.2
  · intro j
    rw [RingOfIntegers.coe_eq_algebraMap, hb j, Algebra.smul_def]

end Work.BW
