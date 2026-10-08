import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-- The kernel of the reduction map `ZMod n → ZMod m` (with `m ∣ n`) is the ideal generated
by `m` inside `ZMod n`.

Any integer representative `z` of `a` is killed by the reduction modulo `m`, hence `m ∣ z`, so
`a = m * b` for `b` the reduction of the quotient. -/
theorem exists_eq_mul_of_castHom_eq_zero {m n : ℕ} (h : m ∣ n) (a : ZMod n)
    (ha : ZMod.castHom h (ZMod m) a = 0) : ∃ b : ZMod n, a = (m : ZMod n) * b := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  have hz : (z : ZMod m) = 0 := by
    simpa using ha
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z m).mp hz
  refine ⟨(t : ZMod n), ?_⟩
  rw [ht]
  push_cast
  ring

end Work.BSLit.Wielandt
