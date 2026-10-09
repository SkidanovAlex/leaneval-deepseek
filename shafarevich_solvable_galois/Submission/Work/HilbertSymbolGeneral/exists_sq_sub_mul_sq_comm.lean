import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbolGeneral

/-!
# Symmetry of representability by the binary form `X ^ 2 - d * Y ^ 2`

Let `F` be a field with `2 ≠ 0` (i.e. `NeZero (2 : F)`) and `a b ∈ Fˣ`.  Then `a` is represented by
the form `X ^ 2 - b * Y ^ 2` if and only if `b` is represented by `X ^ 2 - a * Y ^ 2`.

Intended proof: given `a = u ^ 2 - b * v ^ 2`, if `v ≠ 0` then `b = (u / v) ^ 2 - a * (1 / v) ^ 2`
(because `u ^ 2 - a = b * v ^ 2`, so `(u ^ 2 - a) / v ^ 2 = b`).  If `v = 0` then `a = u ^ 2` with
`u ≠ 0`, and then `b = X ^ 2 - a * Y ^ 2` for `X = (b + 1) / 2`, `Y = (1 - b) / (2 * u)`
(because `X - u * Y = b` and `X + u * Y = 1`).  Both divisions use `2 ≠ 0` and `u ≠ 0`.  The
converse is the same argument with the roles of `a` and `b` exchanged, so it suffices to prove one
implication in a form symmetric in the two units.
-/

/-- One direction of the symmetry, stated symmetrically in the two units `c`, `d`: if `c` is
represented by `X ^ 2 - d * Y ^ 2`, then `d` is represented by `X ^ 2 - c * Y ^ 2`.  The target
statement is then obtained by applying this in both directions. -/
private theorem exists_sq_sub_mul_sq_one_dir {F : Type*} [Field F] [NeZero (2 : F)]
    (c d : Fˣ) (h : ∃ u v : F, u ^ 2 - (d : F) * v ^ 2 = (c : F)) :
    ∃ u v : F, u ^ 2 - (c : F) * v ^ 2 = (d : F) := by
  obtain ⟨u, v, huv⟩ := h
  by_cases hv : v = 0
  · -- `v = 0`, so `c = u ^ 2` with `u ≠ 0`; use `X = (d + 1) / 2`, `Y = (1 - d) / (2 * u)`.
    subst hv
    have huv' : u ^ 2 = (c : F) := by simpa using huv
    have hu : u ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num)] at huv'
      exact c.ne_zero huv'.symm
    refine ⟨((d : F) + 1) / 2, (1 - (d : F)) / (2 * u), ?_⟩
    rw [← huv']
    field_simp
    ring
  · -- `v ≠ 0`; use `u' = u / v`, `v' = 1 / v`.
    refine ⟨u / v, 1 / v, ?_⟩
    field_simp
    linear_combination huv

theorem exists_sq_sub_mul_sq_comm {F : Type*} [Field F] [NeZero (2 : F)] (a b : Fˣ) :
    (∃ u v : F, u ^ 2 - (b : F) * v ^ 2 = (a : F)) ↔
      ∃ u v : F, u ^ 2 - (a : F) * v ^ 2 = (b : F) :=
  ⟨exists_sq_sub_mul_sq_one_dir a b, exists_sq_sub_mul_sq_one_dir b a⟩

end Work.HilbertSymbolGeneral
