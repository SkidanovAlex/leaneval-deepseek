/-
# The "swap" inequality for Hall foliages

If `u` is a nonempty word and `u ++ v < v` (lexicographically), then `u ++ v < v ++ u`.
This is applied to `u = foliage a`, `v = foliage b` for a Hall tree `mul a b`, for which the
combinatorial input `hall_foliage_lt_right` supplies `u ++ v < v`.
-/
import Mathlib
import Submission.Work.SSGRoute.prop5.witt.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

universe u

/-- If `u ++ v < v` then `u ++ v < v ++ u` (as `v` is a prefix of `v ++ u`). -/
lemma swap_le_of_lt {X : Type u} [LinearOrder X] {u v : List X} (h : u ++ v < v) :
    u ++ v < v ++ u :=
  List.Lex.append_right (· < ·) u ((List.lt_iff_lex_lt _ _).mp h)

/-- The swap inequality for Hall foliages, deduced from the basic property
`foliage (mul a b) < foliage b`. -/
lemma swap_hall_of_crux {X : Type u} [LinearOrder X]
    (hcrux : ∀ a b : Magma X, IsHall (Magma.mul a b) →
      Magma.foliage (Magma.mul a b) < Magma.foliage b)
    {a b : Magma X} (h : IsHall (Magma.mul a b)) :
    Magma.foliage a ++ Magma.foliage b < Magma.foliage b ++ Magma.foliage a :=
  swap_le_of_lt (hcrux a b h)

end Work.SSGRoute.prop5
