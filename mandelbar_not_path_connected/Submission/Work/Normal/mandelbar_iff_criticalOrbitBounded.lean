import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.Tricorn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The mandelbar is the boundedness locus of the critical orbit of the quartic `TantibarSq c`

The antiholomorphic quadratic map `T̄_c(z) = (conj z)^2 + c` has second iterate the
holomorphic quartic `TantibarSq c`, `z ↦ (z^2 + conj c)^2 + c`.  Membership of `c` in the
mandelbar means precisely that the orbit of the critical point `0` under `T̄_c` is bounded.

Because `TantibarSq c = T̄_c^[2]`, the even part of the `T̄_c`-orbit of `0` is the
`TantibarSq c`-orbit of `0` (`tantibar_iterate_even`), while the odd part is controlled by the
elementary bound `‖T̄_c w‖ ≤ ‖w‖^2 + ‖c‖`.  Hence the two boundedness conditions are
equivalent.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology

/-- The elementary growth bound for the antiholomorphic quadratic map: the square of the
modulus grows at least quadratically. -/
theorem norm_tantibar_le (c w : ℂ) :
    ‖LeanEval.ComplexAnalysis.Tantibar c w‖ ≤ ‖w‖ ^ 2 + ‖c‖ := by
  calc ‖LeanEval.ComplexAnalysis.Tantibar c w‖ = ‖(starRingEnd ℂ w) ^ 2 + c‖ := rfl
    _ ≤ ‖(starRingEnd ℂ w) ^ 2‖ + ‖c‖ := norm_add_le _ _
    _ = ‖w‖ ^ 2 + ‖c‖ := by rw [norm_pow, starRingEnd_apply, norm_star]

/-- The mandelbar is the set of parameters `c` for which the critical orbit of the holomorphic
quartic `TantibarSq c` (the second iterate of the antiholomorphic map `T̄_c`) is bounded.

Route: use `tantibar_iterate_even` for the even iterates, and the bound
`‖T̄_c w‖ ≤ ‖w‖ ^ 2 + ‖c‖` to dominate the odd iterates by the even ones. -/
theorem mandelbar_iff_criticalOrbitBounded (c : ℂ) :
    c ∈ LeanEval.ComplexAnalysis.Mandelbar ↔ 0 ∈ FilledJuliaSet (TantibarSq c) := by
  constructor
  · -- A bounded `T̄_c`-orbit of `0` gives a bounded `TantibarSq c`-orbit of `0`.
    rintro ⟨M, hM⟩
    exact ⟨M, fun n => by rw [← tantibar_iterate_even c n]; exact hM (2 * n)⟩
  · -- Conversely the odd iterates are `T̄_c` applied to the even iterates.
    rintro ⟨M, hM⟩
    refine ⟨max M (M ^ 2 + ‖c‖), fun n => ?_⟩
    rcases Nat.even_or_odd n with h | h
    · obtain ⟨k, hk⟩ := h
      subst hk
      rw [← two_mul, tantibar_iterate_even]
      exact (hM k).trans (le_max_left _ _)
    · obtain ⟨k, hk⟩ := h
      subst hk
      rw [show 2 * k + 1 = Nat.succ (2 * k) from rfl, Function.iterate_succ_apply',
        tantibar_iterate_even]
      have hb := norm_tantibar_le c ((TantibarSq c)^[k] 0)
      have hle : ‖(TantibarSq c)^[k] 0‖ ^ 2 ≤ M ^ 2 := by
        nlinarith [hM k, norm_nonneg ((TantibarSq c)^[k] 0)]
      linarith [le_max_right M (M ^ 2 + ‖c‖)]

end Work.Normal
