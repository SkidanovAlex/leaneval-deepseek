import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The landing point of the parameter ray `R(23/63)` is not parabolic

`Work.LANDCL.OnlyParabolicIsCycleOf c z₁` records the classical portrait fact at the root of the
non-real period-`5` hyperbolic component of the tricorn: the *only* parabolic points of `T_c` are
the five points of the exact period-`5` cycle of the characteristic point `z₁`.  In particular
every parabolic point is fixed by `(T_c)^[5]` and is **not** fixed by `T_c`.

On the other hand the window ray `R_c(23/63)` lands at a point of *exact* angle period `6`, hence
at a point fixed by `(T_c)^[6]` (`Work.Landing.landsAt_periodic`).  Since `gcd 5 6 = 1`, a point
fixed by both `(T_c)^[5]` and `(T_c)^[6]` is fixed by `T_c`
(`Work.Landing.Family.iterate_one_eq_of_iterate_eq`), which no point of the period-`5` cycle is.
Hence the landing point of `R_c(23/63)` is not parabolic — the content of this file, stated in the
form used by `Work.LANDCL.paramAngleRepelling_of_rootParabolic`:

> `∀ m, ¬ IsParabolic c m z`.

The only combinatorial input is that a point `z = (T_c)^[j] z₁` of the cycle, `j < 5`, is not
fixed by `T_c`; this is `apply_eq_self_of_iterate_eq` below, applied with `n = 5`: if
`(T_c)^[j] z₁ = (T_c)^[j+1] z₁` then `(T_c)^[4] z₁ = (T_c)^[5] z₁ = z₁`, whence
`T_c z₁ = T_c ((T_c)^[4] z₁) = (T_c)^[5] z₁ = z₁`, contradicting the exactness of the period.
-/

namespace Work.LANDCL.ParamAngle

/-- If `x` is periodic of period `n` for `f`, then `f^[n]` fixes every point `f^[j] x` of the
orbit of `x`. -/
lemma iterate_period_apply {α : Type*} {f : α → α} {x : α} {n j : ℕ} (hn : f^[n] x = x) :
    f^[n] (f^[j] x) = f^[j] x := by
  rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hn]

/-- If `x` has period `n` and two consecutive points `f^[j] x`, `f^[j+1] x` of its orbit
coincide (`j < n`), then `x` is a fixed point of `f`.

Indeed the equality propagates `n - (j + 1)` steps forward to `f^[n-1] x = f^[n] x = x`, and then
`f x = f (f^[n-1] x) = f^[n] x = x`.  Applied with `n` the period this says: a point of the orbit
of `x` at a non-`n` step is not fixed by `f` unless `x` itself is. -/
lemma apply_eq_self_of_iterate_eq {α : Type*} {f : α → α} {x : α} {n j : ℕ}
    (hn : f^[n] x = x) (hj : j < n) (h : f^[j] x = f^[j + 1] x) : f x = x := by
  have hle : j + 1 ≤ n := hj
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hj
  -- Propagate `f^[j] x = f^[j+1] x` forward by `n - (j+1)` steps.
  have h2 : f^[n - 1] x = x := by
    have key := congrArg (fun w => f^[n - (j + 1)] w) h
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at key
    rw [show n - (j + 1) + j = n - 1 from by omega,
        show n - (j + 1) + (j + 1) = n from Nat.sub_add_cancel hle, hn] at key
    exact key
  -- `f x = f (f^[n-1] x) = f^[n] x = x`.
  have h3 : f^[n] x = f (f^[n - 1] x) := by
    conv_lhs => rw [show n = 1 + (n - 1) from by omega]
    rw [Function.iterate_add_apply, Function.iterate_one]
  rw [h3, h2] at hn
  exact hn

/-- **The landing point of `R_c(23/63)` is not parabolic**, given that the only parabolic points
of `T_c` lie on the exact period-`5` cycle of `z₁`.

Any parabolic point of `T_c` is a point `T_c^[j] z₁`, `j < 5`, of that cycle; such a point is
fixed by `(T_c)^[5]` but not by `T_c`.  Hence, as the landing point of `R_c(23/63)`, it is also
fixed by `(T_c)^[6]` and therefore (coprimality of `5` and `6`) by `T_c` — contradiction. -/
theorem not_isParabolic_of_landsAt_paramAngle {c z₁ z : ℂ}
    (huniq : Work.LANDCL.OnlyParabolicIsCycleOf c z₁)
    (hland : Work.Landing.landsAt c Work.Landing.paramAngle z) :
    ∀ m : ℕ, ¬ Work.Landing.IsParabolic c m z := by
  obtain ⟨hper, hne, hcyc⟩ := huniq
  intro m hm
  -- `z` lies on the period-`5` cycle of `z₁`.
  obtain ⟨j, hj, hzj⟩ := hcyc z ⟨m, hm⟩
  refine Work.Landing.landsAt_paramAngle_not_parabolic hland ?_ ?_
  · -- `(T_c)^[5] z = z`.
    rw [hzj]
    exact iterate_period_apply hper
  · -- `z` is not fixed by `T_c`.
    rw [hzj]
    intro hcon
    have hcon' : (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ =
        (LeanEval.ComplexAnalysis.Tantibar c)^[j + 1] z₁ := by
      rw [Function.iterate_succ_apply']
      exact hcon.symm
    exact hne (apply_eq_self_of_iterate_eq hper hj hcon')

end Work.LANDCL.ParamAngle
