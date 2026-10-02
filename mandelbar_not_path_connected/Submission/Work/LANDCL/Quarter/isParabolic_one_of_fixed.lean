import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.Quarter

/-- **A parabolic point of any odd period that is already fixed by `T_c` is parabolic of
period `1`.**

If `z` is fixed by `T_c` and `z` is parabolic of period `m` — i.e. `(T_c)^[m] z = z` and the
multiplier of the holomorphic second return map `(T_c)^{2m} = (Tsq c)^[m]` at `z` is `1` — then
also `multiplier2 c 1 z = 1`.

The mathematics: since `z` is fixed by `T_c`, it is fixed by `Tsq c = (T_c)^2`, so the chain rule
computes `multiplier2 c m z = (multiplier2 c 1 z)^m`; the hypothesis gives `(multiplier2 c 1 z)^m
= 1`.  On the other hand `multiplier2 c 1 z = deriv (Tsq c) z` is a *non-negative real*
(`Work.Landing.Family.deriv_tsq_iterate_odd_real`, applied at the odd period `1`), and a
non-negative real whose `m`-th power is `1` (`m > 0`) equals `1`.

This is exactly why on the boundary of a hyperbolic component of odd period the parabolic
points of the fixed-point (= period `1`) component are the fixed points: the multiplier cannot be
a root of unity other than `1`. -/
theorem isParabolic_one_of_fixed {c z : ℂ} {m : ℕ}
    (hz : LeanEval.ComplexAnalysis.Tantibar c z = z) (h : Work.Landing.IsParabolic c m z) :
    Work.Landing.IsParabolic c 1 z := by
  obtain ⟨⟨hmpos, _hmper⟩, hmult⟩ := h
  -- `z` is fixed by the holomorphic second return map `Tsq c`.
  have hTsz : Work.Landing.Tsq c z = z := by
    have hcomp : Work.Landing.Tsq c z = LeanEval.ComplexAnalysis.Tantibar c
        (LeanEval.ComplexAnalysis.Tantibar c z) := by
      simp only [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, starRingEnd_apply,
        star_add, star_pow, star_star]
    rw [hcomp, hz, hz]
  -- Chain rule at a fixed point: `multiplier2 c m z = (multiplier2 c 1 z)^m`.
  have hmult1 : Work.Landing.multiplier2 c m z = (Work.Landing.multiplier2 c 1 z) ^ m := by
    have hdf := Work.FSeed.API.deriv_iterate_fixed (g := Work.Landing.Tsq c)
      (Work.FSeed.differentiable_Tsq c) hTsz m
    simpa [Work.Landing.multiplier2, Function.iterate_one] using hdf
  have hpow : (Work.Landing.multiplier2 c 1 z) ^ m = 1 := by
    rw [← hmult1]; exact hmult
  -- `multiplier2 c 1 z` is a non-negative real.
  obtain ⟨r, hr0, hr⟩ := Work.Landing.Family.deriv_tsq_iterate_odd_real c
    (show Odd 1 by decide) (by simpa [Function.iterate_one] using hz)
  have hd : Work.Landing.multiplier2 c 1 z = (r : ℂ) := by
    simpa [Work.Landing.multiplier2, Function.iterate_one] using hr
  have hrpow : (r : ℂ) ^ m = 1 := by rw [← hd]; exact hpow
  have hrpow' : r ^ m = 1 := by
    have hcast : (r : ℂ) ^ m = ((r ^ m : ℝ) : ℂ) := by push_cast; ring
    rw [hcast] at hrpow
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from Complex.ofReal_one.symm] at hrpow
    exact Complex.ofReal_inj.mp hrpow
  have hr1 : r = 1 := (pow_eq_one_iff_of_nonneg hr0 (Nat.pos_iff_ne_zero.mp hmpos)).mp hrpow'
  have hfinal : Work.Landing.multiplier2 c 1 z = 1 := by rw [hd, hr1]; norm_num
  exact ⟨⟨by norm_num, by simpa [Function.iterate_one] using hz⟩, hfinal⟩

end Work.LANDCL.Quarter
