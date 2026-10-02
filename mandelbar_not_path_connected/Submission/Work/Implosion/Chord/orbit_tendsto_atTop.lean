import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Orbits of a continuous map of `ℝ` with `f x > x` diverge to `+∞`

Let `f : ℝ → ℝ` be continuous with `f x > x` for every `x`, and let `a : ℝ`.  Then the orbit
`n ↦ f^[n] a` is nondecreasing and unbounded above, hence tends to `+∞`.

The unboundedness argument is by contradiction.  A monotone bounded orbit converges to
`L = ⨆ n, f^[n] a`; since `f (f^[n] a) = f^[n+1] a`, the shifted orbit also converges to `L`, while
continuity gives that `f (f^[n] a)` converges to `f L`.  Hence `f L = L`, contradicting `L < f L`.

(The strict monotonicity hypothesis `hmono` is not needed for this conclusion; it is retained
because it is part of the requested statement.)
-/

open Filter Set Function
open scoped Topology

namespace Work.Implosion.Chord

theorem orbit_tendsto_atTop (f : ℝ → ℝ) (hcont : Continuous f) (hmono : StrictMono f)
    (hgt : ∀ x : ℝ, x < f x) (a : ℝ) :
    Filter.Tendsto (fun n : ℕ => f^[n] a) Filter.atTop Filter.atTop := by
  have _ : StrictMono f := hmono
  set u : ℕ → ℝ := fun n => f^[n] a with hu_def
  -- the orbit is nondecreasing
  have hmono_u : Monotone u := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [hu_def, Function.iterate_succ_apply']
    exact (hgt (f^[n] a)).le
  -- and it is unbounded above
  have hnotbdd : ¬ BddAbove (range u) := by
    intro hbdd
    have hu : Tendsto u atTop (𝓝 (⨆ n, u n)) := tendsto_atTop_ciSup hmono_u hbdd
    have hsucc : Tendsto (fun n => u (n + 1)) atTop (𝓝 (⨆ n, u n)) :=
      hu.comp (tendsto_add_atTop_nat 1)
    have hcomp : Tendsto (fun n => f (u n)) atTop (𝓝 (f (⨆ n, u n))) :=
      (hcont.tendsto (⨆ n, u n)).comp hu
    have heq : (fun n => f (u n)) = fun n => u (n + 1) := by
      funext n
      simp only [hu_def, Function.iterate_succ_apply']
    rw [heq] at hcomp
    have hfix : f (⨆ n, u n) = ⨆ n, u n := tendsto_nhds_unique hcomp hsucc
    exact (hgt (⨆ n, u n)).ne' hfix
  exact tendsto_atTop_atTop_of_monotone' hmono_u hnotbdd

end Work.Implosion.Chord
