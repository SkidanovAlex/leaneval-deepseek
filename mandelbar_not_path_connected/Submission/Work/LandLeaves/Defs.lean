/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# `LandLeaves` — the landing/`LANDCL` leaf inputs (area of the lead's ledger §5)

This area (`Submission/Work/LandLeaves/`, namespace `Work.LandLeaves`) owns the leaf inputs of
the landing chain that the ledger `Submission/Work/NOTES_LEAD_mandelbar_ledger.md` §5 lists as
still unproved:

| ledger item | statement | where in this area |
|---|---|---|
| 1. rotation number zero (angle defect) | `Work.Landing.RotationNumberZero` repaired to `PeriodicAngle (Int.fract θ) (2k)` | repair in `Work.Landing.RotationNumberZero` itself (Landing/Land.lean), the equivalence and the regression refutation are `rotationNumberZero_iff_Ico`, `not_rotationNumberZero_raw` below |
| 2. `DynBottcherOnlyOnMandelbar` | `IsDynBottcher c φ → c ∈ Mb` | `Submission/Work/LandLeaves/DynBottcherOnlyOnMandelbar.lean`, `.../dynBottcher_preliminaries.lean` |
| 3. `AttractingCyclesInner c` | attracting points have a non-escaping neighbourhood | `Submission/Work/LandLeaves/attractingCyclesInner.lean` |
| 4. `PeriodicRaysLand c` directly | periodic rays land (Milnor 18.10) without local connectivity | `Submission/Work/LandLeaves/periodicRaysLand.lean` (the classical input) plus the reductions `Reductions.lean` |
| 5. `SnailDichotomy` | Snail lemma (general period) | `Submission/Work/LandLeaves/snailDichotomy.lean`, `.../repelling_or_parabolic.lean` |
| 6. `GoldbergMilnorB1` | stability of a landing at a repelling point | `Submission/Work/LandLeaves/goldbergMilnorB1.lean` |

## The vocabulary of the area

* `RayAccumSingleton` — the landing statement in accumulation-set form, i.e. the shape in which
  the *direct* (Milnor 18.10, hyperbolic-metric, no local connectivity) proof delivers the
  theorem; `rayAccumSingleton_iff_periodicRaysLand` proves that this form is equivalent to
  `Work.Landing.PeriodicRaysLand` at parameters which have a Böttcher coordinate, so the
  reductions of `Reductions.lean` can be fed from either formulation.
* `angDouble_iterate_one`, `not_periodicAngle_one`, `not_rotationNumberZero_raw` — the
  machine-checked refutation of the *old* (unnormalised) `RotationNumberZero` of ledger item 1.

## Angle conventions

Everything in the area is phrased **modulo `1`** in the angle: `Work.FSeed.landsAt_add_int_iff`
gives `landsAt c (θ + n) z ↔ landsAt c θ z`, so a landing statement that concludes a property of
the *raw* real `θ` is false for every `θ` outside `[0,1)`.  `RayAccumSingleton` inherits this:
its conclusion is a property of the *accumulation set*, which is `fract`-invariant.

Import one module: `Submission.Work.LandLeaves.All`.
-/
import Submission.Work.FSeed.Rays.landsAt_periodic
import Submission.Work.LANDCL.Defs
import Submission.Work.Landing.Land.Caratheodory

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical

namespace Work.LandLeaves

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Ledger item 1 — the angle normalisation of `RotationNumberZero` -/

/-- **The repaired `Work.Landing.RotationNumberZero` is the old statement on `[0,1)`.**

The old form of the definition (concluding `PeriodicAngle θ (2 * k)` for an arbitrary *real*
angle `θ`) is refuted in `not_rotationNumberZero_raw` below; the repaired definition concludes
`PeriodicAngle (Int.fract θ) (2 * k)`.  On the canonical interval `Set.Ico 0 1` of angles the two
coincide, because `Int.fract θ = θ` there.  In particular the use of the statement at
`θ = 23/63` (ledger item 1, `Work.LANDCL.paramAngleRepelling_quarter`) is unaffected by the
repair: `23/63 ∈ [0,1)`. -/
theorem rotationNumberZero_iff_Ico (c : ℂ) (k : ℕ) :
    Work.Landing.RotationNumberZero c k ↔
      ∀ z : ℂ, Work.Landing.IsParabolic c k z → ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        Work.Landing.landsAt c θ z → Work.Landing.PeriodicAngle θ (2 * k) := by
  constructor
  · intro h z hz θ hθ hland
    have h' := h z hz θ hland
    rwa [Int.fract_eq_self.mpr hθ] at h'
  · intro h z hz θ hland
    -- `h` at the canonical representative `Int.fract θ` gives exactly the goal
    exact h z hz (Int.fract θ) ⟨Int.fract_nonneg θ, Int.fract_lt_one θ⟩
      (Work.FSeed.landsAt_fract_iff.mpr hland)

/-! ## The refutation of the *old* form (regression test)

The old definition quantified over **real** angles and concluded `PeriodicAngle θ (2 * k)`, i.e.
`angDouble^[2*k] θ = θ` with the raw representative.  Since `landsAt` only depends on the angle
modulo `1` (`Work.FSeed.landsAt_add_one_iff`), while `1 ↦ angDouble 1 = 0`, the old statement was
false as soon as *some* ray lands at a parabolic point.  The three lemmas below are the
machine-checked record of that defect. -/

/-- `angDouble 1 = 0`: the angle `1` is the same ray as the angle `0`. -/
@[simp] theorem angDouble_one : Work.Landing.angDouble 1 = 0 := by
  rw [Work.Landing.angDouble]
  norm_num [Int.fract_eq_self]

/-- **The angle `1` is not periodic of any positive period**: `angDouble^[n] 1 = 0` for every
`n ≥ 1`, so `PeriodicAngle 1 n` would read `0 = 1`. -/
theorem angDouble_iterate_one (n : ℕ) : (Work.Landing.angDouble)^[n + 1] (1 : ℝ) = 0 := by
  induction n with
  | zero => simpa using angDouble_one
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [Work.Landing.angDouble]

/-- The raw angle `1` is never periodic. -/
theorem not_periodicAngle_one {n : ℕ} (hn : 0 < n) :
    ¬ Work.Landing.PeriodicAngle (1 : ℝ) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [Work.Landing.PeriodicAngle, angDouble_iterate_one m]
  norm_num

/-- **The old (unnormalised) form of `RotationNumberZero` is false.**  If any parabolic point of
period `k` is the landing point of a dynamic ray (which is the classical situation at the
parabolic parameters used by the route, e.g. `1/2` at `c = 1/4`), then

`∀ z, IsParabolic c k z → ∀ θ, landsAt c θ z → PeriodicAngle θ (2 * k)`

is refuted: `landsAt` is invariant under `θ ↦ θ + 1`, but `1` is not a periodic angle.  This is
the angle-mod-`1` defect recorded in the ledger §5 and in
`Submission/Work/LandLeaves/NOTES_FALSE_RotationNumberZero.md`. -/
theorem not_rotationNumberZero_raw (c : ℂ) (k : ℕ) (hk : 0 < 2 * k)
    (h : ∃ z : ℂ, Work.Landing.IsParabolic c k z ∧ Work.Landing.landsAt c 0 z) :
    ¬ (∀ z : ℂ, Work.Landing.IsParabolic c k z → ∀ θ : ℝ,
        Work.Landing.landsAt c θ z → Work.Landing.PeriodicAngle θ (2 * k)) := by
  rintro hraw
  obtain ⟨z, hz, hland⟩ := h
  have h1 : Work.Landing.landsAt c (1 : ℝ) z := by
    simpa using (Work.FSeed.landsAt_add_one_iff (c := c) (z := z) (θ := 0)).mpr hland
  exact not_periodicAngle_one hk (hraw z hz 1 h1)

/-! ## The landing statement in accumulation-set form (the direct Milnor route) -/

/-- **The landing theorem in accumulation-set form**: for a parameter with a Böttcher coordinate,
the accumulation set (near the Julia set) of every periodic dynamic ray is a *single point*.

This is the shape in which the direct proof of Milnor 18.10 — the hyperbolic metric on
`ℂ ∖ closure (postcritical set)` and the expansion of the inverse branches, *without* local
connectivity of the Julia set — delivers the landing theorem: one shows that the (nonempty,
compact, invariant) accumulation set of a periodic ray cannot contain two distinct points.  It is
equivalent to `Work.Landing.PeriodicRaysLand` at parameters that have a Böttcher coordinate
(`rayAccumSingleton_iff_periodicRaysLand`), by uniqueness of the Böttcher coordinate.

The Böttcher coordinate is universally quantified, so that the statement does not depend on the
choice of coordinate; off the mandelbar `IsDynBottcher` is unsatisfiable
(`Work.LANDCL.DynBottcherOnlyOnMandelbar`) and the statement is vacuous, which is why the clause
`DynBottcherExists c` appears in the equivalence. -/
def RayAccumSingleton (c : ℂ) : Prop :=
  ∀ θ : ℝ, Work.Landing.IsPeriodicAngle θ → ∃ z : ℂ, ∀ φ : ℂ → ℂ,
    Work.ParamRays.IsDynBottcher c φ → Work.Landing.rayAccum c φ θ = {z}

/-- **`RayAccumSingleton` and `PeriodicRaysLand` agree** at every parameter that has a Böttcher
coordinate.  The point is that the accumulation set is the same for every Böttcher coordinate
(`Work.Landing.rayAccum_congr` + `Work.ParamRays.isDynBottcher_unique`), so quantifying over the
coordinate or existentially quantifying it is immaterial. -/
theorem rayAccumSingleton_iff_periodicRaysLand {c : ℂ}
    (h : Work.ParamRays.DynBottcherExists c) :
    RayAccumSingleton c ↔ Work.Landing.PeriodicRaysLand c := by
  constructor
  · intro hS θ hθ
    obtain ⟨z, hz⟩ := hS θ hθ
    obtain ⟨φ₀, hφ₀⟩ := h
    exact ⟨z, φ₀, hφ₀, hz φ₀ hφ₀⟩
  · intro hP θ hθ
    obtain ⟨z, φ, hφ, hz⟩ := hP θ hθ
    refine ⟨z, fun ψ hψ => ?_⟩
    have hcongr : Work.Landing.rayAccum c ψ θ = Work.Landing.rayAccum c φ θ :=
      Work.Landing.rayAccum_congr
        (fun w hw => Work.ParamRays.isDynBottcher_unique hψ hφ hw) θ
    rw [hcongr, hz]

end Work.LandLeaves
