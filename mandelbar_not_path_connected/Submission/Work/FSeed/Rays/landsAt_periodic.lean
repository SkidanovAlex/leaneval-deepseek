/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# FSeed: `landsAt` depends on the angle only modulo `1`

The ray direction `Work.Landing.rayDirection θ = exp (2πiθ)` satisfies
`rayDirection (θ + n) = rayDirection θ` for every integer `n` (it is a `1`-periodic, indeed
`ℤ`-periodic, map `ℝ → ℂ`).  Consequently so do the radial line `radialRay`, the dynamical ray
`dynRay`, its accumulation set `rayAccum`, and therefore the landing relation
`Work.Landing.landsAt c θ z = ∃ φ, IsDynBottcher c φ ∧ rayAccum c φ θ = {z}`.

## Why this file exists (regression API)

`Submission/Work/NOTES_LEAD_mandelbar_seedsimple.md` §1: the *old* field
`Work.FSeed.LocalRayPortrait.two_rays` quantified over three **real** angles `θ θ' θ''` and
concluded a real equality `θ = θ' ∨ θ = θ'' ∨ θ' = θ''`.  Take `θ = α₁`, `θ' = α₁ + 1`,
`θ'' = α₁ + 2`: the three angles are pairwise distinct reals but, by the lemmas below, they all
land at the same point.  Hence the old bundle `Work.FSeed.RootParabolicInput c` was *false* for
every `c`.  Every counting statement about landing rays must therefore be phrased **modulo `1`**,
i.e. with `Int.fract`, which is what `LocalRayPortrait` now does.

The lemmas below are not needed by `Classify.lean`; they are what makes the mod-`1` statements of
the area usable downstream, and they are the regression test that the vacuity bug cannot return.

## Main results

* `Work.FSeed.rayDirection_add_int`, `radialRay_add_int`, `dynRay_add_int`, `dynRayF_add_int`,
  `rayAccum_add_int` — the definitions are `ℤ`-periodic in the angle;
* `Work.FSeed.landsAt_add_int_iff` — `landsAt c (θ + n) z ↔ landsAt c θ z`;
* `Work.FSeed.landsAt_fract_iff`, `landsAt_fract` — `landsAt c (Int.fract θ) z ↔ landsAt c θ z`;
* `Work.FSeed.landsAt_add_one_iff` — the `n = 1` case, in the form of the refutation;
* `Work.FSeed.landsAt_of_fract_eq` — `landsAt` factors through `Int.fract`;
* `Work.FSeed.coLands_add_int_iff`, `coLands_fract_iff` — the same for `coLands`;
* `Work.FSeed.fract_add_int`, `T_fract` — the angle-map side of the same normalisation.
-/
import Submission.Work.FSeed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function
open scoped Topology

noncomputable section

namespace Work.FSeed

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The definitions are `ℤ`-periodic in the angle -/

/-- `Int.fract` is invariant under translation by an integer.  (Not in this Mathlib under the
name `Int.fract_add_int`, so it is proved here from `Int.fract_eq_fract`.) -/
theorem fract_add_int (θ : ℝ) (n : ℤ) : Int.fract (θ + n) = Int.fract θ :=
  Int.fract_eq_fract.mpr ⟨n, by ring⟩

/-- **The ray direction is `ℤ`-periodic in the angle**: `exp (2πi(θ+n)) = exp (2πiθ)` for every
integer `n` (`Complex.exp_int_mul_two_pi_mul_I`). -/
theorem rayDirection_add_int (θ : ℝ) (n : ℤ) :
    Work.Landing.rayDirection (θ + n) = Work.Landing.rayDirection θ := by
  unfold Work.Landing.rayDirection
  rw [show (↑(2 * Real.pi * (θ + n)) : ℂ) * Complex.I
        = ↑(2 * Real.pi * θ) * Complex.I + ↑n * (2 * ↑Real.pi * Complex.I) by
      push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The radial line of the Böttcher coordinate is `ℤ`-periodic in the angle. -/
theorem radialRay_add_int (θ : ℝ) (n : ℤ) :
    Work.Landing.radialRay (θ + n) = Work.Landing.radialRay θ := by
  unfold Work.Landing.radialRay
  rw [rayDirection_add_int]

/-- The dynamical ray `R_c(θ)` is `ℤ`-periodic in the angle, for *every* Böttcher coordinate
`φ`; no hypothesis on `c` is used. -/
theorem dynRay_add_int (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) (n : ℤ) :
    Work.Landing.dynRay c φ (θ + n) = Work.Landing.dynRay c φ θ := by
  unfold Work.Landing.dynRay
  rw [radialRay_add_int]

/-- The same for the canonical dynamical ray `dynRayF c θ` of the area. -/
theorem dynRayF_add_int (c : ℂ) (θ : ℝ) (n : ℤ) :
    dynRayF c (θ + n) = dynRayF c θ :=
  dynRay_add_int c (Work.ParamRays.dynPhi c) θ n

/-- The accumulation set of a dynamical ray is `ℤ`-periodic in the angle. -/
theorem rayAccum_add_int (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) (n : ℤ) :
    Work.Landing.rayAccum c φ (θ + n) = Work.Landing.rayAccum c φ θ := by
  unfold Work.Landing.rayAccum
  rw [dynRay_add_int]

/-! ## The landing relation is `ℤ`-periodic in the angle -/

/-- **Landing is invariant under translation of the angle by an integer**: the ray at angle
`θ + n` lands at `z` if and only if the ray at angle `θ` does. -/
theorem landsAt_add_int_iff {c z : ℂ} {θ : ℝ} (n : ℤ) :
    Work.Landing.landsAt c (θ + n) z ↔ Work.Landing.landsAt c θ z := by
  unfold Work.Landing.landsAt Work.Landing.RayLands
  simp only [rayAccum_add_int]

/-- **Landing depends on the angle only through `Int.fract`.**  This is the normalised form of
`landsAt`: every ray-count statement of the area is phrased with `Int.fract`. -/
theorem landsAt_fract_iff {c z : ℂ} {θ : ℝ} :
    Work.Landing.landsAt c (Int.fract θ) z ↔ Work.Landing.landsAt c θ z := by
  have h : Int.fract θ = θ + (↑(-⌊θ⌋) : ℝ) := by
    have h2 := Int.fract_add_floor θ
    push_cast
    linarith
  rw [h, landsAt_add_int_iff]

/-- The forward direction of `landsAt_fract_iff`, in the form used to normalise an angle. -/
theorem landsAt_fract {c z : ℂ} {θ : ℝ} (h : Work.Landing.landsAt c θ z) :
    Work.Landing.landsAt c (Int.fract θ) z :=
  landsAt_fract_iff.mpr h

/-- The case `n = 1` of `landsAt_add_int_iff`, in the form in which the vacuity bug of
`NOTES_LEAD_mandelbar_seedsimple.md` §1 was stated: `landsAt c θ z ↔ landsAt c (θ+1) z`. -/
theorem landsAt_add_one_iff {c z : ℂ} {θ : ℝ} :
    Work.Landing.landsAt c (θ + 1) z ↔ Work.Landing.landsAt c θ z := by
  simpa using landsAt_add_int_iff (c := c) (z := z) (θ := θ) (1 : ℤ)

/-- **`landsAt` factors through `Int.fract`**: two angles with the same fractional part give the
same landing relation.  Equivalently, `landsAt c · z` is a function of the class of `θ` in
`ℝ/ℤ`. -/
theorem landsAt_of_fract_eq {c z : ℂ} {θ θ' : ℝ} (h : Int.fract θ = Int.fract θ') :
    (Work.Landing.landsAt c θ z ↔ Work.Landing.landsAt c θ' z) := by
  rw [show θ = Int.fract θ + (⌊θ⌋ : ℝ) from (Int.fract_add_floor θ).symm,
    show θ' = Int.fract θ' + (⌊θ'⌋ : ℝ) from (Int.fract_add_floor θ').symm, h]
  rw [landsAt_add_int_iff, landsAt_add_int_iff]

/-- **Co-landing is invariant under translation of an angle by an integer.** -/
theorem coLands_add_int_iff {c : ℂ} {θ θ' : ℝ} (n : ℤ) :
    Work.Landing.coLands c (θ + n) θ' ↔ Work.Landing.coLands c θ θ' := by
  unfold Work.Landing.coLands
  simp only [landsAt_add_int_iff]

/-- **Co-landing depends on the angle only through `Int.fract`.** -/
theorem coLands_fract_iff {c : ℂ} {θ θ' : ℝ} :
    Work.Landing.coLands c (Int.fract θ) θ' ↔ Work.Landing.coLands c θ θ' := by
  unfold Work.Landing.coLands
  simp only [landsAt_fract_iff]

/-! ## The angle map side -/

/-- The angle map `T θ = -2θ mod 1` of the area depends on `θ` only modulo `1`; this is the
angle-map analogue of `landsAt_fract_iff` and is what makes the mod-`1` portrait statements
compatible with the dynamics. -/
theorem T_fract (θ : ℝ) : T (Int.fract θ) = T θ := by
  unfold T Work.Landing.angDouble
  exact Int.fract_eq_fract.mpr ⟨2 * ⌊θ⌋, by
    have h2 := Int.fract_add_floor θ
    push_cast
    linarith⟩

/-- Iterated form of `T_fract`: every **positive** iterate of the angle map depends on the angle
only modulo `1`.  (The `n = 0` case would read `Int.fract θ = θ`, which is false in general — the
same phenomenon that made the old real-valued portrait clause contradictory.) -/
theorem T_iterate_fract (n : ℕ) (θ : ℝ) : (T^[n + 1]) (Int.fract θ) = (T^[n + 1]) θ := by
  induction n with
  | zero => simpa using T_fract θ
  | succ n ih =>
    show (T^[n + 1 + 1]) (Int.fract θ) = (T^[n + 1 + 1]) θ
    rw [Function.iterate_succ_apply' T (n + 1) (Int.fract θ),
      Function.iterate_succ_apply' T (n + 1) θ, ih]

end Work.FSeed

end
