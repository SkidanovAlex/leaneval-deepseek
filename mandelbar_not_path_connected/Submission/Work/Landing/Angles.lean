import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Angle doubling for the tricorn family

External rays of `T_c` are labelled by angles `θ ∈ ℝ/ℤ`; since the Böttcher coordinate
satisfies `φ_c(T_c z) = conj(φ_c z)²`, the map `T_c` sends the ray at angle `θ` to the ray at
angle `-2θ`.  We normalise angles to the half-open interval `[0,1)` using `Int.fract`, so the
angle-doubling map is

`angDouble θ = Int.fract (-2θ)`,   i.e.   `angDouble θ = (-2θ) mod 1`.

Since `T_c` is antiholomorphic, the *second* iterate `Tsq c` acts on angles by `θ ↦ 4θ mod 1`;
the *first return map* on the angles of a period-`k` orbit of the multicorn is therefore
`angDouble^[k]`, which for odd `k` acts as `θ ↦ (-2)^k θ = -2^k θ mod 1`.

## The angles used by the current route of the tricorn proof

The umbilical-cord obstruction sits on the **root arc** of the non-real period-`5` hyperbolic
component `H` (HS Fig. 3 and 6; see `NOTES_LEAD_mandelbar_arc_top.md` §0 and §2):

* `rootAngle1 = 371/1023` and `rootAngle2 = 404/1023` are the two **dynamic root angles** of the
  period-`5` orbit.  Both are periodic of period `10` under `angDouble`, and
  `angDouble^[5] rootAngle1 = rootAngle2`, `angDouble^[5] rootAngle2 = rootAngle1`: the first
  return map exchanges the two rays landing at the dynamic root.  They also occur as the angles
  of two of the four parameter rays accumulating at `∂H`.
* `paramAngle = 23/63` is periodic of period `6` under `angDouble`
  (`23 → 17 → 29 → 5 → 53 → 20 → 23`).  Since `6 ∤ 10`, a ray at this angle cannot land at a
  parabolic point of the period-`5` orbit whose second-return multiplier is `1`, so it lands at a
  *repelling* periodic point (Milnor 18.10 + rotation number zero); this is the ray `R(23/63)`
  used in the endgame as the ray through the "window" between the two root angles.
* `windowEps = 1/2048`: the two windows `rootAngle1 ± windowEps` and `rootAngle2 ± windowEps` are
  disjoint and separated by `paramAngle` (`window_separation`).

The two **co-root angles** `coRootAngle1 = 12/33`, `coRootAngle2 = 13/33` (period `5`, see HS
Fig. 1/7) are recorded for reference; the current route does not use them.
-/

noncomputable section

namespace Work.Landing

open Function

/-- Angle doubling for the antiholomorphic quadratic family: `θ ↦ -2θ mod 1`, in the
normalisation `[0,1)`. -/
def angDouble (θ : ℝ) : ℝ := Int.fract (-2 * θ)

@[simp]
theorem angDouble_def (θ : ℝ) : angDouble θ = Int.fract (-2 * θ) := rfl

/-- `θ` is periodic of period `n` under angle doubling. -/
def PeriodicAngle (θ : ℝ) (n : ℕ) : Prop := angDouble^[n] θ = θ

/-- `θ` is a periodic angle. -/
def IsPeriodicAngle (θ : ℝ) : Prop := ∃ n : ℕ, 0 < n ∧ PeriodicAngle θ n

/-- `θ` has exact period `n` under angle doubling. -/
def ExactPeriodAngle (θ : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ PeriodicAngle θ n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ PeriodicAngle θ m

/-- Angle doubling on **rational** angles, used by the Écalle-pullback certificate
(`angDouble_coe_rat` relates it to `angDouble` on `ℝ`). -/
def angDoubleQ (q : ℚ) : ℚ := Int.fract (-2 * q)

/-- The forward orbit of an angle under angle doubling. -/
def angleOrbit (θ : ℝ) : Set ℝ := {θ' : ℝ | ∃ n : ℕ, angDouble^[n] θ = θ'}

/-- The open cyclic interval from `a` to `c` (both in `[0,1)`): the interval `(a,c)` if `a < c`
and `(a,1) ∪ (0,c)` otherwise. -/
def CyclicIoo (a c : ℝ) : Set ℝ := if a < c then Set.Ioo a c else Set.Ioo a 1 ∪ Set.Ioo 0 c

/-- The first dynamic root angle `371/1023` of the non-real period-`5` component. -/
def rootAngle1 : ℝ := 371 / 1023

/-- The second dynamic root angle `404/1023` of the non-real period-`5` component. -/
def rootAngle2 : ℝ := 404 / 1023

/-- The angle `23/63`, periodic of period `6`, of the parameter ray used in the endgame. -/
def paramAngle : ℝ := 23 / 63

/-- The width `1/2048` of the two windows around the root angles used in the endgame. -/
def windowEps : ℝ := 1 / 2048

/-- The five **lifted arcs** `W_j` of the L-wake condition (`NOTES_LEAD_mandelbar_EL_F_contracts.md`
§6): the successive images of the root-ray pair `{371, 404}/1023` under the lifted doubling map
`θ ↦ -2θ` (the lift chosen so that the arc stays adjacent to the sector of the critical orbit).
Their widths are `33·2^j / 1023`, i.e. `33, 66, 132, 264, 528` over `1023`. -/
def wakeArc (j : ℕ) : ℝ × ℝ :=
  match j % 5 with
  | 0 => (371 / 1023, 404 / 1023)
  | 1 => (215 / 1023, 281 / 1023)
  | 2 => (461 / 1023, 593 / 1023)
  | 3 => (860 / 1023, 1124 / 1023)
  | _ => (821 / 1023, 1349 / 1023)

/-- The first dynamic co-root angle `12/33` of the non-real period-`5` component (not used by the
current route). -/
def coRootAngle1 : ℝ := 12 / 33

/-- The second dynamic co-root angle `13/33` of the non-real period-`5` component (not used by
the current route). -/
def coRootAngle2 : ℝ := 13 / 33

/-- The angle `1004/1023` of the fourth parameter ray accumulating at the non-real period-`5`
component (HS Fig. 1). -/
def paramAngle4 : ℝ := 1004 / 1023

@[simp] theorem rootAngle1_def : rootAngle1 = 371 / 1023 := rfl
@[simp] theorem rootAngle2_def : rootAngle2 = 404 / 1023 := rfl
@[simp] theorem paramAngle_def : paramAngle = 23 / 63 := rfl
@[simp] theorem windowEps_def : windowEps = 1 / 2048 := rfl
@[simp] theorem coRootAngle1_def : coRootAngle1 = 12 / 33 := rfl
@[simp] theorem coRootAngle2_def : coRootAngle2 = 13 / 33 := rfl
@[simp] theorem paramAngle4_def : paramAngle4 = 1004 / 1023 := rfl

end Work.Landing
