/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The approximate perturbed Fatou coordinate (lead's design, `NOTES_LEAD_mandelbar_flower.md` §B)

There is no *exact* perturbed Fatou coordinate for the local normal form
`f(ζ) = ζ + (ζ² − a²)h(ζ)` with `a ≠ 0`, and neither the conformal straightening nor
the annulus uniformisation is needed by any consumer.  What the arc-top glue (I1)/(I2)
needs is a coordinate that linearizes the dynamics **to second order**, with a summable
error.

On the set `Nm = {a² < 0}` we have `a = i·λ` (`λ > 0`).  Put

  `approxEcal a κ u = u + κ · log (sinh (a·u) / a)`,     `κ = 1 − h₁`,

where `h ζ = 1 + h₁ ζ + O(ζ²)`.  Since `d/du log (sinh (a u)/a) = ζ(u) = ecalPt a u`
(and the second derivative is `a² − ζ²`), this is the antiderivative correction that
kills the linear term of the displacement:

* `modelDisp_second_order` : `Φ(u) + h(ζ) − ζ·h(ζ)² = O(‖ζ‖² + ‖a‖²)`,
  with **no factor `1/‖a‖`** — the divergence of the naive `log(1+A)` bounds is avoided
  by the integral representation
  `log(1+A₁) − log(1+A₂) = (A₁−A₂)∫₀¹ dt/(1+A_t)`, `A_t = (ζ + (1−2t)a)h`, because
  `∫₀¹ A_t dt = ζh` exactly;
* `approxEcal_step` : on the **transit strip** `R ≤ Re u ≤ π/λ − R`,
  `Ũ(u + Φ(u)) − Ũ(u) + 1 = O(‖ζ(u)‖² + λ²)` — the `κ = 1 − h₁` correction cancels the
  linear part `ζ`;
* `approxEcal_transit` : summing along an orbit that stays in the strip,
  `Ũ(u_n) − Ũ(u₀) + n = O(1/R + λ)` — the per-step errors are summable (`1/|u|²` at the
  two ends of the strip), so the transit error is *uniform in the number of steps*.

Consequences (numerically checked by the lead: with `κ = 1−h₁` the step error decays like
`|ζ|² + λ²`, with the wrong sign it is linear in `ζ`).
-/
import Submission.Work.Implosion.Disp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

open Complex

/-! ## The hypotheses and the coordinate -/

/-- The uniform smallness hypotheses of the implosion chapter, matching the lead's design:
on `‖ζ‖ < r` one has `h ζ = 1 + h₁ ζ + O(ζ²)` with constant `A`, and `‖h‖ ≤ 2`. -/
def ImplosionBounds (h : ℂ → ℂ) (h1 : ℂ) (A r : ℝ) : Prop :=
  (∀ ζ : ℂ, ‖ζ‖ < r → ‖h ζ - 1 - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2) ∧ (∀ ζ : ℂ, ‖ζ‖ < r → ‖h ζ‖ ≤ 2)

/-- The **transit strip** of the Écalle coordinate: the eggeater's body, at distance `R`
from the two ends `u = 0` and `u = π/λ` of the strip of width `π/λ`.  On it the orbit
moves essentially linearly with speed `−1` and takes `≈ π/λ` steps to cross. -/
def transitStrip (lam R : ℝ) : Set ℂ := {u : ℂ | R ≤ u.re ∧ u.re ≤ Real.pi / lam - R}

theorem mem_transitStrip_iff (lam R : ℝ) (u : ℂ) :
    u ∈ transitStrip lam R ↔ R ≤ u.re ∧ u.re ≤ Real.pi / lam - R := Iff.rfl

/-- The **transit regime**: the point is in the transit strip at distance `R ≥ 4` from the
two ends, the Écalle point is uniformly small (`4(‖ζ‖ + λ) ≤ 1`), `‖h‖ ≤ 2`, and the
argument `sinh (a u)/a` of the correction lies in the slit plane.  The smallness of `ζ`
keeps `1 + (ζ ± a)h` in the slit plane, so every `log` of the construction is on the
principal branch with no jump (this is exactly what the naive statement without it
misses at the ends `ζ ≈ ±1`), and `‖h − 1‖ ≤ 1/2` keeps `h` away from `0`, so that one
iterate really is a translation by `−1` rather than a near-fixed-point creep. -/
def GoodTransit (a : ℂ) (h : ℂ → ℂ) (lam R : ℝ) (u : ℂ) : Prop :=
  u ∈ transitStrip lam R ∧ 4 ≤ R ∧ 4 * (‖ecalPt a u‖ + lam) ≤ 1
    ∧ ‖h (ecalPt a u) - 1‖ ≤ 1 / 2 ∧ ‖h (ecalPt a u)‖ ≤ 2
    ∧ Complex.sinh (a * u) / a ∈ Complex.slitPlane

/-- The **approximate perturbed Fatou coordinate**: `Ũ(u) = u + κ·log(sinh(a·u)/a)`.
The correction is an antiderivative of the Écalle point map `ζ(u) = a·coth(a·u)`, so with
`κ = 1 − h₁` it cancels the linear term of the displacement and the dynamics becomes the
translation `u ↦ u − 1` up to `O(‖ζ‖² + λ²)`. -/
noncomputable def approxEcal (a κ u : ℂ) : ℂ :=
  u + κ * Complex.log (Complex.sinh (a * u) / a)

theorem approxEcal_apply (a κ u : ℂ) :
    approxEcal a κ u = u + κ * Complex.log (Complex.sinh (a * u) / a) := rfl

end Work.Implosion
