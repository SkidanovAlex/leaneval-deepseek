/-
# Böttcher coordinates for the tricorn (BOT-2)

Definitions for the `Work.Bottcher` chapter of the `mandelbar_not_path_connected`
project.  For the anti-holomorphic degree-2 ("tricorn") family

`T_c(z) = conj z ^ 2 + c`

we set up

*  the Green function `G_c` (imported from the sibling chapter `Work.Escape`,
   single source of truth: `Escape.green`), re-exported here as `green c z`, and
   its critical value `greenParam c = G_c(0)`;
*  the holomorphic *second iterate* `p_c = pMap c = T_c ∘ T_c`, a monic quartic;
*  the Böttcher coordinate `bottcher c` on the domain
   `CritDomain c = {z | G_c z > G_c 0}` with the product formula
   `φ_c(z) = z ∏_n (p_c^n z / (p_c^n z)^4)^{4^{-(n+1)}}`;
*  the parameter Böttcher coordinate `Phi c = φ_c(c)`;
*  dynamic rays `dynamicRay c θ` and the angle-doubling map `θ ↦ -2θ`.

Conventions (see `NOTES.md`).
*  An *angle* is a real number (in turns); the ray at angle `θ` is the radial ray
   in direction `rayDirection θ = exp(2 π i θ)`; `dynamicRay` is periodic with
   period `1` in `θ`.
*  `bottcher` is a *total* function (defined through a `tsum`), and every theorem
   about it carries the hypothesis `z ∈ CritDomain c`.  This is exactly the
   regime in which the product formula is the true Böttcher coordinate: it is the
   largest domain uniformly in `c` on which the formula has no degenerate factor.
*  `M*` denotes `LeanEval.ComplexAnalysis.Mandelbar`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Escape.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Green function (re-exported from `Work.Escape`) -/

/-- The Green function `G_c(z)` of the tricorn map, re-exported from the
`Work.Escape` chapter (`Escape.green (Tantibar c) 2 z`). -/
noncomputable abbrev green (c z : ℂ) : ℝ := Work.Escape.green (Tantibar c) 2 z

/-- The potential `G_c(0)` of the critical point (the critical value of the Green
function); `c ∉ M*` iff `0 < greenParam c`. -/
noncomputable abbrev greenParam (c : ℂ) : ℝ := Work.Escape.greenParam c

theorem green_def (c z : ℂ) : green c z = Work.Escape.green (Tantibar c) 2 z := rfl

theorem greenParam_def (c : ℂ) : greenParam c = green c 0 := rfl

/-- The **escape set** (basin of infinity) `{G_c > 0}`. -/
def EscapeSet (c : ℂ) : Set ℂ := {z | 0 < green c z}

/-- The domain `{G_c > G_c(0)}` on which the Böttcher coordinate is the true one.
It contains the critical value `c` exactly when `c ∉ M*`. -/
def CritDomain (c : ℂ) : Set ℂ := {z | greenParam c < green c z}

theorem mem_CritDomain {c z : ℂ} : z ∈ CritDomain c ↔ greenParam c < green c z := Iff.rfl

theorem mem_EscapeSet {c z : ℂ} : z ∈ EscapeSet c ↔ 0 < green c z := Iff.rfl

/-! ## The holomorphic second iterate -/

/-- The holomorphic *second iterate* `p_c = T_c ∘ T_c` of the tricorn map, i.e.
`p_c(z) = (z^2 + conj c)^2 + c`; a monic polynomial of degree `4`. -/
noncomputable def pMap (c : ℂ) : ℂ → ℂ := fun z => (z ^ 2 + conj c) ^ 2 + c

theorem pMap_apply (c z : ℂ) : pMap c z = (z ^ 2 + conj c) ^ 2 + c := rfl

theorem Tantibar_zero (c : ℂ) : Tantibar c 0 = c := by simp [Tantibar]

/-- `p_c` is the second iterate of `T_c` (as a function). -/
theorem pMap_eq_iterate_two (c : ℂ) : pMap c = (Tantibar c)^[2] := by
  funext z
  simp [pMap, Tantibar, map_add, map_pow, Function.iterate_succ_apply']

/-- For every `n`, the `n`-th iterate of `p_c` is the `2n`-th iterate of `T_c`. -/
theorem pMap_iterate (c z : ℂ) (n : ℕ) :
    (pMap c)^[n] z = (Tantibar c)^[2 * n] z := by
  rw [pMap_eq_iterate_two, Function.iterate_mul]

/-- `T_c` applied to the `n`-th `p_c`-iterate is the `(2n+1)`-st `T_c`-iterate. -/
theorem Tantibar_iterate_pMap (c z : ℂ) (n : ℕ) :
    Tantibar c ((pMap c)^[n] z) = (Tantibar c)^[2 * n + 1] z := by
  rw [pMap_iterate, show 2 * n + 1 = Nat.succ (2 * n) by omega,
    Function.iterate_succ_apply']

/-- The orbits of `z` and of `p_c z` are related by `T_c`. -/
theorem pMap_iterate_Tantibar (c z : ℂ) (n : ℕ) :
    (pMap c)^[n] (Tantibar c z) = Tantibar c ((pMap c)^[n] z) := by
  rw [pMap_iterate, pMap_iterate,
    ← Function.iterate_succ_apply (f := Tantibar c) (n := 2 * n) (x := z),
    ← Function.iterate_succ_apply' (f := Tantibar c) (n := 2 * n) (x := z)]

/-! ## The escape radius of the family -/

/-- A convenient escape radius for the tricorn family: for `‖z‖ ≥ escapeRadius c`
the norm of the `T_c`-image at least doubles, and the second iterate at least
squares it. -/
noncomputable def escapeRadius (c : ℂ) : ℝ := 2 * (1 + ‖c‖)

/-! ## Böttcher coordinate -/

/-- The set of points whose `p_c`-orbit avoids the critical point `0`; on this set
the product formula for the Böttcher coordinate has no degenerate factors. -/
def AvoidsCriticalOrbit (c : ℂ) : Set ℂ := {z | ∀ n : ℕ, (pMap c)^[n] z ≠ 0}

/-- The normalised factor `p_c(z)/z^4 = 1 + O(1/z^2)` of the Böttcher product.
At `z = 0` this is `0` (totalised division); all theorems assume `z` in
`CritDomain c`, which is contained in `AvoidsCriticalOrbit c`. -/
noncomputable def normFactor (c z : ℂ) : ℂ := pMap c z / z ^ 4

/-- The `n`-th term of the Böttcher series. -/
noncomputable def bottcherTerm (c : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ((1 / 4 : ℝ) ^ (n + 1) : ℂ) * Complex.log (normFactor c ((pMap c)^[n] z))

/-- The Böttcher series `Σ_n 4^{-(n+1)} log (p_c(z_n)/z_n^4)`, `z_n = p_c^n z`. -/
noncomputable def bottcherSeries (c z : ℂ) : ℂ := ∑' n : ℕ, bottcherTerm c n z

/-- Partial products of the Böttcher product formula. -/
noncomputable def bottcherPartial (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  z * Complex.exp (∑ n ∈ Finset.range N, bottcherTerm c n z)

/-- The **Böttcher coordinate of the product formula** for the tricorn map at
parameter `c`:

`bottcher c z = z ∏_n (p_c^n z / (p_c^n z)^4)^{4^{-(n+1)}}`, `p_c = T_c ∘ T_c`,

i.e. `bottcher c z = z * exp (bottcherSeries c z)`.

## What is proved about it

* `bottcher_comm_pMap` : `φ ∘ p_c = φ^4` (the Böttcher equation for the
  holomorphic quartic `p_c = T_c^2`), on the escaping set;
* `norm_bottcher_domain` / `norm_bottcher_eq_exp_green` : `‖φ_c z‖ = exp (G_c z)`;
* `bottcher_tendsto_atTop` : `φ_c z / z → 1` (tangency at infinity);
* `analyticAt_bottcher` : `φ_c` is analytic off `{‖z‖ < escapeRadius c}`.

## Warning (branch defect of the product formula)

`Complex.log` is not additive, so on the locus where a factor
`p_c^n z / (p_c^n z)^4` crosses the negative real axis the series jumps by an
accumulated multiple of `2πi` which need not be an integer multiple of `2πi`.
Consequently the product formula agrees with the (analytic) Böttcher coordinate
of `T_c` only up to a locally constant factor with values in the roots of unity
of `2`-power order; see `Work.Bottcher.Core.ProductFormulaTelescoping` for a
machine-checked counterexample to `φ (T_c z) = conj (φ z)^2` outside the
far region.

The Böttcher equation `φ ∘ T_c = conj ∘ φ^2` is nevertheless **proved** on the
branch-consistent far region `{z : escapeRadius c ≤ ‖z‖}`:
`Work.Bottcher.Core.bottcher_comm_Tantibar_far`.  On that region the product
formula *is* the analytic Böttcher coordinate
(`Work.Bottcher.Core.eq_bottcher_of_analytic`).  For the parts of the escape set
outside the far region one must use the analytic Böttcher coordinate supplied
classically, e.g. by `Work.ParamRays.IsDynBottcher` /
`Work.ParamRays.BottcherExists`. -/
noncomputable def bottcher (c z : ℂ) : ℂ := z * Complex.exp (bottcherSeries c z)

/-! ## Rays and equipotentials -/

/-- The point of the unit circle at angle `θ` (measured in turns). -/
noncomputable def rayDirection (θ : ℝ) : ℂ := Complex.exp ((2 * Real.pi * θ : ℝ) * Complex.I)

theorem rayDirection_add_one (θ : ℝ) : rayDirection (θ + 1) = rayDirection θ := by
  have h2 : Complex.exp ((2 * Real.pi : ℂ) * Complex.I) = 1 := by
    simpa using Complex.exp_two_pi_mul_I
  have h : ((2 * Real.pi * (θ + 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  simp only [rayDirection, h, Complex.exp_add, h2, mul_one]

/-- The **parameter Böttcher coordinate** `Φ(c) = φ_c(c)`: the Böttcher coordinate
evaluated at the critical value `c`, set to the junk value `0` on the mandelbar
`M*` (where the critical orbit does not escape).  For `c ∉ M*` this is Nakane's
real-analytic diffeomorphism `ℂ \ M* → ℂ \ D̄` (see `Phi_eq_bottcher`,
`norm_Phi_eq_exp_green`, `Phi_eq_zero_of_mem_mandelbar`). -/
noncomputable def Phi (c : ℂ) : ℂ := by
  classical
  exact if c ∈ Mandelbar then 0 else bottcher c c

theorem Phi_eq_bottcher {c : ℂ} (hc : c ∉ Mandelbar) : Phi c = bottcher c c := by
  classical
  simp [Phi, hc]

theorem Phi_eq_zero_of_mem_mandelbar {c : ℂ} (hc : c ∈ Mandelbar) : Phi c = 0 := by
  classical
  simp [Phi, hc]

/-- The **potential** of the parameter `c`: `log ‖Φ(c)‖`.  This is `0` exactly on
the mandelbar (`‖Φ c‖ = 0` there, and `Real.log 0 = 0` is the totalised
convention); for `c ∉ M*` it equals `green c c = 2 * greenParam c`, the Green
function of the critical value. -/
noncomputable def potential (c : ℂ) : ℝ := by
  classical
  exact if c ∈ Mandelbar then 0 else Real.log ‖Phi c‖

/-- The **external angle** of an escaping parameter: `arg (Φ c) / 2π`, normalised
to `[0, 1)`. -/
noncomputable def extAngle (c : ℂ) : ℝ :=
  toIcoMod one_pos 0 (Complex.arg (Phi c) / (2 * Real.pi))

/-- The **parameter ray** `R(θ)`: the parameters outside the mandelbar whose
Böttcher coordinate lies on the radial ray of direction `rayDirection θ`, outside
the unit circle.  For `c ∉ M*`, `c ∈ R(θ)` iff the critical value lies on the
*dynamic* ray `R_c(θ)`. -/
def paramRay (θ : ℝ) : Set ℂ :=
  {c | c ∉ Mandelbar ∧ ∃ r : ℝ, 1 < r ∧ Phi c = (r : ℂ) * rayDirection θ}

/-- The **parameter equipotential** `{c ∉ M* : ‖Φ c‖ = R}`. -/
def paramEquipotential (R : ℝ) : Set ℂ := {c | c ∉ Mandelbar ∧ ‖Phi c‖ = R}

/-- The **parameter equipotential arc** of level `R` between the angles `β₁ ≤ β₂`:
the `Φ`-preimage of the closed circular arc of radius `R` between the directions
`rayDirection β₁` and `rayDirection β₂` (counterclockwise).  This is the
"equipotential arc" used in the endgame of the non-path-connectedness proof. -/
def paramEquipotentialArc (R β₁ β₂ : ℝ) : Set ℂ :=
  {c | c ∉ Mandelbar ∧ ‖Phi c‖ = R ∧ extAngle c ∈ Set.Icc β₁ β₂}

/-- The **dynamic ray of angle `θ` for an arbitrary Böttcher coordinate** `φ`:
the set of points whose `φ`-value lies on the radial ray of direction
`rayDirection θ` outside the unit circle.  This is the form in which the
angle-doubling rule is stated and proved
(`Tantibar_maps_dynamicRayOf`): any `φ` satisfying `φ ∘ T_c = conj ∘ φ^2` sends
`R_φ(θ)` into `R_φ(-2θ)`. -/
def dynamicRayOf (φ : ℂ → ℂ) (θ : ℝ) : Set ℂ :=
  {z | ∃ r : ℝ, 1 < r ∧ φ z = (r : ℂ) * rayDirection θ}

/-- The **dynamic equipotential** of level `lam` of the tricorn map: the level set
`{z : G_c(z) = lam}` of the Green function. -/
def dynamicEquipotential (c : ℂ) (lam : ℝ) : Set ℂ := {z | green c z = lam}

/-- The **dynamic ray** `R_c(θ)` of angle `θ`: the points of `CritDomain c` whose
Böttcher coordinate lies on the radial ray of direction `rayDirection θ` outside
the unit circle.

For `c ∈ M*` we have `CritDomain c = EscapeSet c` (the whole basin of infinity),
so this is the classical dynamic ray; for `c ∉ M*` it is the part of the ray in
`{G_c > G_c(0)}`.  In particular the critical value of an escaping parameter `c`
lies on `R_c(θ)` exactly when `c ∈ R(θ)` (`paramRay`). -/
def dynamicRay (c : ℂ) (θ : ℝ) : Set ℂ :=
  {z | z ∈ CritDomain c ∧ ∃ r : ℝ, 1 < r ∧ bottcher c z = (r : ℂ) * rayDirection θ}

/-- The **angle-doubling map** of the antiholomorphic tricorn family: `θ ↦ -2θ`.
It is the action of `T_c` on dynamic-ray angles (`Tantibar_maps_dynamicRay`). -/
noncomputable def angleDouble (θ : ℝ) : ℝ := -2 * θ

@[simp] theorem angleDouble_apply (θ : ℝ) : angleDouble θ = -2 * θ := rfl

end Work.Bottcher
