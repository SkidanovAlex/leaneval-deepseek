import Submission.Work.RPV.Defs

/-!
# Block B of the rectangular-peg route: the Lagrangian family built from a curve

This file is the vocabulary of subproject `Work.RPB` (the `B` block of `RECTPEG_ROUTE_LEAD.md`).
It imports the shared vocabulary `Submission.Work.RPV.Defs` and adds only the notions that the
`B`-nodes (`B1`, `B1'`, `B2`, `B3`, `B4`, `B5`) speak about:

* the chord data of a curve family (`chordVec`, `chordSum`, `halfChord`, `halfChordSum`) and the
  chord annulus `chordSurf` of a planar curve isotopy, whose phase `IsChordPhase` is a smooth lift
  of the argument of the chord direction with its two monodromies;
* the signed area `signedArea` of a closed plane curve and the notion `IsCurveFamily` of a smooth
  isotopy of embedded closed curves (the shape of the hypotheses of `area_pos_of_isotopy`);
* `IsLevelData`: the level coordinates `(ρ, Γ, A)` of the chord annulus near the blown-up diagonal
  `Λ = {r = 0}`, obtained by inverting `s = ρ |g(τ,t,ρ)|²`, extended across the level `Σ₀`;
* `IsCollarData`: the collar `E⁺` above `Σ₀` (level curves `Γ_σ`, phases `A_σ` for `σ ≥ 0`);
* `IsMiddleChart`: the monotone chord reparametrisation `x ↦ r = R τ x t` of the annulus on
  `|x| < √2`, which is `τ_π`-symmetric from the start.

Conventions (fixed once, used by every node of the block).

* `c : ℝ → ℝ → ℂ` is a curve family: `c τ t` is the point of the curve at "time" `τ` and parameter
  `t`; the parameter is `2π`-periodic and the family is `C^∞` in `(τ,t)`.
* The chord annulus is parametrised by `(τ, t, r)` with `0 < r < π`; the two endpoints of the chord
  are `c τ (t + r)` and `c τ (t - r)`. The point in `PS` is `chordSurf c a τ t r`, where `a` is a
  lift of `arg (c τ (t+r) - c τ (t-r))`.
* All angles are real lifts: `a τ (t + 2π) r = a τ t r + 2π` (periodicity of the curve) and
  `a τ (t + π) (π - r) = a τ t r + π` (the chord swap is `τ_π`).
* The level of the chord annulus is `s = K₀ + 1 = r² |halfChord|²`; `s = 0` is the blown-up
  diagonal `Λ`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB

/-! ## B1/B1': curve families and their signed area -/

/-- The signed area `(1/2) ∮ ω_ℂ(c, c')` of a closed plane curve `c`. -/
def signedArea (c : ℝ → ℂ) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..(2 * π), Work.RPV.ωC (c t) (deriv c t)

/-- A smooth `2π`-periodic family of embedded (Jordan) closed plane curves with nonvanishing
derivative, indexed by `τ ∈ [0,1]`. -/
def IsCurveFamily (c : ℝ → ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2) ∧
  (∀ τ t, c τ (t + 2 * π) = c τ t) ∧
  (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', c τ t = c τ t' → ∃ m : ℤ, t' = t + 2 * π * m) ∧
  (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (c τ) t ≠ 0)

/-! ## B2: the chord annulus -/

/-- The chord vector `c τ (t + r) - c τ (t - r)`. -/
def chordVec (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ := c τ (t + r) - c τ (t - r)

/-- The chord sum `c τ (t + r) + c τ (t - r)`. -/
def chordSum (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ := c τ (t + r) + c τ (t - r)

/-- The half chord `(c τ (t + r) - c τ (t - r)) / (2r)`, whose limit at `r = 0` is `c'(t)`. -/
def halfChord (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ := (c τ (t + r) - c τ (t - r)) / (2 * r)

/-- The reduced coordinate `(z + w)/√2` of the chord `(z, w) = (c τ (t+r), c τ (t-r))`. -/
def halfChordSum (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ :=
  (c τ (t + r) + c τ (t - r)) / (Real.sqrt 2 : ℂ)

/-- `IsChordPhase c a`: `a` is a `C^∞` lift of the argument of the chord direction of `c` on the
strip `0 ≤ τ ≤ 1`, `t ∈ ℝ`, `0 < r ≤ π`, together with the two monodromies
`a τ (t + 2π) r = a τ t r + 2π` and `a τ (t + π) (π - r) = a τ t r + π`.

The value at `r = 0` is *not* constrained here: the annulus is only used for `0 < r < π`, and the
junction with the collar is expressed through `IsLevelData`. -/
def IsChordPhase (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) π)
  ∧ (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) π,
      chordVec c τ t r = (‖chordVec c τ t r‖ : ℂ) * Complex.exp (a τ t r * I))
  ∧ (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) π,
      a τ (t + 2 * π) r = a τ t r + 2 * π)
  ∧ (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) π,
      a τ (t + π) (π - r) = a τ t r + π)

/-- The chord annulus of the curve family `c` with phase `a`: the chord `(c τ (t+r), c τ (t-r))`
seen in `PS` through `chordPS`. -/
def chordSurf (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) (τ t r : ℝ) : Work.RPV.PS :=
  Work.RPV.chordPS (c τ (t + r)) (c τ (t - r)) (a τ t r)

/-! ## B3: level coordinates near the blown-up diagonal -/

/-- `IsLevelData c a`: level coordinates of the chord annulus of `c` near the blown-up diagonal
`Λ = {r = 0}` (the level `s = K₀ + 1 = 0`), extended across `Λ` to `s < 0`.

* `ρ τ t s` is the square `r²` of the chord parameter on the level `s = ρ |halfChord|²`;
* `Γ τ t s` is the reduced coordinate `uproj` on that level;
* `A τ t s` is the phase `q₂` on that level.

The data is `C³` in `(τ,t,s)` on `|s| < s₁` (`smρ`/`smΓ`/`smA`) and, additionally, `C⁸` there
(`smρ8`/`smΓ8`/`smA8`).  The `C⁸` fields are what the collar and the assembled `LagFamily` need at
the junction `s = 0`; they are kept *separate* from the `C³` ones so that the already-proved `C³`
consumers keep compiling.  The construction is in fact analytic, so `C⁸` costs nothing.  The data
agrees with the chord annulus for `s ≥ 0`:
on the annulus we have `ρ τ t (r² ‖halfChord c τ t r‖²) = r²`,
`Γ τ t (r² ‖halfChord c τ t r‖²) = halfChordSum c τ t r` and `A … = a τ t r` for `0 < r < r₁`. -/
structure IsLevelData (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) where
  s₁ : ℝ
  hs₁ : 0 < s₁
  s₀ : ℝ
  hs₀ : 0 < s₀
  hs₀s₁ : s₀ ≤ s₁
  r₁ : ℝ
  hr₁ : 0 < r₁
  ρ : ℝ → ℝ → ℝ → ℝ
  Γ : ℝ → ℝ → ℝ → ℂ
  A : ℝ → ℝ → ℝ → ℝ
  smρ : ContDiffOn ℝ 3 (fun z : ℝ × (ℝ × ℝ) => ρ z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-s₁) s₁)
  smΓ : ContDiffOn ℝ 3 (fun z : ℝ × (ℝ × ℝ) => Γ z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-s₁) s₁)
  smA : ContDiffOn ℝ 3 (fun z : ℝ × (ℝ × ℝ) => A z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-s₁) s₁)
  smρ8 : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρ z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-s₁) s₁)
  smΓ8 : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Γ z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-s₁) s₁)
  smA8 : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => A z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-s₁) s₁)
  ρ_zero : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ρ τ t 0 = 0
  small : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioo (0 : ℝ) r₁,
    r ^ 2 * ‖halfChord c τ t r‖ ^ 2 ∈ Set.Ioo (-s₁) s₁
  ρ_eq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioo (0 : ℝ) r₁,
    ρ τ t (r ^ 2 * ‖halfChord c τ t r‖ ^ 2) = r ^ 2
  Γ_eq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioo (0 : ℝ) r₁,
    Γ τ t (r ^ 2 * ‖halfChord c τ t r‖ ^ 2) = halfChordSum c τ t r
  A_eq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioo (0 : ℝ) r₁,
    A τ t (r ^ 2 * ‖halfChord c τ t r‖ ^ 2) = a τ t r
  covers : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ s ∈ Set.Ioo (0 : ℝ) s₀,
    ∃ r ∈ Set.Ioo (0 : ℝ) r₁, s = r ^ 2 * ‖halfChord c τ t r‖ ^ 2

/-! ## B4: the collar above `Σ₀` -/

/-- `IsCollarData c a L`: the collar over the blown-up diagonal.  It is a *globally* smooth family
of level curves `Γ_σ` and phases `A_σ` (for `σ ∈ ℝ`), where

* for `-L.s₀ < σ ≤ 0` it *is* the level data `L` (`Γ τ σ t = L.Γ τ t (-σ)`,
  `A τ σ t = L.A τ t (-σ)`): the parameter `σ = -s` is the negative of the level parameter
  `s = K₀ + 1` of `IsLevelData`, so `σ ≤ 0` is the chord annulus side and `σ ≥ 0` is the collar
  `E⁺` (`K₀ = -1 - σ < -1`);
* for `σ ≥ 0` the surface `(σ,t) ↦ levelPt (Γ τ σ t) σ (A τ σ t)` is Lagrangian
  (`lag`: `∂_t A_σ = ω_ℂ(∂_σ Γ_σ, ∂_t Γ_σ)`), its level curves are embedded, and the area law
  `Area(Γ_σ) = 2π(1+σ)` holds.  The `lag` field is required only for `σ ≥ 0`: on the strip
  `σ ≤ 0` it would be *derivable* from the level data (see below), so requiring it there would add
  nothing but a reproving obligation;
* the far end `σ ≥ σ₂` is the standard circles of the zero section.

**Why `annulusΓ`/`annulusA` range over the strip `-L.s₀ < σ ≤ 0` and not over all of `σ ≤ 0`.**
The level data `L` is only constrained on `|s| < L.s₁`; its values for `s ≥ L.s₁` are arbitrary.
The earlier formulation (`∀ σ, σ ≤ 0 → …`, i.e. `s ≥ 0` unbounded) was therefore *unsatisfiable*:
it was machine-checked (replacing `L.Γ` outside the strip by a wild smooth function gives again an
`IsLevelData` for which no collar exists) and the finding is recorded, with the refuting files that
have since been removed together with the old formulation, in
`Submission/Work/RPB/B4/B4_COLLAR_FALSE_NOTE.md`.  The strip is all the assembly needs.

**Why the covered radius `s₀` is separate from the smoothness radius `s₁`.**  `covers` says that
every level `s ∈ (0, s₀)` is attained, for every `(τ,t)`, as `S(τ,t,r) = r²‖halfChord c τ t r‖²`;
`small` says `S(τ,t,r) < s₁` for all `r ∈ (0,r₁)`.  A single radius for both roles is
*unsatisfiable*: `small` gives `sup_r S(τ,t,·) ≤ s₁` while `covers` up to `s₁` gives
`sup_r S(τ,t,·) ≥ s₁` for *every* `(τ,t)`, forcing `s₁ = sup_r S(τ,t,·)` independent of `(τ,t)` —
false for a non-constant family (machine-checked; the refuting files are recorded in
`Submission/Work/RPB/B3/`).  With two radii the axioms are satisfiable: take `s₁` a smoothness
radius and `s₀` any positive number at most `inf_{(τ,t)} sup_r S(τ,t,·)`, which is positive by
compactness of `[0,1] × S¹` and `S(τ,t,r₁/2) > 0`.  All the level data's *value* axioms are
quantified over `r`, hence over attained levels only, and `covers` is used exactly to pass from an
arbitrary `s ∈ (0,s₀)` to such an `r`.

**Consequences for the builder.**  On `σ ∈ (-L.s₁, 0]` the collar is *determined* by `L`, and
`smΓ : ContDiff ℝ 8` is global, so the collar's `σ > 0` jets at `σ = 0` are thereby forced to equal
those of `L.Γ(-σ)`: that is what makes the assembled `LagFamily` `C⁸` at the junction, with no
separate jet-matching field.  The `σ < 0` slices are the chord annulus, whose Lagrangian condition
is the level-data flux identity for `s > 0` already proved by `Work.RPB.B3.levelData_flux`, so no
new input is demanded there.  The new obligations are all for `σ ≥ 0`: `lag`, `emb`, `area`, and
`nearΓ`/`nearA` at `σ = 0`, with the free `σ > 0` near-field constrained only by the `C⁸`-gluing at
`σ = 0`. -/
structure IsCollarData (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (L : IsLevelData CI.c a) where
  σ₂ : ℝ
  hσ₂ : 0 < σ₂
  Γ : ℝ → ℝ → ℝ → ℂ
  A : ℝ → ℝ → ℝ → ℝ
  smΓ : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Γ z.1 z.2.1 z.2.2)
  smA : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => A z.1 z.2.1 z.2.2)
  annulusΓ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, -L.s₀ < σ → σ ≤ 0 → ∀ t, Γ τ σ t = L.Γ τ t (-σ)
  annulusA : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, -L.s₀ < σ → σ ≤ 0 → ∀ t, A τ σ t = L.A τ t (-σ)
  perΓ : ∀ τ σ t, Γ τ σ (t + 2 * π) = Γ τ σ t
  perA : ∀ τ σ t, A τ σ (t + 2 * π) = A τ σ t + 2 * π
  lag : ∀ τ σ t, 0 ≤ σ → deriv (fun s => A τ σ s) t
    = Work.RPV.ωC (deriv (fun s => Γ τ s t) σ) (deriv (fun s => Γ τ σ s) t)
  emb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, 0 ≤ σ →
    (∀ t, deriv (fun s => Γ τ σ s) t ≠ 0) ∧
      (∀ t t', Γ τ σ t = Γ τ σ t' → ∃ m : ℤ, t' = t + 2 * π * m)
  area : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, 0 ≤ σ → signedArea (Γ τ σ) = 2 * π * (1 + σ)
  nearΓ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, Γ τ 0 t = (Real.sqrt 2 : ℂ) * CI.c τ t
  nearA : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, A τ 0 t = L.A τ t 0
  farΓ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t,
    Γ τ σ₂ t = (Real.sqrt (2 + 2 * σ₂) : ℂ) * Complex.exp ((t - π / 2) * I)
  farA : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, A τ σ₂ t = t

/-! ## B5: the middle chart

The monotone chord reparametrisation `x ↦ r = R τ x t` of the annulus on `|x| < √2` (with the
`τ_π` symmetry `R τ (-x) (t + π) = π - R τ x t` built in from the start) is *not* given a structure
here: it is produced inside the proof of `exists_lagFamily`, where the `π/2` parameter offsets
between the chord chart and the collar chart are fixed consistently. -/

end Work.RPB
