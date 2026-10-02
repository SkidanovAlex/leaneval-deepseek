/-
# GATE2 — the sibling inputs out of which the exit path is built (the design's D1)

`Work.GATE2.ExitPathData` (`Submission/Work/GATE2/ExitPath.lean`) is the single residual interface
through which residual 2 of the gate is delivered.  The design
`NOTES_LEAD_mandelbar_gate2transport.md` §4–§6 builds that datum — for a tongue parameter `e` near
`c₀`, the path

    σ := [e → c₀] ⋆ ψ (v + λ − (u₀ − 1)) ⋆ [c₁ → F_e e]

— from three sibling statements, named here so that the lead can wire them:

* **PL** (`Work.GATE2.PrincipalParam`, design §4.1): the principal Fatou parametrisation `ψ` of the
  `c₀`-flower on the slit plane `ℂ \ (−∞, v − 1/2]`, with `ψ v = c₀`, equivariant for `F₀` (shift
  by `1`) and for the antiholomorphic root `g₀ = (T_{c₀})^5` (the `ι`-symmetry).  Built by half-step
  lifts through `g₀` plus Liouville; its only critical value in the basin is `c₀`.
* **EXL** (`Work.GATE2.ExitLoop`, design §4.2): the `α`-window exit loop at `c₀`, off `K c₀`,
  inside a compact `𝒦` on which the `α`-deviation is `< 1/16384`, with potential at least
  `(3/4)·G(Ψ(u−1))` along it and the offset-avoidance condition (W).  **Plus the confinement of the
  loops**: the loops have a uniformly bounded range and lie in `{Re < −1}` (`K₀` below).  This is
  *not* decoration: `Work.PARIMPL.TransitLockstep` is instantiated *before* `e`, with a fixed box
  `[X₁, X₁+W] × {|Im| ≤ H}` and a fixed window `[−Xo, −1)`, so the construction of D1 needs the
  levels `v + N₀ + δ t` of the loops to be bounded in both coordinates and below `−1`.  The design
  notes (`Submission/Work/GATE2/PL/NOTES_D1_gap.md` §4) assume exactly this; PL's `bounded_gap`
  note shows the confinement is unavoidable.  (The `ρ`-max construction of
  `NOTES_LEAD_mandelbar_gaps2.md` §4 produces `K₀` for free.)
* **UT** (PARIMPL, design §5): `Work.PARIMPL.TransitData.UT`, already a *field* of PARIMPL's
  transit data — the uniform lock-step transit of every point of a bounded box of the attracting
  coordinate.  D1 needs it with a **caller-prescribed floor** `X₁ ≥ Xb` on the box
  (`Work.GATE2.TransitLockstepAbove`): the box produced by UT must reach above the threshold `X` of
  PL's `PrincipalParam.far`, since that is the region in which `ψ` is the inverse Fatou coordinate.
  (`TransitLockstepAbove . Xb v → TransitLockstep . v`; UT is the floor-free form.)

plus the uniform-continuity bookkeeping of the design's D1 (NAKANE's `continuous_greenFun`,
`Work.GATE2.deviation_continuousAt`, `Work.PARIMPL.continuous_tsqIter`).

This module states the two structures (PL and EXL) exactly as the design does, so that the residual
of the area is *named* and can be handed to the sibling owners.  `Work.GATE2.ExitPathData` is a
theorem away from them (the design's D1), and nothing below asserts that D1 has been carried out.
-/
import Submission.Work.GATE2.Escape
import Submission.Work.PARIMPL.Transit
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The slit plane** `Ω_v = ℂ \ (−∞, v − 1/2]`: the plane cut along the real half-line
`(−∞, v − 1/2]`.  This is the natural domain of the principal Fatou parametrisation of the
`c₀`-flower: the cut contains the branch offsets `−1/2 − n/2` reflected through `v`. -/
def slitAt (v : ℝ) : Set ℂ := {w : ℂ | ¬ (w.im = 0 ∧ w.re ≤ v - 1 / 2)}

/-- **PL — the principal Fatou parametrisation passes through the critical value** (design §4.1).

`ψ` is continuous on the slit plane `Ω_v`, maps `v` to the critical value `c₀`, and intertwines
`F (= (T_{c₀})^{10})` with the shift `w ↦ w + 1` and the antiholomorphic square root
`g = (T_{c₀})^5` with the `ι`-symmetry `w ↦ w̄ + 1/2`.  Far to the right it is the (local) inverse
of the attracting Fatou coordinate `φa` of the flower on the invariant sub-petal `Pg`.

The data `ψ`, `X` are fields (the statement is a structure, not a `Prop`), so a caller
supplies them by `refine ⟨_, _⟩` or by `obtain`. -/
structure PrincipalParam (F g : ℂ → ℂ) (c₀ : ℂ) (Pg : Set ℂ) (φa : ℂ → ℂ) (v : ℝ) where
  /-- the parametrisation. -/
  ψ : ℂ → ℂ
  /-- the threshold beyond which `ψ` is the inverse of the Fatou coordinate. -/
  X : ℝ
  /-- `ψ` is continuous on the slit plane. -/
  cont : ContinuousOn ψ (slitAt v)
  /-- `ψ` passes through the critical value. -/
  ψv : ψ v = c₀
  /-- `ψ` intertwines `F` with the unit shift. -/
  shift : ∀ w ∈ slitAt v, F (ψ w) = ψ (w + 1)
  /-- `ψ` intertwines the antiholomorphic square root `g` with the `ι`-symmetry. -/
  anti : ∀ w ∈ slitAt v, g (ψ w) = ψ (star w + 1 / 2)
  /-- far to the right, `ψ` is the inverse of the attracting Fatou coordinate on the sub-petal. -/
  far : ∀ w : ℂ, X < w.re → ψ w ∈ Pg ∧ φa (ψ w) = w

/-- **EXL — the exit loop of the `α`-window at `c₀`** (design §4.2, with the confinement of
`Submission/Work/GATE2/PL/NOTES_D1_gap.md` §4).

A compactum `𝒦` off the filled Julia set `K c₀`, on which the `α`-deviation of the critical
Böttcher coordinate is `< 1/16384` (so that the whole transit near `𝒦` stays inside the
`α`-window); the two ends `Ψ (u−1)` and `Ψ u` of the leak disc lie in `𝒦`; a second compactum `K₀`
with `Re < −1` and `Ψ K₀ ⊆ 𝒦` (the **confinement** of the exit loops, needed by UT's fixed box and
window); and for every `u` of the disc a loop from `u−1` to `u` inside `K₀` along which the
potential is at least `(3/4)·G(Ψ(u−1))` and whose offsets avoid the cut of `Ω_v` (condition (W)).

The offset-avoidance `(W)` is the one delicate point of the design. -/
structure ExitLoop (c₀ : ℂ) (Ψ : ℂ → ℂ) (x₀ r₀ v : ℝ) (α : ℝ) where
  /-- the compactum carrying the exit loop. -/
  𝒦 : Set ℂ
  /-- ... which is compact. -/
  isCompact : IsCompact 𝒦
  /-- ... and off the filled Julia set of `c₀` (hence inside `critDomain c₀`). -/
  offK : ∀ z ∈ 𝒦, z ∉ Work.EL.K c₀
  /-- the whole compactum lies in the thin `α`-window. -/
  win : ∀ z ∈ 𝒦, |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z| < (1 / 16384 : ℝ)
  /-- the two ends of the leak disc lie in the compactum. -/
  discs : ∀ u ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) r₀, Ψ (u - 1) ∈ 𝒦 ∧ Ψ u ∈ 𝒦
  /-- the confinement compactum of the exit loops. -/
  K₀ : Set ℂ
  /-- ... which is compact. -/
  isCompact_K₀ : IsCompact K₀
  /-- ... and lies in `{Re < −1}` (so that UT's exit window applies). -/
  K₀_re : ∀ w ∈ K₀, w.re < -1
  /-- ... and its `Ψ`-image lies in the window compactum. -/
  K₀_sub : ∀ w ∈ K₀, Ψ w ∈ 𝒦
  /-- the exit loop, with its potential floor and the offset-avoidance condition (W). -/
  loop : ∀ u ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) r₀, ∃ lam : C(unitInterval, ℂ),
    lam 0 = u - 1 ∧ lam 1 = u ∧ (∀ t, lam t ∈ K₀) ∧
    (∀ t, (3 / 4 : ℝ) * Work.Bottcher.green c₀ (Ψ (u - 1)) ≤
      Work.Bottcher.green c₀ (Ψ (lam t))) ∧
    (∀ t, (v : ℂ) + (lam t - (u - 1)) ∈ slitAt v)

/-- **PL for the `c₀`-flower**, in the flower's own vocabulary: `F = Work.EL.F c₀`,
`g = (T_{c₀})^5`, the sub-petal and Fatou coordinate of the `FatouCoord` fix. -/
abbrev PrincipalParamFlower (c₀ : ℂ) (Pg : Set ℂ) (φa : ℂ → ℂ) (v : ℝ) :=
  PrincipalParam (Work.EL.F c₀) ((Tantibar c₀)^[5]) c₀ Pg φa v

/-- **PL, in the form the sibling hypotheses can actually discharge** — the `far` field is
restricted to a *horizontal strip* `{Re > X, |Im| ≤ B}`.

The unrestricted half-plane form (`PrincipalParam.far` for all `w` with `Re w > X`) is **false**:
`Submission/Work/FatouCoord/NOTES.md` §2 records a machine-checked counterexample
(`h z = 1 + 2z`, `a = 2`) for which the Fatou coordinate's image is strip-like, not a right
half-plane; the FatouCoord shelf only proves the strip-tail statement `fatouCoordW_image_bdd`
(`∀ R B, ∃ C, ∀ τ, C < Re τ → |Im τ| ≤ B → ∃ w, R < Re w ∧ ψ w = τ`).  Every use in this area
(the box points of D1) has `|Im w|` bounded by the diameter of the loop confinement `K₀`, so the
strip form *would* suffice.

**Caveat (recorded in `NOTES.md` §13).**  This form is *not yet constructed*.  Two independent
reviews found that (i) `B` must be positive (done, `hB` below), otherwise `far` is vacuous and a
junk continuous witness exists; and (ii) `Work.GATE2.PL`'s construction cannot be seeded from the
strip hypothesis alone — `baseψ_mem` needs a preimage of `φa` for *every* `w` with `Re w > X`
(no bound on `|Im|`), and the Liouville step that yields `ψ v = c₀` uses the lifting over whole
half-planes.  So the strip statement is a genuine rework of PL, not a specialisation of it.  The
structure is kept here as the exact target. -/
structure PrincipalParamStrip (F g : ℂ → ℂ) (c₀ : ℂ) (Pg : Set ℂ) (φa : ℂ → ℂ) (v : ℝ) where
  /-- the parametrisation. -/
  ψ : ℂ → ℂ
  /-- the threshold beyond which `ψ` is the inverse of the Fatou coordinate. -/
  X : ℝ
  /-- the height of the strip in which that holds. -/
  B : ℝ
  /-- ... which must be positive, otherwise `far` below is vacuous. -/
  hB : 0 < B
  /-- `ψ` is continuous on the slit plane. -/
  cont : ContinuousOn ψ (slitAt v)
  /-- `ψ` passes through the critical value. -/
  ψv : ψ v = c₀
  /-- `ψ` intertwines `F` with the unit shift. -/
  shift : ∀ w ∈ slitAt v, F (ψ w) = ψ (w + 1)
  /-- `ψ` intertwines the antiholomorphic square root `g` with the `ι`-symmetry. -/
  anti : ∀ w ∈ slitAt v, g (ψ w) = ψ (star w + 1 / 2)
  /-- in the strip `{Re > X, |Im| ≤ B}`, `ψ` is the inverse of the Fatou coordinate on `Pg`. -/
  far : ∀ w : ℂ, X < w.re → |w.im| ≤ B → ψ w ∈ Pg ∧ φa (ψ w) = w

/-- The strip form of PL for the `c₀`-flower. -/
abbrev PrincipalParamStripFlower (c₀ : ℂ) (Pg : Set ℂ) (φa : ℂ → ℂ) (v : ℝ) :=
  PrincipalParamStrip (Work.EL.F c₀) ((Tantibar c₀)^[5]) c₀ Pg φa v

/-- A `PrincipalParam` (unrestricted `far`) is a `PrincipalParamStrip` (the strip case is a
specialisation). -/
def PrincipalParam.toStrip {F g : ℂ → ℂ} {c₀ : ℂ} {Pg : Set ℂ} {φa : ℂ → ℂ} {v : ℝ}
    (P : PrincipalParam F g c₀ Pg φa v) {B : ℝ} (hB : 0 < B) :
    PrincipalParamStrip F g c₀ Pg φa v where
  ψ := P.ψ
  X := P.X
  B := B
  hB := hB
  cont := P.cont
  ψv := P.ψv
  shift := P.shift
  anti := P.anti
  far := fun w hw _ => P.far w hw

/-- **UT with a caller-prescribed floor** (`Work.PARIMPL.TransitLockstep` with `X₁ ≥ Xb`).

For every bounded box `[X₁, X₁+W] × {|Im| ≤ H}` of the attracting coordinate *whose base `X₁` can
be taken above the prescribed `Xb`* and every bounded exit window `−Xo ≤ Re u < −1`, the `n`-th
iterate of any point `y'` within `ρ` of a box point `y` sits within `η` of
`Ψ (trans c − nIn + n + φa y)`, uniformly in the parameter and in `n`.

This is the form of UT that D1 needs: PL's `PrincipalParam.far` is available only on `{Re > X}`, so
the construction must place UT's box above `X` — and the box `X₁` produced by
`Work.PARIMPL.TransitLockstep` is a witness which D1 cannot otherwise control.  Forgetting the floor
gives `Work.PARIMPL.TransitLockstep`:

`TransitLockstepAbove … Xb v → TransitLockstep … v` (weakening by `le_refl`/dropping `Xb ≤ X₁`). -/
def TransitLockstepAbove (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (nIn : ℕ) (Ft : ℂ → ℂ → ℂ)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (Xb v : ℝ) : Prop :=
  ∀ H W Xo η : ℝ, 0 < η → ∃ X₁ ρ : ℝ, Xb ≤ X₁ ∧ 0 < ρ ∧
    ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ y y' : ℂ, ∀ n : ℕ,
      y ∈ Pa → X₁ ≤ (φa y).re → (φa y).re ≤ X₁ + W → |(φa y).im| ≤ H → ‖y' - y‖ ≤ ρ →
      let u := trans c - nIn - v + n + φa y
      (-Xo) ≤ u.re → u.re < -1 →
        ‖(Ft c)^[n] y' - Ψ u‖ ≤ η

/-- Weakening `TransitLockstepAbove` to PARIMPL's floor-free `TransitLockstep`. -/
theorem TransitLockstepAbove.toLockstep {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {nIn : ℕ}
    {Ft : ℂ → ℂ → ℂ} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {Xb v : ℝ}
    (h : TransitLockstepAbove c₀ Nm trans nIn Ft Pa φa Ψ Xb v) :
    Work.PARIMPL.TransitLockstep c₀ Nm trans nIn Ft Pa φa Ψ v := by
  intro H W Xo η hη
  obtain ⟨X₁, ρ, -, hρ, hb⟩ := h H W Xo η hη
  exact ⟨X₁, ρ, hρ, fun c hc y y' n hy h1 h2 h3 h4 hu1 hu2 =>
    hb c hc y y' n hy h1 h2 h3 h4 hu1 hu2⟩

end Work.GATE2
