/-
# `Submission/Work/GATE2/` — the vocabulary of the three residuals of the `twoSided` gate

Area **GATE2** of the mandelbar project: the three residuals that the delivered GATE chapter
(`Submission/Work/GATE/`) leaves open, and their assembly into the `twoSided` field of
`Work.Final.FinalInputs`.

The GATE chapter proves the whole chain of §2 of `NOTES_LEAD_mandelbar_residuals.md` down to the
per-parameter residual

```
Work.GATE.twoSided_of_residual (hOpen) (hfront) (TD : TransitData c₀ Nm) h₁ h₂ : TwoSided c₀ Nm
```

with

* `h₁ : ∃ ρ > 0, ∀ e ∈ Nm ∩ ball c₀ ρ, bTongue … e → e ∉ Mandelbar → Nonempty (GateResidual e α₁)`,
* `h₂` : the same for the `ι b`-tongue and `α₂`.

This module fixes the vocabulary in which GATE2 states the three residuals of the design:

1. **ACCESS** (`Submission/Work/GATE2/Access.lean`): the positive dichotomy of §2.2 — the base
   point of the connecting path is accessed by a root-ray (case (i): a real point on the lift of
   `R(α₁)`) or by the deep equator tail (case (ii): ELRig's `htail`).  In both cases the point
   off the filled Julia set lies in the two near sides of the nest, so `A1`
   (`Work.GATE.Nest.nest_angle_design`) puts its ray angle in one of the two windows.
2. **TRANSPORT** (residual 2, `Submission/Work/GATE2/Transport.lean`): the transport of the
   branch data and of the base window from `c₀` to the parameters `e` of the two tongues.  Here
   the *tube* and the *branch* are no longer part of the residual: for **any** parameter carrying
   the dynamical Böttcher data, the Böttcher inverse branch on the tube of ray points of the
   `α₁`-window satisfies all four `BranchData` conditions (`Work.GATE.Gate.branchDataAlpha1`, a
   construction that only uses `DynB` and `IsCritBottcher`, hence applies verbatim at `e`).  What
   remains is the *orbit* statement: the critical orbit of `F_e = (T_e)^{10}` meets the
   `α`-window of the tube, and the ray-tube branch follows it backwards.  This is the design's
   `G1`+`G2`+`G3`.
3. **SHIFTED ESCAPE** (residual 3, `Submission/Work/GATE2/Escape.lean`): the `trans_escape` of
   PARIMPL's `LeakData` for the *half-integer* translate `x* - j₀ + 1/2` (the `ι b`-tongue).
   The half-shifted leak disc is a leak disc because of the `ι`-symmetry
   `Ψ (w̄ + 1/2) = (T_c)^5 (Ψ w)` of the antiholomorphic Écalle cylinder (HS Lemma 2.3) — a
   *proved* statement here, from ELRig's `ParabolicFlower.Ψ_anti` and the total invariance of the
   filled Julia set.

## The sibling exports consumed by this area

* **ELRig**: `Work.EL.RootParabolic`, the Leau–Fatou flower, `Work.EL.Z1Nest` (nest, certificate
  angles, `SP`), `Work.ELRig.RayCylLift` (`TailId`, `hzne`, `img₁`, `img₂`), `Work.EL.PairSides`
  and the ELTop ray-side lemmas;
* **PARIMPL**: `Work.PARIMPL.ParNormal` (with `Nm`, `Par`), `MatchData`, `TransitData`
  (`transU`, the exit matching), `LeakData` (the leak point, the deep disc, the robustness (I2));
* **NAKANE**: `Work.NAKANE.continuousOn_jointVarphi` (joint Böttcher continuity) and
  `Work.NAKANE.GreenJoint` (joint Green continuity, i.e. `Work.PARIMPL.GreenEscapeOpen`).

The **one** place where a sibling area's final form is still in flight is ELRig's R-a3 `htail`
(`∃ R', ∀ x : ℝ, x < -R' → Ψ x ∈ pairSideNear nest.P0`), which GATE2 consumes in exactly the form
in which ELRig's own `Work.EL.equatorLeak_of_htail` consumes it.  See `NOTES.md`.
-/
import Submission.Work.GATE2.Inputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## The tracked transit exit (PARIMPL's `TransitData.exit`, tracked in the integer) -/

/-! ## ⚠ The defect: `ExitTracked` is refutable

`ExitTracked` quantifies over *every* integer `k`
with `Re (trans c + k) < -1`, and is already false for `η = 1` as soon as `Nm ∩ ball c₀ ρ`
contains an escaping parameter `c ∉ M*` (which the tongues provide): every `k ≪ 0` is admissible,
`fl.Ψ_small` puts the targets `Ψ (trans c + k)` arbitrarily close to `z₁`, while the *escaping*
critical orbit of `c ∉ M*` visits `ball z₁ 1` only finitely often — so a single orbit point would
have to be the limit `z₁`, contradicting `Ψ u ≠ z₁`.  Every theorem of this chapter that took
`hExit : ExitTracked …` as a hypothesis is therefore *vacuous*; it is kept only as the record of
the defect.  The honest form is `Work.GATE2.ExitTrackedLoc` below (the design's bounded-window
exit, which `Work.PARIMPL.TransitData.UT` implies).  See `NOTES.md` §0 and
`Submission/Work/NOTES_LEAD_mandelbar_gate2transport.md` §2. -/

/-- **The tracked transit exit.**  The design's PARIMPL §1.3–1.4 exit matching, *tracked in the
integer*: the repelling coordinate `u` of an orbit point is the transit coordinate plus **that
integer**, for *every* admissible number `k` of transit steps (the transit has `≈ π/λ_c` steps,
so every `k` with `Re (trans c) + k < -1` occurs).

This is a refinement of the field `Work.PARIMPL.TransitData.exit` of PARIMPL's transit data
(which asserts only that *some* integer works); the refinement is what makes the leak disc of a
*prescribed* level `x* - j₀` (or its half-integer translate) escapable.  It is stated entirely in
the vocabulary of PARIMPL's objects: the transit coordinate `trans`, the second return map
`Ft = (T_c)^{10}`, the repelling coordinate `Ψ` of the flower and the implosion side `Nm`. -/
def ExitTracked (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (Ft : ℂ → ℂ → ℂ) (Ψ : ℂ → ℂ) : Prop :=
  ∀ η > 0, ∃ ρ > 0, ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ k : ℤ,
    (trans c + (k : ℂ)).re < -1 →
      ∃ n : ℕ, ∃ u : ℂ, Ψ u = (Ft c)^[n] c ∧ ‖u - (trans c + (k : ℂ))‖ ≤ η

/-- **The tracked exit implies PARIMPL's exit matching.**  For a fixed parameter `c` there is an
integer `k` with `Re (trans c) + k < -1` (take `k` very negative), so `ExitTracked` gives an orbit
point with repelling coordinate equal to `trans c + k` up to `η`: exactly the statement of
`Work.PARIMPL.TransitData.exit`. -/
theorem ExitTracked.toTransitExit {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ}
    {Ψ : ℂ → ℂ} (h : ExitTracked c₀ Nm trans Ft Ψ) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ,
      ∃ n : ℕ, ∃ u : ℂ, ∃ k : ℤ,
        u.re < -1 ∧ Ψ u = (Ft c)^[n] c ∧ ‖u - (trans c + (k : ℂ))‖ ≤ η := by
  intro η hη
  obtain ⟨ρ, hρ, hρ'⟩ := h (min η 1) (lt_min hη one_pos)
  refine ⟨ρ, hρ, fun c hc => ?_⟩
  set k : ℤ := -⌈(trans c).re⌉ - 3 with hk
  have hkre : (trans c + (k : ℂ)).re ≤ -3 := by
    have h1 : ((k : ℤ) : ℝ) = -(((⌈(trans c).re⌉ : ℤ) : ℝ)) - 3 := by simp [hk]
    have h2 : (trans c + (k : ℂ)).re = (trans c).re + (k : ℝ) := by simp
    have h3 : (trans c).re ≤ (((⌈(trans c).re⌉ : ℤ) : ℝ)) := Int.le_ceil _
    rw [h2, h1]; linarith
  obtain ⟨n, u, hu, hdist⟩ := hρ' c hc k (lt_of_le_of_lt hkre (by norm_num))
  have hure : u.re < -1 := by
    have h1 : |u.re - (trans c + (k : ℂ)).re| ≤ ‖u - (trans c + (k : ℂ))‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (u - (trans c + (k : ℂ)))
    have h2 : |u.re - (trans c + (k : ℂ)).re| ≤ 1 :=
      le_trans h1 (le_trans hdist (min_le_right _ _))
    have h3 : u.re - (trans c + (k : ℂ)).re ≤ 1 := (abs_le.mp h2).2
    linarith
  exact ⟨n, u, k, hure, hu, le_trans hdist (min_le_left _ _)⟩


/-- **The bounded-window exit** — the honest replacement of `ExitTracked`, and the form the
design's §2/§5 of `NOTES_LEAD_mandelbar_gate2transport.md` prescribes: the tracked exit is
restricted to the *bounded* window `-X ≤ Re (trans c + k) < -1` of exit levels.

Two remarks on the exact form.

* The window is bounded *below* (`-X ≤ ·`), which is what rules out the refutation of
  `ExitTracked`: every use needs only the single integer `k` that pins the transit coordinate to
  the leak lattice, and there `Re (trans c + k)` is bounded by `xLeak + r₀/2` (the leak level is
  deep: `Re < -1`).
* The conclusion is stated as `‖(Ft c)^[n] c - Ψ (trans c + k)‖ ≤ η` rather than the design's
  `∃ u, Ψ u = (Ft c)^[n] c ∧ ‖u - (trans c + k)‖ ≤ η`.  The two are equivalent up to composing
  with the local inverse of `Ψ` (which is a local homeomorphism on `Re < -1`), and the present
  form is the one that `Work.PARIMPL.TransitData.UT` gives *directly*. -/
def ExitTrackedLoc (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (Ft : ℂ → ℂ → ℂ) (Ψ : ℂ → ℂ) : Prop :=
  ∀ X η : ℝ, 1 < X → 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ k : ℤ,
    -X ≤ (trans c + (k : ℂ)).re → (trans c + (k : ℂ)).re < -1 →
      ∃ n : ℕ, ‖(Ft c)^[n] c - Ψ (trans c + (k : ℂ))‖ ≤ η

/-- **Non-vacuity of the exit window.**  For a window of length `≥ 2` (`3 ≤ X`) there is always
an integer level in it, namely `-⌈Re z⌉ - 2`, whose real part lies in `[-3, -2)`.  (The design
writes `X > 1`; every use takes `X` large, and `3 ≤ X` is what the arithmetic below needs.) -/
theorem exists_int_window (z : ℂ) {X : ℝ} (hX : 3 ≤ X) :
    ∃ k : ℤ, -X ≤ (z + (k : ℂ)).re ∧ (z + (k : ℂ)).re < -1 := by
  have hre : ∀ k : ℤ, (z + (k : ℂ)).re = z.re + (k : ℝ) := fun k => by
    simp [Complex.add_re]
  have hcast : ∀ k : ℤ, ((-k - 2 : ℤ) : ℝ) = -(k : ℝ) - 2 := fun k => by push_cast; ring
  refine ⟨-⌈z.re⌉ - 2, ?_, ?_⟩
  · rw [hre, hcast]
    have h : ((⌈z.re⌉ : ℤ) : ℝ) ≤ z.re + 1 := by
      have := Int.ceil_lt_add_one z.re; linarith
    linarith
  · rw [hre, hcast]
    have h : z.re ≤ ((⌈z.re⌉ : ℤ) : ℝ) := Int.le_ceil z.re
    linarith

/-! ## Extracting an integer from the distance to the `ℤ`-orbit -/

/-- **The distance to the `ℤ`-orbit is attained.**  If `distZ z x < r` then some translate
`z + k` is within `r` of `x`.  (`distZ` is an `iInf` over `ℤ`, so `distZ z x < r` gives some
index, by `le_ciInf`.) -/
theorem exists_dist_lt_of_distZ_lt {z x : ℂ} {r : ℝ}
    (h : Work.PARIMPL.distZ z x < r) : ∃ k : ℤ, dist (z + (k : ℂ)) x < r := by
  by_contra hc
  push Not at hc
  have : r ≤ Work.PARIMPL.distZ z x := le_ciInf fun k => hc k
  linarith

/-- The tongue form of the same: a point of the `b`-tongue is at `distZ`-distance `< r₀/2` from
the leak level `xLeak`. -/
theorem distZ_lt_of_bTongue {trans : ℂ → ℂ} {xLeak r₀ : ℝ} {e : ℂ}
    (h : Work.GATE.bTongue trans xLeak r₀ e) :
    Work.PARIMPL.distZ (trans e) ((xLeak : ℝ) : ℂ) < r₀ / 2 := by
  obtain ⟨k, hk⟩ := h
  refine lt_of_le_of_lt (Work.PARIMPL.distZ_le (trans e) ((xLeak : ℝ) : ℂ) (-k)) ?_
  have hsub : (trans e + ((-k : ℤ) : ℂ)) - ((xLeak : ℝ) : ℂ)
      = trans e - (((xLeak + (k : ℝ)) : ℝ) : ℂ) := by push_cast; ring
  rwa [dist_eq_norm, hsub, ← dist_eq_norm]

/-- The `ι b`-tongue version, at the half-integer translate `xLeak + 1/2`. -/
theorem distZ_lt_of_iotaTongue {trans : ℂ → ℂ} {xLeak r₀ : ℝ} {e : ℂ}
    (h : Work.GATE.iotaTongue trans xLeak r₀ e) :
    Work.PARIMPL.distZ (trans e) (((xLeak + 1 / 2 : ℝ)) : ℂ) < r₀ / 2 := by
  obtain ⟨k, hk⟩ := h
  refine lt_of_le_of_lt (Work.PARIMPL.distZ_le (trans e)
    (((xLeak + 1 / 2 : ℝ)) : ℂ) (-k)) ?_
  have hsub : (trans e + ((-k : ℤ) : ℂ)) - (((xLeak + 1 / 2 : ℝ)) : ℂ)
      = trans e - (((xLeak + 1 / 2 + (k : ℝ)) : ℝ) : ℂ) := by push_cast; ring
  rwa [dist_eq_norm, hsub, ← dist_eq_norm]

/-! ## The base window in the two root directions -/

/-- **The base window**: the conclusion of `Work.GATE.Nest.base_window_disjunction` — the base
point of the connecting path has its `α`-relative Böttcher argument within `windowEps` of one of
the two root directions.  This is what the gate transport `Work.GATE.gate_window` consumes. -/
def BasePointWindow (φ : ℂ → ℂ) (z : ℂ) : Prop :=
  |Work.GATE.deviation φ Work.EL.alpha1 z| < Work.Final.windowEps ∨
    |Work.GATE.deviation φ Work.EL.alpha2 z| < Work.Final.windowEps

/-! ## The transport residual (residual 2) -/

/-- **The transport residual**, in the minimal form: per-parameter gate residuals for the two
tongues.  This is *verbatim* the pair of hypotheses `h₁`, `h₂` of
`Work.GATE.twoSided_of_residual`.

The finer, purely dynamical form in which the design's `G1`–`G3` produce it is
`TongueOrbitResidual` (module `Submission.Work.GATE2.Transport`), and
`Work.GATE2.TongueOrbitResidual.toTongueResidual` derives this one from it. -/
structure TongueResidual (c₀ : ℂ) (Nm : Set ℂ) (TD : Work.GATE.TransitData c₀ Nm) where
  /-- the radius on which the transport holds. -/
  ρ : ℝ
  /-- ... which is positive. -/
  hρ : 0 < ρ
  /-- the `b`-tongue parameters have their external angle in the `α₁`-window. -/
  b : ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e →
    e ∉ Mandelbar → Nonempty (Work.GATE.GateResidual e Work.Final.alpha1)
  /-- the `ι b`-tongue parameters have their external angle in the `α₂`-window. -/
  iota : ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e →
    e ∉ Mandelbar → Nonempty (Work.GATE.GateResidual e Work.Final.alpha2)

/-- The residual in the `∃ ρ > 0` shape in which `Work.GATE.twoSided_of_residual` consumes it. -/
theorem TongueResidual.b_res {c₀ : ℂ} {Nm : Set ℂ} {TD : Work.GATE.TransitData c₀ Nm}
    (TR : TongueResidual c₀ Nm TD) :
    ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e →
      e ∉ Mandelbar → Nonempty (Work.GATE.GateResidual e Work.Final.alpha1) :=
  ⟨TR.ρ, TR.hρ, TR.b⟩

/-- The same for the `ι b`-tongue. -/
theorem TongueResidual.iota_res {c₀ : ℂ} {Nm : Set ℂ} {TD : Work.GATE.TransitData c₀ Nm}
    (TR : TongueResidual c₀ Nm TD) :
    ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e →
      e ∉ Mandelbar → Nonempty (Work.GATE.GateResidual e Work.Final.alpha2) :=
  ⟨TR.ρ, TR.hρ, TR.iota⟩

end Work.GATE2
