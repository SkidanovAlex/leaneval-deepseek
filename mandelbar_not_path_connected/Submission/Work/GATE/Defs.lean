/-
# `Submission/Work/GATE/` — the `twoSided` field of `Work.Final.FinalInputs`

Area of the mandelbar project, subproject **GATE**: the second of the two residues of
`Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §2, namely the field

```
twoSided : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
  ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
  Work.ParamRays.extAngle e₁ ∈ Set.Ioo (alpha1 - windowEps) (alpha1 + windowEps) ∧
  Work.ParamRays.extAngle e₂ ∈ Set.Ioo (alpha2 - windowEps) (alpha2 + windowEps)
```

of `Work.Final.FinalInputs` (`Submission/Work/Final/Main.lean`): at every scale a straight
segment through the implosion side `Nm` near the root parameter `c₀` carries *escaping*
parameters whose parameter external angles lie in the two windows around the two root angles
`α₁ = 371/1023`, `α₂ = 404/1023`.

## The chain of §2 of the design, and what is in this file

The design decomposes `twoSided` into

* **TT (PARIMPL, §1.3–1.4)** — the *transit coordinate* `trans` of the imploded parabolic germ:
  continuous on `Nm` near `c₀`, with imaginary part `≈ 0` (height `0`), with `Re trans → -∞`
  at the parabolic locus (`trans_phase_blowup`), and the *escape* property: a parameter at which
  the transited critical value lands in the (shifted) leak disc is outside the connectedness
  locus.  Here: the structure `TransitData`.
* **GATE (§2.3)** — along the critical orbit the inverse branch fixing `±a` agrees with the
  `α₁`-Böttcher branch, via connecting paths to the `α₁` ray tail; consequence: a parameter in
  the `b`-tongue has `extAngle ≈ α₁` and a parameter in the `ι b`-tongue has `extAngle ≈ α₂`.
  Here: the structure `GateAngle`, whose two fields are *verbatim* the conclusion `gate_angle`
  of §2.3 (`G1`–`G4` + `A1` are its provenance).
* **SEG (§2.1)** — the straight segment: it ends on the parabolic arc, sweeps `≥ 2` transit
  turns at height `≈ 0`, and therefore hits both the `b`-tongue and the `ι b`-tongue.  Proved
  here (`Submission/Work/GATE/Segment/`, module `…Segment.All`), from `TransitData` and the
  elementary structure of `Nm` (`IsOpen`, `c₀ ∈ frontier Nm`).
* **the leak point in an `α`-access (§2.2)** — `A1` (the ELNest nest-angle lemma), the ELCYL
  dichotomy (`TailId`, the crossing parity) and the shift of the leak
  (`Work.Final.equatorLeak_shift`, *proved*).  The nest-angle lemma `A1` is *derivable* from the
  delivered pair-side angle lemmas and the angular nesting of the nest; it is proved here in
  `Submission/Work/GATE/Nest/` (see `Work.GATE.Nest.ray_angle_of_near_sides`).

## What to import

```lean
import Submission.Work.GATE.All          -- the whole chapter
import Submission.Work.GATE.TwoSided      -- the target: Work.GATE.twoSided
```

The single entry point for the drive is

```lean
Work.GATE.twoSided (hOpen : IsOpen Nm) (hfront : c₀ ∈ frontier Nm)
    (TD : Work.GATE.TransitData c₀ Nm) (G : Work.GATE.GateAngle c₀ Nm TD) :
    Work.GATE.TwoSided c₀ Nm
```
i.e. `Work.GATE.TwoSided c₀ Nm` is *definitionally* the `twoSided` field of
`Work.Final.FinalInputs`, so the lead can write `twoSided := Work.GATE.twoSided …` verbatim.
-/
import Submission.Work.Final.Defs

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

namespace Work.GATE

open LeanEval.ComplexAnalysis (Mandelbar)

/-! ## The two tongues of the transit coordinate -/

/-- **The `b`-tongue.**  The transit coordinate of the imploded germ is `≈ xLeak + k` for an
integer `k`: the transited critical value lands in the `k`-th integer translate of the leak disc
of the equatorial rigidity.  Since the repelling coordinate satisfies `Ψ (w + 1) = F (Ψ w)`, the
integer translates are the forward images of one and the same leak point: this is the family
labelled `b` in §2.1 of the design. -/
def bTongue (trans : ℂ → ℂ) (xLeak r₀ : ℝ) (e : ℂ) : Prop :=
  ∃ k : ℤ, dist (trans e) (((xLeak + (k : ℝ)) : ℝ) : ℂ) < r₀ / 2

/-- **The `ι b`-tongue**: the transited critical value lands in the half-integer translate
`xLeak + 1/2 + ℤ` of the leak disc.  By the `ι`-symmetry of the equator,
`Ψ (w̄ + 1/2) = (T_c)^5 (Ψ w)`, this is the leak of the `ι`-image of the leak point
(`Work.Final.equatorLeak_shift`), pushed forward by the antiholomorphic square root of the
second return map. -/
def iotaTongue (trans : ℂ → ℂ) (xLeak r₀ : ℝ) (e : ℂ) : Prop :=
  ∃ k : ℤ, dist (trans e) (((xLeak + 1 / 2 + (k : ℝ)) : ℝ) : ℂ) < r₀ / 2

theorem bTongue_def {trans : ℂ → ℂ} {xLeak r₀ : ℝ} {e : ℂ} :
    bTongue trans xLeak r₀ e ↔
      ∃ k : ℤ, dist (trans e) (((xLeak + (k : ℝ)) : ℝ) : ℂ) < r₀ / 2 := Iff.rfl

theorem iotaTongue_def {trans : ℂ → ℂ} {xLeak r₀ : ℝ} {e : ℂ} :
    iotaTongue trans xLeak r₀ e ↔
      ∃ k : ℤ, dist (trans e) (((xLeak + 1 / 2 + (k : ℝ)) : ℝ) : ℂ) < r₀ / 2 := Iff.rfl

/-- The distance from a complex number to a real number, when the real part matches: this is the
form in which the height bound `|Im trans e| ≤ r₀/8` of `TransitData` is turned into a bound on
`dist (trans e) (xLeak + k)`. -/
theorem dist_ofReal_of_re_eq {z : ℂ} {x : ℝ} (h : z.re = x) : dist z (x : ℂ) = |z.im| := by
  have hz : z - (x : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, h, Complex.mul_I_im]
  rw [Complex.dist_eq, hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- A point of the `b`-tongue whose height is small is *on* the leak lattice: the height bound
`|Im trans e| ≤ r₀/8` of `TransitData` turns `Re trans e = xLeak + k` into
`dist (trans e) (xLeak + k) < r₀/2`, the form in which the escape property `(I2)` of PARIMPL §1.4
is consumed. -/
theorem bTongue_of_re_eq {trans : ℂ → ℂ} {xLeak r₀ : ℝ} {e : ℂ} {k : ℤ}
    (hre : (trans e).re = xLeak + (k : ℝ)) (him : |(trans e).im| < r₀ / 2) :
    bTongue trans xLeak r₀ e :=
  ⟨k, by rw [dist_ofReal_of_re_eq hre]; exact him⟩

theorem iotaTongue_of_re_eq {trans : ℂ → ℂ} {xLeak r₀ : ℝ} {e : ℂ} {k : ℤ}
    (hre : (trans e).re = xLeak + 1 / 2 + (k : ℝ)) (him : |(trans e).im| < r₀ / 2) :
    iotaTongue trans xLeak r₀ e :=
  ⟨k, by rw [dist_ofReal_of_re_eq hre]; exact him⟩

/-- Shifting the first argument of `dist` by `1/2` shifts the second by `1/2`. -/
theorem dist_sub_half (z w : ℂ) : dist (z - 1 / 2) w = dist z (w + 1 / 2) := by
  rw [Complex.dist_eq, Complex.dist_eq]
  congr 1
  ring

/-- The two tongues are the two lattices: shifting the transit coordinate by `1/2` exchanges
them.  This is the formal content of the `ι`-symmetry of the equator: the `ι b`-tongue of the
coordinate `trans` is the `b`-tongue of the coordinate `trans - 1/2`. -/
theorem iotaTongue_iff_bTongue_shift (trans : ℂ → ℂ) (xLeak r₀ : ℝ) (e : ℂ) :
    iotaTongue trans xLeak r₀ e ↔ bTongue (fun c => trans c - 1 / 2) xLeak r₀ e := by
  have hcast : ∀ k : ℤ, (((xLeak + (k : ℝ) : ℝ)) : ℂ) + 1 / 2 =
      (((xLeak + 1 / 2 + (k : ℝ) : ℝ)) : ℂ) := by
    intro k; push_cast; ring
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [dist_sub_half, hcast k]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [dist_sub_half, hcast k] at hk
    exact hk

/-! ## TT: the transit data of the imploded germ (PARIMPL §1.3–1.4) -/

/-- **The transit coordinate of the imploded parabolic germ** — the input `TT` of the design §2.1,
in the exact form of §1.3–1.4 of `NOTES_LEAD_mandelbar_residuals.md`:

* `trans` is the transit coordinate `Ũ_sym (u (F^[nIn] c)) - π/λ_c` of the critical orbit
  (PARIMPL's `TRANS`);
* `cont` — `trans_cont`: continuity on the implosion side near `c₀`;
* `height` — `trans_height` with `critHeight_zero`: the transited critical value has Écalle
  height `≈ 0`, stated as a bound by the leak radius;
* `blowup` — `trans_phase_blowup`: the phase blows up like `π/λ_c` at the parabolic arc, i.e.
  `Re trans → -∞` along `Nm` at every point of the frontier of `Nm` (the design's `Par`);
* `escape_b`, `escape_iota` — `trans_escape` (§1.4, with the joint continuity `(I2)` of the Green
  function) for the leak disc `{dist · xLeak ≤ r₀}` and for its half-integer shift
  `{dist · (xLeak + 1/2) ≤ r₀}` (`Work.Final.equatorLeak_shift`).  `xLeak = x* - j₀` is the
  (deep) leak level of §1.4. -/
structure TransitData (c₀ : ℂ) (Nm : Set ℂ) where
  /-- the (deep) leak level `x* - j₀` of the repelling coordinate. -/
  xLeak : ℝ
  /-- the leak radius of `(I2)`. -/
  r₀ : ℝ
  /-- the leak radius is positive. -/
  hr₀ : 0 < r₀
  /-- the radius of the neighbourhood of `c₀` on which the transit data holds. -/
  ρ : ℝ
  /-- ... which is positive. -/
  hρ : 0 < ρ
  /-- the transit coordinate itself. -/
  trans : ℂ → ℂ
  /-- `trans_cont`. -/
  cont : ContinuousOn trans (Nm ∩ Metric.ball c₀ ρ)
  /-- `trans_height`: the Écalle height of the transited critical value is `≈ 0` — stated as a
  bound by the leak radius, which is the form SEG consumes. -/
  height : ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, |(trans c).im| ≤ r₀ / 8
  /-- `trans_phase_blowup`, on the whole frontier of the implosion side. -/
  blowup : ∀ p ∈ frontier Nm ∩ Metric.ball c₀ ρ,
    Tendsto (fun c => (trans c).re) (𝓝[Nm] p) atBot
  /-- `trans_escape` for the leak disc `xLeak + ℤ` (the `b`-tongue). -/
  escape_b : ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, bTongue trans xLeak r₀ c → c ∉ Mandelbar
  /-- `trans_escape` for the shifted leak disc `xLeak + 1/2 + ℤ` (the `ι b`-tongue). -/
  escape_iota : ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, iotaTongue trans xLeak r₀ c → c ∉ Mandelbar

/-- For real arguments, the distance in `ℂ` is the absolute value of the difference. -/
theorem dist_ofReal (a b : ℝ) : dist ((a : ℝ) : ℂ) ((b : ℝ) : ℂ) = |a - b| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The two leak lattices are separated by at least `1/2`. -/
theorem half_le_dist_lattice (x : ℝ) (k m : ℤ) :
    1 / 2 ≤ dist (((x + (k : ℝ)) : ℝ) : ℂ) (((x + 1 / 2 + (m : ℝ)) : ℝ) : ℂ) := by
  rw [dist_ofReal]
  have h : x + (k : ℝ) - (x + 1 / 2 + (m : ℝ)) = ((k - m : ℤ) : ℝ) - 1 / 2 := by
    push_cast; ring
  rw [h]
  rcases le_total (k - m) 0 with hn | hn
  · have h' : ((k - m : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [abs_of_neg (by linarith)]
    linarith
  · rcases eq_or_lt_of_le hn with h0 | hpos
    · rw [← h0]; norm_num
    · have h1 : (1 : ℝ) ≤ ((k - m : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ k - m := hpos
        exact_mod_cast this
      rw [abs_of_pos (by linarith)]
      linarith

/-- **The two tongues are disjoint** (for a leak radius below `1/2`): a parameter of the
`b`-tongue is not a parameter of the `ι b`-tongue.  This is the formal content of the two leak
families of §2.1 being distinct: the lattices `xLeak + ℤ` and `xLeak + 1/2 + ℤ` are separated by
`1/2`. -/
theorem bTongue_not_iotaTongue {trans : ℂ → ℂ} {xLeak r₀ : ℝ} (hr : r₀ < 1 / 2) {e : ℂ}
    (h₁ : bTongue trans xLeak r₀ e) : ¬ iotaTongue trans xLeak r₀ e := by
  rintro ⟨m, hm⟩
  obtain ⟨k, hk⟩ := h₁
  have htri : dist (((xLeak + (k : ℝ)) : ℝ) : ℂ) (((xLeak + 1 / 2 + (m : ℝ)) : ℝ) : ℂ) < r₀ := by
    calc dist (((xLeak + (k : ℝ)) : ℝ) : ℂ) (((xLeak + 1 / 2 + (m : ℝ)) : ℝ) : ℂ)
        ≤ dist (((xLeak + (k : ℝ)) : ℝ) : ℂ) (trans e)
          + dist (trans e) (((xLeak + 1 / 2 + (m : ℝ)) : ℝ) : ℂ) := dist_triangle _ _ _
      _ = dist (trans e) (((xLeak + (k : ℝ)) : ℝ) : ℂ)
          + dist (trans e) (((xLeak + 1 / 2 + (m : ℝ)) : ℝ) : ℂ) := by
            rw [dist_comm (((xLeak + (k : ℝ)) : ℝ) : ℂ) (trans e)]
      _ < r₀ / 2 + r₀ / 2 := add_lt_add hk hm
      _ = r₀ := by ring
  have := half_le_dist_lattice xLeak k m
  linarith

namespace TransitData

variable {c₀ : ℂ} {Nm : Set ℂ} (TD : TransitData c₀ Nm)

/-- The `b`-tongue grows with the leak radius. -/
theorem bTongue_mono {trans : ℂ → ℂ} {xLeak r r' : ℝ} (h : r ≤ r') {e : ℂ}
    (he : bTongue trans xLeak r e) : bTongue trans xLeak r' e := by
  obtain ⟨k, hk⟩ := he
  exact ⟨k, lt_of_lt_of_le hk (by linarith)⟩

/-- The `ι b`-tongue grows with the leak radius. -/
theorem iotaTongue_mono {trans : ℂ → ℂ} {xLeak r r' : ℝ} (h : r ≤ r') {e : ℂ}
    (he : iotaTongue trans xLeak r e) : iotaTongue trans xLeak r' e := by
  obtain ⟨k, hk⟩ := he
  exact ⟨k, lt_of_lt_of_le hk (by linarith)⟩

/-- The transit data restricted to a smaller neighbourhood of `c₀`: the fields are stated for a
ball of radius `ρ`, and passing to a smaller radius only shrinks their statements. -/
def restrict (ρ' : ℝ) (hρ' : 0 < ρ') (hle : ρ' ≤ TD.ρ) : TransitData c₀ Nm where
  xLeak := TD.xLeak
  r₀ := TD.r₀
  hr₀ := TD.hr₀
  ρ := ρ'
  hρ := hρ'
  trans := TD.trans
  cont := TD.cont.mono (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hle))
  height := fun c hc => TD.height c ⟨hc.1, Metric.ball_subset_ball hle hc.2⟩
  blowup := fun p hp => TD.blowup p ⟨hp.1, Metric.ball_subset_ball hle hp.2⟩
  escape_b := fun c hc => TD.escape_b c ⟨hc.1, Metric.ball_subset_ball hle hc.2⟩
  escape_iota := fun c hc => TD.escape_iota c ⟨hc.1, Metric.ball_subset_ball hle hc.2⟩

@[simp] theorem restrict_trans (ρ' : ℝ) (hρ' : 0 < ρ') (hle : ρ' ≤ TD.ρ) :
    (TD.restrict ρ' hρ' hle).trans = TD.trans := rfl

@[simp] theorem restrict_xLeak (ρ' : ℝ) (hρ' : 0 < ρ') (hle : ρ' ≤ TD.ρ) :
    (TD.restrict ρ' hρ' hle).xLeak = TD.xLeak := rfl

@[simp] theorem restrict_r₀ (ρ' : ℝ) (hρ' : 0 < ρ') (hle : ρ' ≤ TD.ρ) :
    (TD.restrict ρ' hρ' hle).r₀ = TD.r₀ := rfl

end TransitData

/-! ## GATE: the angle transport through the gate (§2.3) -/

/-- **The gate angle transport** — the conclusion `gate_angle` of §2.3 of the design, in the two
tongues.  Its provenance is the chain `A1` + `G1`–`G4`: the `α₁`-branch `Λ_e` of the Böttcher
inverse on the tube `S₁(e)`, the identification `L_e = Λ_e` along the critical orbit (`G1` for the
inverse branch fixing `±a_e`, `G2` for the two ends of each segment `ρ_k`), and the connecting
paths `L_e^[k] P_e` to the `α₁` ray tail (`G3`), giving `e = Λ_e^[m] p_e` and hence

`extAngle e = α₁ + (ϑ_e p_e - α₁)/1024^m`,

which lies in the window because `|ϑ_e p_e - α₁| < 1/2048`.

`A1` (`Work.GATE.Nest.ray_angle_of_near_sides`) and the ELCYL dichotomy (the `TailId` of §3.2 and
the crossing parity) supply the *base* of `G2`: the leak point of the equatorial rigidity is
accessed by the `α₁`-ray tail.  `G1` is the only step that needs PARIMPL's domain `D` and the
joint continuity of the Böttcher coordinate; it is recorded here as the two fields below. -/
structure GateAngle (c₀ : ℂ) (Nm : Set ℂ) (TD : TransitData c₀ Nm) : Prop where
  /-- a parameter in the `b`-tongue near `c₀` has parameter external angle in the `α₁`-window. -/
  b : ∀ ε > 0, ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
    bTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
      |Work.ParamRays.extAngle e - Work.Final.alpha1| < ε
  /-- a parameter in the `ι b`-tongue has parameter external angle in the `α₂`-window: the
  `ι`-symmetry `Ψ (w̄ + 1/2) = (T_c)^5 (Ψ w)` of the repelling coordinate, pushed through the gate
  of the `α₂`-tail (`G2` for the second branch). -/
  iota : ∀ ε > 0, ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
    iotaTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
      |Work.ParamRays.extAngle e - Work.Final.alpha2| < ε

/-! ## The target: the `twoSided` field of `Work.Final.FinalInputs`, verbatim -/

/-- **The `twoSided` field of `Work.Final.FinalInputs`, *verbatim*** (compare
`Submission/Work/Final/Main.lean`): at every scale `r > 0` there is a straight segment in the
implosion side `Nm` inside `ball c₀ r` carrying two escaping parameters, whose parameter external
angles lie in the windows around `α₁` and `α₂` of half-width `windowEps = 1/2048`. -/
def TwoSided (c₀ : ℂ) (Nm : Set ℂ) : Prop :=
  ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
    ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
    Work.ParamRays.extAngle e₁ ∈ Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
      (Work.Final.alpha1 + Work.Final.windowEps) ∧
    Work.ParamRays.extAngle e₂ ∈ Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
      (Work.Final.alpha2 + Work.Final.windowEps)

theorem twoSided_iff (c₀ : ℂ) (Nm : Set ℂ) : TwoSided c₀ Nm ↔
    ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.ParamRays.extAngle e₁ ∈ Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
        (Work.Final.alpha1 + Work.Final.windowEps) ∧
      Work.ParamRays.extAngle e₂ ∈ Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
        (Work.Final.alpha2 + Work.Final.windowEps) :=
  Iff.rfl

/-- The window of half-width `ε` around `α`, from a bound on `|θ - α|`. -/
theorem mem_window_of_abs_lt {θ α ε : ℝ} (h : |θ - α| < ε) :
    θ ∈ Set.Ioo (α - ε) (α + ε) := by
  rw [abs_lt] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The half-width `windowEps = 1/2048` of the two angle windows is positive. -/
theorem windowEps_pos : 0 < Work.Final.windowEps := by
  rw [Work.Final.windowEps, Work.Landing.windowEps]
  norm_num

/-- The two windows are *disjoint* from the far arc: `α₁ + windowEps < α₂ - windowEps`.  This is
the arithmetic content of the window separation (`Work.Final.window_separation`) that makes the
two escaping parameters `e₁`, `e₂` of `twoSided` *different* angles. -/
theorem windows_disjoint :
    Work.Final.alpha1 + Work.Final.windowEps < Work.Final.alpha2 - Work.Final.windowEps := by
  have h := Work.Final.window_separation
  linarith [h.2.1, h.2.2.1]

end Work.GATE
