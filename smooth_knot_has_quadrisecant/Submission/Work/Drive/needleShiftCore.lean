import Mathlib
import Submission.Work.Drive.needleShift
import Submission.Work.Drive.polarDir_injOn_of_singleRay

/-!
# The core of the needle's flattening datum: one ray, and the angular velocity

The shifted needle pin `Work.Drive.NeedleShiftedFlatteningData` asks for
`Work.Drive.FlatteningData (fun t => needleFam r D lam δ₁ δ₂ ε (t + period/4))`, i.e. for a frame
`(u, v)` and a centre `c'` such that the projection `M := projectAlong w c N` of the needle along a
unit `w`

* is injective on one period (`hinj`) and regular (`hvel`),
* satisfies the planar frame identity about `c'` (`hplane`),
* avoids `c'` (`hne`), starts in the direction `(1,0)` (`h0`),
* has an injective direction map (`hdir`),
* has positive angular velocity (`hang`).

This module removes two of those clauses from the burden of the pin: **`hinj` follows from `hdir`**
(`hdir` is injectivity of a function of `M`, so `M t₁ = M t₂ ⟹ polarDir t₁ = polarDir t₂`), and
**`hvel` follows from `hang`** (the angular-velocity numerator is `(⟪M-c',u⟫⟪M',v⟫ - ⟪M-c',v⟫⟪M',u⟫)/ρ²`,
`Work.Drive.angVel_num_eq`, which vanishes as soon as `M' = 0`).

Moreover `hdir` itself is *not* an independent obligation: `Work.Drive.polarDir_injOn_of_singleRay`
derives it from `hang` together with the *single-ray* condition — the ray from `c'` in the direction
`u` is met only at the base parameter.  So the pin reduces to the **core datum**

* the frame and centre,
* `hplane`, `hne`, `h0`,
* `hsingle` (one ray), `hang` (positive angular velocity).

That is `Work.Drive.FlatteningCore`, and `Work.Drive.flatteningData_of_core` turns it into
`FlatteningData` (using smoothness and periodicity, which `Work.Drive.isCInfKnot_of_flatteningData`
consumes separately).  The corresponding pin is `Work.Drive.NeedleShiftedCore`, and
`Work.Drive.needleEnd_of_shiftedCore` is the needle end from it — the exact form
`Work.Drive.unknotted_of_avoidingArc_of_pins` consumes.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The derivative of the norm along a curve.**  For `Space`-valued `g` with `g t ≠ 0`,

    d/dt ‖g t‖ = ⟪g t, g' t⟫ / ‖g t‖.

(Mathlib has `HasDerivAt.norm_sq` but not the norm itself; the proof composes with `Real.sqrt`.) -/
lemma hasDerivAt_norm {g : ℝ → Space} {g' : Space} {t : ℝ} (h : HasDerivAt g g' t)
    (hg : g t ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖g s‖) (inner ℝ (g t) g' / ‖g t‖) t := by
  have hpos : 0 < ‖g t‖ := norm_pos_iff.mpr hg
  have hne : ‖g t‖ ^ 2 ≠ 0 := by positivity
  have hcomp : HasDerivAt (fun s : ℝ => Real.sqrt (‖g s‖ ^ 2))
      (1 / (2 * Real.sqrt (‖g t‖ ^ 2)) * (2 * inner ℝ (g t) g')) t :=
    (Real.hasDerivAt_sqrt hne).comp t h.norm_sq
  have hfun : (fun s : ℝ => Real.sqrt (‖g s‖ ^ 2)) = fun s : ℝ => ‖g s‖ := by
    ext s
    exact Real.sqrt_sq (norm_nonneg (g s))
  have hval : 1 / (2 * Real.sqrt (‖g t‖ ^ 2)) * (2 * inner ℝ (g t) g')
      = inner ℝ (g t) g' / ‖g t‖ := by
    rw [Real.sqrt_sq (norm_nonneg (g t))]
    field_simp
  rw [hfun, hval] at hcomp
  exact hcomp

/-- The derivative of `t ↦ ‖M t - c‖`. -/
lemma deriv_norm_sub_eq {M : ℝ → Space} {c : Space} {t : ℝ}
    (hM : DifferentiableAt ℝ M t) (hne : M t ≠ c) :
    deriv (fun s : ℝ => ‖M s - c‖) t = inner ℝ (M t - c) (deriv M t) / ‖M t - c‖ :=
  (hasDerivAt_norm (hM.hasDerivAt.sub_const c) (sub_ne_zero.mpr hne)).deriv

/-- **The derivative of a polar coordinate.**  With `ρ = ‖M t - c‖`,

    d/dt (⟪M t - c, u⟫/ρ) = (⟪M' t, u⟫ ρ - ⟪M t - c, u⟫ (⟪M t - c, M' t⟫/ρ)) / ρ². -/
lemma deriv_polarCoord_eq {M : ℝ → Space} {c u : Space} {t : ℝ}
    (hM : DifferentiableAt ℝ M t) (hne : M t ≠ c) :
    deriv (polarCoord M c u) t
      = (inner ℝ (deriv M t) u * ‖M t - c‖
          - inner ℝ (M t - c) u * (inner ℝ (M t - c) (deriv M t) / ‖M t - c‖))
        / ‖M t - c‖ ^ 2 := by
  have h1 : DifferentiableAt ℝ (fun s : ℝ => M s - c) t := hM.sub_const c
  have hρne : (fun s : ℝ => ‖M s - c‖) t ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hnum_diff : DifferentiableAt ℝ (fun s : ℝ => inner ℝ (M s - c) u) t :=
    h1.inner ℝ (differentiableAt_const u)
  have hρ_diff : DifferentiableAt ℝ (fun s : ℝ => ‖M s - c‖) t :=
    h1.norm ℝ (sub_ne_zero.mpr hne)
  have hnum' : deriv (fun s : ℝ => inner ℝ (M s - c) u) t = inner ℝ (deriv M t) u := by
    rw [deriv_inner_apply ℝ (f := fun s : ℝ => M s - c) (g := fun _ : ℝ => u) h1
      (differentiableAt_const u)]
    simp
  have hden' : deriv (fun s : ℝ => ‖M s - c‖) t = inner ℝ (M t - c) (deriv M t) / ‖M t - c‖ :=
    deriv_norm_sub_eq hM hne
  rw [show polarCoord M c u = fun s : ℝ => inner ℝ (M s - c) u / ‖M s - c‖ from rfl]
  rw [deriv_fun_div hnum_diff hρ_diff hρne, hnum', hden']

/-- **The angular-velocity numerator is the chart cross product.**  For `a = ⟪M · - c, u⟫/ρ` and
`b = ⟪M · - c, v⟫/ρ` (the two polar coordinates of `M` about `c`),

    a b' - b a' = (⟪M - c, u⟫ ⟪M', v⟫ - ⟪M - c, v⟫ ⟪M', u⟫) / ρ².

In particular it vanishes as soon as `M' = 0` — so the numerator is `hang` in its geometric form:
the cross product of the position and the velocity of `M` about `c`. -/
lemma angVel_num_eq {M : ℝ → Space} {c u v : Space} {t : ℝ}
    (hM : DifferentiableAt ℝ M t) (hne : M t ≠ c) :
    polarCoord M c u t * deriv (polarCoord M c v) t
      - polarCoord M c v t * deriv (polarCoord M c u) t
      = (inner ℝ (M t - c) u * inner ℝ (deriv M t) v
          - inner ℝ (M t - c) v * inner ℝ (deriv M t) u) / ‖M t - c‖ ^ 2 := by
  rw [deriv_polarCoord_eq hM hne (u := v), deriv_polarCoord_eq hM hne (u := u)]
  simp only [polarCoord]
  have hne0 : ‖M t - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  field_simp
  ring

/-- **A positive angular velocity forces a nonvanishing projected velocity.**  If the
angular-velocity numerator of `M` about `c` (in the frame `(u, v)`) is positive everywhere and `M`
avoids `c`, then `velocity M` never vanishes. -/
lemma velocity_ne_zero_of_angVel_pos {M : ℝ → Space} {c u v : Space}
    (hM : ∀ t : ℝ, DifferentiableAt ℝ M t) (hne : ∀ t : ℝ, M t ≠ c)
    (hpos : ∀ t : ℝ, 0 < polarCoord M c u t * deriv (polarCoord M c v) t
      - polarCoord M c v t * deriv (polarCoord M c u) t) :
    ∀ t : ℝ, velocity M t ≠ 0 := by
  intro t hzero
  have h := hpos t
  rw [angVel_num_eq (hM t) (hne t)] at h
  have hz : deriv M t = 0 := hzero
  rw [hz] at h
  simp at h

/-- **The core of the flattening datum.**  The same frame/centre data as `FlatteningData`, but with
the two *derived* clauses removed (`hinj` and `hvel`) and with the injectivity of the direction map
replaced by the (weaker) single-ray condition. -/
def FlatteningCore (N : ℝ → Space) : Prop :=
  ∃ w c c' u v : Space,
    ‖w‖ = 1 ∧
    ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
    (∀ t : ℝ, projectAlong w c N t - c' =
      inner ℝ (projectAlong w c N t - c') u • u +
      inner ℝ (projectAlong w c N t - c') v • v) ∧
    (∀ t : ℝ, projectAlong w c N t ≠ c') ∧
    polarDir (projectAlong w c N) c' u v 0 = (1, 0) ∧
    (∀ t : ℝ, 0 < t → t < period → polarDir (projectAlong w c N) c' u v t ≠ (1, 0)) ∧
    (∀ t : ℝ, 0 < polarCoord (projectAlong w c N) c' u t *
        deriv (polarCoord (projectAlong w c N) c' v) t -
      polarCoord (projectAlong w c N) c' v t *
        deriv (polarCoord (projectAlong w c N) c' u) t)

/-- **The core datum implies the flattening datum.** -/
theorem flatteningData_of_core {N : ℝ → Space} (hNsm : ContDiff ℝ cInfT N)
    (hNper : Function.Periodic N period) (h : FlatteningCore N) : FlatteningData N := by
  obtain ⟨w, c, c', u, v, hw, hu, hv, huv, hplane, hne, h0, hsingle, hpos⟩ := h
  have hMsm : ContDiff ℝ cInfT (projectAlong w c N) := projectAlong_smooth hNsm w c
  have hMper : Function.Periodic (projectAlong w c N) period := projectAlong_periodic hNper w c
  have hdir : Set.InjOn (polarDir (projectAlong w c N) c' u v) (Set.Ico (0 : ℝ) period) :=
    polarDir_injOn_of_singleRay hu hv huv hMsm hMper hplane hne h0 hsingle hpos
  have hinj : Set.InjOn (projectAlong w c N) (Set.Ico (0 : ℝ) period) := by
    intro t₁ h₁ t₂ h₂ heq
    refine hdir h₁ h₂ ?_
    simp only [polarDir, polarCoord]
    rw [heq]
  have hdM : ∀ t : ℝ, DifferentiableAt ℝ (projectAlong w c N) t := fun t =>
    (projectAlong_smooth hNsm w c).differentiable cInfT_ne_zero |>.differentiableAt
  have hvel : ∀ t : ℝ, velocity (projectAlong w c N) t ≠ 0 :=
    velocity_ne_zero_of_angVel_pos hdM hne hpos
  exact ⟨w, c, c', u, v, hw, hinj, hvel, hu, hv, huv, hplane, hne, h0, hdir, hpos⟩

/-- **The needle pin in core form.**  This is `Work.Drive.NeedleShiftedFlatteningData` with
`FlatteningData` replaced by `FlatteningCore`: the pin's remaining geometric content is one ray and
the angular velocity. -/
def NeedleShiftedCore (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
    ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
      0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
      FlatteningCore (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4))

/-- The shifted needle is `C^∞` and `period`-periodic (extracted from
`Work.Drive.sweepFam_contDiff_periodic`). -/
lemma contDiff_shiftedNeedle {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    ContDiff ℝ cInfT (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4)) :=
  ((sweepFam_contDiff_periodic hr.smooth.continuous D lam δ₁ δ₂ (ne_of_gt hδ₁)
    (ne_of_gt hδ₂)).2.2 ε).comp (contDiff_id.add contDiff_const)

lemma periodic_shiftedNeedle {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    Function.Periodic (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4)) period := by
  have hper : Function.Periodic (needleFam r D lam δ₁ δ₂ ε) period := fun t =>
    (sweepFam_contDiff_periodic hr.smooth.continuous D lam δ₁ δ₂ (ne_of_gt hδ₁)
      (ne_of_gt hδ₂)).2.1 ε t
  intro t
  show needleFam r D lam δ₁ δ₂ ε (t + period + period / 4)
    = needleFam r D lam δ₁ δ₂ ε (t + period / 4)
  rw [show t + period + period / 4 = (t + period / 4) + period by ring, hper]

/-- **The shifted core pin implies the shifted flattening pin.** -/
theorem needleShiftedFlatteningData_of_core {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (h : NeedleShiftedCore r D) : NeedleShiftedFlatteningData r D := by
  obtain ⟨ε₀, L, hε₀, hL, hmain⟩ := h
  refine ⟨ε₀, L, hε₀, hL, ?_⟩
  intro lam δ₁ δ₂ ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact flatteningData_of_core (contDiff_shiftedNeedle hr D h4 h6) (periodic_shiftedNeedle hr D h4 h6)
    (hmain lam δ₁ δ₂ ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

/-- **The needle end, from the shifted core pin.**  Same conclusion as
`Work.Drive.needleEnd_of_shiftedPin`. -/
theorem needleEnd_of_shiftedCore {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (h : NeedleShiftedCore r D) :
    ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
      ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
        0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0 :=
  needleEnd_of_shiftedPin hr D (needleShiftedFlatteningData_of_core hr D h)

end Work.Drive
