import Submission.Work.Smooth.Plane.Jordan
import Submission.Work.Smooth.Jordan.unitCircle_isSimple

/-!
# `Work.Smooth.Plane.NullHomotopicAvoiding` is vacuous

This file records a **negative result** about the classical input of the sibling chapter
`Submission/Work/Smooth/Plane`:

> `Work.Smooth.Plane.NullHomotopicAvoiding c x` — "the loop `c` is null-homotopic in the complement
> of `x`" — is *satisfied by every continuous `c` and every `x` outside the trace of `c`*, because
> the definition imposes no condition at all on the intermediate loops `H (s, ·)`; the *cone
> homotopy* `H (s, t) = c (2π t (1 - s))` is a witness (its image is contained in the trace of `c`,
> hence avoids `x`).

Consequently the "hard direction of the Jordan curve theorem" in the chapter's datum
`Work.Smooth.Plane.PlaneJordanData` (`inside_not_nullHomotopic`) is false as stated, and
`Work.Smooth.Plane.PlaneJordanInput` is refutable: `not_planeJordanInput` below.

The intended notion — the loop is *essential* in `ℂ ∖ {x}` — is the homotopy of loops *relative to
the base point*: one must also require `H (s, 0) = H (s, 1)` for all `s` (the base point stays
fixed), i.e. that every intermediate loop is a loop.  With that correction the statement becomes
the classical one ("a simple closed curve winds around every interior point"), which is what
`Work.Smooth.Jordan.noFilling_of_mem_V` and `Work.Smooth.JordanSeparation.ind_eq_zero_of_avoiding_extension`
formalise; the correction is implemented in `Work.Smooth.Schoenflies.NullHomotopicRel` (see
`NullHomotopyRel.lean`).

## Main results

* `nullHomotopicAvoiding_of_notMem_range` — the cone homotopy;
* `not_nonempty_planeJordanData` — no curve has a `PlaneJordanData`;
* `not_planeJordanInput` — `Work.Smooth.Plane.PlaneJordanInput` is false.
-/

open Set

namespace Work.Smooth.Schoenflies

noncomputable section

open Work.Smooth.Plane

/-- **The cone homotopy witnesses `NullHomotopicAvoiding` for every point off the trace.**

For any continuous `c : ℝ → ℂ` and any `x` outside the range of `c`, the map
`H (s, t) = c (2π t (1 - s))` is a homotopy from the loop `t ↦ c (2π t)` to the constant loop at
`c 0` whose image lies in the trace of `c`, hence avoids `x`: so `NullHomotopicAvoiding c x` holds.

This shows that `NullHomotopicAvoiding` (as defined) only expresses that `x` is off the trace, and
not the essentiality of the loop. -/
theorem nullHomotopicAvoiding_of_notMem_range {c : ℝ → ℂ} (hc : Continuous c) {x : ℂ}
    (hx : x ∉ Set.range c) : NullHomotopicAvoiding c x := by
  refine ⟨⟨fun p : ArcInterval × ArcInterval =>
      c (2 * Real.pi * (p.2 : ℝ) * (1 - (p.1 : ℝ))), hc.comp (by fun_prop)⟩, ?_, ?_, ?_⟩
  · intro p
    exact fun h => hx ⟨_, h⟩
  · intro t
    show c (2 * Real.pi * (t : ℝ) * (1 - (0 : ℝ))) = c (2 * Real.pi * (t : ℝ))
    ring_nf
  · intro t
    show c (2 * Real.pi * (t : ℝ) * (1 - (1 : ℝ))) = c 0
    norm_num

/-- **No curve has a `PlaneJordanData`.**  The datum demands that no point of the open disc can be
contracted away from `c` (`inside_not_nullHomotopic`), but the cone homotopy contracts the loop away
from *every* point off its trace — in particular from the image under `e` of the centre of the disc,
which is off the trace by injectivity of `e` and the boundary condition. -/
theorem not_nonempty_planeJordanData (c : ℝ → ℂ) (hc : Continuous c) :
    ¬ Nonempty (PlaneJordanData c) := by
  rintro ⟨d⟩
  let z : Work.InnermostDisk.Disc :=
    ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩
  have hz : ‖(z : ℂ)‖ < 1 := by simp [z]
  have hx : d.e z ∉ Set.range c := by
    rintro ⟨θ, hθ⟩
    have h1 : d.e (Work.CoreTopology.circlePoint θ) = d.e z := by rw [d.boundary θ, hθ]
    have h2 : Work.CoreTopology.circlePoint θ = z := d.inj h1
    have h3 : ‖(z : ℂ)‖ = 1 := by
      rw [← h2, Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    exact absurd h3 (by linarith)
  exact d.inside_not_nullHomotopic z hz (nullHomotopicAvoiding_of_notMem_range hc hx)

/-- **`Work.Smooth.Plane.PlaneJordanInput` is false.**  The classical input of the planar
innermost-disc chapter quantifies over all continuous simple closed curves, but its datum is
uninhabited (`not_nonempty_planeJordanData`); the unit circle already witnesses this
(`Work.Smooth.Jordan.unitCircle_isSimple`).

Consequently any result of `Submission/Work/Smooth/Plane` stated from `PlaneJordanInput` as an
*explicit hypothesis* (e.g. `Work.Smooth.Plane.exists_spanningDisc_of_convex_planar`) is vacuous as
long as that hypothesis is `PlaneJordanInput`; the hypothesis must be replaced by the corrected
datum (`Work.Smooth.Schoenflies.RelNullHomotopic`), or by `Work.Smooth.Schoenflies.planeHypothesis`
(this chapter's unconditional planar Jordan–Schoenflies). -/
theorem not_planeJordanInput : ¬ PlaneJordanInput := by
  intro h
  have hsimple : Set.InjOn Work.Smooth.Jordan.unitCircle.toPlaneCurve.γ
      (Set.Ico 0 (2 * Real.pi)) := by
    simpa only [Work.Smooth.Jordan.PlaneCurve.IsSimple] using
      Work.Smooth.Jordan.unitCircle_isSimple
  exact not_nonempty_planeJordanData Work.Smooth.Jordan.unitCircle.toPlaneCurve.γ
    Work.Smooth.Jordan.unitCircle.toPlaneCurve.cont
    (h Work.Smooth.Jordan.unitCircle.toPlaneCurve.γ
      Work.Smooth.Jordan.unitCircle.toPlaneCurve.cont
      Work.Smooth.Jordan.unitCircle.toPlaneCurve.periodic hsimple)

end

end Work.Smooth.Schoenflies
