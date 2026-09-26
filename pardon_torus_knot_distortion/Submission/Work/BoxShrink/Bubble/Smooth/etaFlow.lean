import Submission.Work.BoxShrink.Bubble.Smooth.GaugeFlow
import Submission.Work.BoxShrink.Bubble.Smooth.curveSard

/-!
# The variable-endpoint auxiliary function

`Smooth/GaugeFlow.lean` proves the push-off from a *fixed* critical-value-free interval `[-1/2, b]`
for the auxiliary function `auxFun gauge c σ u s = softMax (gauge - s) (planeCoord c σ u)`.  That form
of the analytic input is **false** in one regime (documented there and in `PLAN.md`): when the box
contains the whole surface, `b` is forced above `max_F planeCoord`, and the maximum of the auxiliary
function on the compact surface is a critical value lying inside `[-1/2, b]`.

This file implements the corrected form: the under-approximating smooth maximum is parametrised by its
error `η`,

  `softMaxEta η u v = (u + v)/2 + (√((u - v)² + η²) - η)/2`,
  `max u v - η/2 ≤ softMaxEta η u v ≤ max u v`,

and, for the level `a < 0`, one takes `η := -2a`, so that the error `η/2 = -a` exactly closes the gap:
`{h_a < a}` implies `max (gauge - s) (planeCoord) < 0`, hence `h_a`'s sublevel set `{h_a < a}` is
contained in `upperRegion ∪ lowerRegion` — while the interval `[a, b]` no longer has to straddle the
maximum of `h_a`, because `a` may be chosen as close to `0` as the gap below the critical values of
`h_a` allows (see `PLAN.md` stretches 8–9).

**`slicePushOff_of_curveSardEta`** is the resulting statement: if for every closed curve `γ` of the
surface inside `boxRegion` there is a gauge, a level `a < 0` and a level `b > 0` with `b` above `h_a` on
`γ` and `[a, b]` critical-value-free for `h_a|_F`, then `SlicePushOff` holds — via the delegated
`Work.BoxShrink.Bubble.Smooth.curveSard`.  This is the last-mile statement in the exact form the flow
theorem consumes.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The error-parametrised under-approximating smooth maximum.** -/
noncomputable def softMaxEta (η u v : ℝ) : ℝ :=
  (u + v) / 2 + (Real.sqrt ((u - v) ^ 2 + η ^ 2) - η) / 2

theorem softMaxEta_le_max {η : ℝ} (hη : 0 ≤ η) (u v : ℝ) : softMaxEta η u v ≤ max u v := by
  have h : Real.sqrt ((u - v) ^ 2 + η ^ 2) - η ≤ |u - v| := by
    have h0 : (u - v) ^ 2 + η ^ 2 ≤ (|u - v| + η) ^ 2 := by
      have h00 : (u - v) ^ 2 = |u - v| ^ 2 := (sq_abs (u - v)).symm
      nlinarith [abs_nonneg (u - v), h00, sq_nonneg η]
    have h1 : Real.sqrt ((u - v) ^ 2 + η ^ 2) ≤ Real.sqrt ((|u - v| + η) ^ 2) :=
      Real.sqrt_le_sqrt h0
    have h2 : Real.sqrt ((|u - v| + η) ^ 2) = |u - v| + η := Real.sqrt_sq (by positivity)
    linarith
  have hmax : max u v = (u + v) / 2 + |u - v| / 2 := by
    rcases le_total u v with huv | huv
    · rw [max_eq_right huv, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left huv, abs_of_nonneg (by linarith)]; ring
  rw [softMaxEta, hmax]; linarith

theorem max_sub_half_le_softMaxEta {η : ℝ} (hη : 0 < η) (u v : ℝ) :
    max u v - η / 2 ≤ softMaxEta η u v := by
  have h : |u - v| ≤ Real.sqrt ((u - v) ^ 2 + η ^ 2) := by
    rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
    nlinarith [sq_abs (u - v), sq_nonneg η]
  have hmax : max u v = (u + v) / 2 + |u - v| / 2 := by
    rcases le_total u v with huv | huv
    · rw [max_eq_right huv, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left huv, abs_of_nonneg (by linarith)]; ring
  rw [softMaxEta, hmax]; linarith

theorem contDiff_softMaxEta {η : ℝ} (hη : η ≠ 0) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => softMaxEta η p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hη2 : 0 < η ^ 2 := by positivity
  have hpos : ((p.1 - p.2) ^ 2 + η ^ 2) ≠ 0 :=
    ne_of_gt (by nlinarith [sq_nonneg (p.1 - p.2)])
  have hinner : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 + η ^ 2) p := by fun_prop
  have hsqrt : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.sqrt ((q.1 - q.2) ^ 2 + η ^ 2)) p :=
    (Real.contDiffAt_sqrt hpos).comp p hinner
  have h2 : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => (Real.sqrt ((q.1 - q.2) ^ 2 + η ^ 2) - η) / 2) p :=
    (hsqrt.sub (contDiffAt_const (c := η))).div_const 2
  have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1 + q.2) / 2) p := by fun_prop
  have hres : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => softMaxEta η q.1 q.2) p := by
    have := h1.add h2
    simpa [softMaxEta] using this
  exact hres

/-- **The auxiliary function with the error tied to the level**: at level `a < 0` one takes `η = -2a`,
so that `{h < a}` implies `max (gauge - s) (planeCoord) < 0`. -/
noncomputable def auxFunEta (η : ℝ) (gauge : R3 → ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u s : ℝ) :
    R3 → ℝ :=
  fun y => softMaxEta η (gauge y - s) (planeCoord c σ u y)

theorem contDiff_auxFunEta {gauge : R3 → ℝ} (hgauge : ContDiff ℝ 2 gauge) {η : ℝ} (hη : η ≠ 0)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u s : ℝ) : ContDiff ℝ 2 (auxFunEta η gauge c σ u s) := by
  have h1 : ContDiff ℝ 2 (fun y : R3 => gauge y - s) := hgauge.sub contDiff_const
  have h2 : ContDiff ℝ 2 (fun y : R3 => planeCoord c σ u y) := contDiff_planeCoord c σ u
  have h3 : ContDiff ℝ 2 (fun y : R3 => (gauge y - s, planeCoord c σ u y)) := h1.prodMk h2
  exact (contDiff_softMaxEta hη).comp h3

/-- **The last-mile statement, in the form the flow theorem consumes.**

For every closed curve `γ` of the surface inside `boxRegion` there is a gauge of the box, a level
`a < 0` and a level `b > 0` such that the auxiliary function `auxFunEta (-2a) gauge c σ u s` is below
`b` on `γ` and the whole interval `[a, b]` is critical-value-free for it.  Under this single input the
push-off holds. -/
theorem slicePushOff_of_curveSardEta {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) →
      ∃ (δ a b : ℝ) (gauge : R3 → ℝ),
        ContDiff ℝ 2 gauge ∧
          (∀ y : R3, Submission.boxNorm c σ y ≤ gauge y) ∧
          (∀ y : R3, gauge y ≤ Submission.boxNorm c σ y + δ) ∧
          a < 0 ∧ 0 < b ∧
          (∀ t : ℝ, auxFunEta (-2 * a) gauge c σ u s (γ t) < b) ∧
          (∀ t ∈ Set.Icc a b,
            Work.Smooth.Morse.IsRegularValue ψ (auxFunEta (-2 * a) gauge c σ u s) t)) :
    SlicePushOff (Work.Smooth.Morse.torus ψ) s c σ u := by
  refine Smooth.curveSard (ψ := ψ) ?_
  intro γ hγ
  obtain ⟨δ, a, b, gauge, hg, hlo, -, ha, hb, hbγ, hreg⟩ := h γ hγ
  refine ⟨auxFunEta (-2 * a) gauge c σ u s, a, b,
    contDiff_auxFunEta hg (by linarith : (-2 * a) ≠ 0) c σ u s, ha, hb, ?_, hbγ, hreg⟩
  -- `{h_a < a}` is off the slice: it lies in the box region and below the plane
  intro x hxcar hxa
  have hη : 0 < -2 * a := by linarith
  have hmax : max (gauge x - s) (planeCoord c σ u x) < 0 := by
    have h1 := max_sub_half_le_softMaxEta (η := -2 * a) hη (gauge x - s) (planeCoord c σ u x)
    have h2 : softMaxEta (-2 * a) (gauge x - s) (planeCoord c σ u x) < a := hxa
    linarith
  have hu : gauge x - s < 0 := lt_of_le_of_lt (le_max_left _ _) hmax
  have hv : planeCoord c σ u x < 0 := lt_of_le_of_lt (le_max_right _ _) hmax
  have hB : Submission.boxNorm c σ x < s := by
    have hle := hlo x
    linarith
  refine Set.subset_union_right ?_
  refine (Work.BoxShrink.Core.mem_lowerRegion (P := Work.Smooth.Morse.torus ψ)).mpr
    ⟨hxcar, (Submission.mem_PBox_iff s c σ x).mpr hB, ?_⟩
  have hv' := hv
  simp only [planeCoord] at hv'
  linarith

/-- **The field `bubble` for the smooth tori, from the variable-endpoint input.** -/
noncomputable def bubbleSweep_of_curveSardEta {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) →
      ∃ (δ a b : ℝ) (gauge : R3 → ℝ),
        ContDiff ℝ 2 gauge ∧
          (∀ y : R3, Submission.boxNorm c σ y ≤ gauge y) ∧
          (∀ y : R3, gauge y ≤ Submission.boxNorm c σ y + δ) ∧
          a < 0 ∧ 0 < b ∧
          (∀ t : ℝ, auxFunEta (-2 * a) gauge c σ u s (γ t) < b) ∧
          (∀ t ∈ Set.Icc a b,
            Work.Smooth.Morse.IsRegularValue ψ (auxFunEta (-2 * a) gauge c σ u s) t)) :
    Work.BoxShrink.Core.BubbleSweep (Work.Smooth.Morse.torus ψ) s c σ u :=
  bubble_of_slicePushOff (slicePushOff_of_curveSardEta (ψ := ψ) h)

end

end Work.BoxShrink.Bubble
