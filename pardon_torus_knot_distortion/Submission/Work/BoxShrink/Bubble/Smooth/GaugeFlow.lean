import Submission.Work.BoxShrink.Bubble.Smooth
import Submission.Work.BoxShrink.Bubble.Smooth.boxGauge
import Submission.Work.Smooth.Morse.Flow
import Submission.Work.BoxShrink.Bubble.Restricted

/-!
# Folding the box into the level function: the push-off from a gauge and one critical-value input

`Work.BoxShrink.Bubble.Smooth` proves the push-off for the smooth tori in the "plateau"
configurations, where the flow of the plane coordinate lands inside the box.  This file removes that
restriction, following `PLAN.md`: the box is **folded into the level function**.

Write `B := Submission.boxNorm c σ` (the box norm) and `g := Work.BoxShrink.Bubble.planeCoord c σ u`
(the plane coordinate), and let `gauge` be the smooth gauge of the box
(`Work.BoxShrink.Bubble.Smooth.boxGauge`: `ContDiff ℝ 2 gauge` and `B ≤ gauge ≤ B + δ`).  Put

  `auxFun gauge c σ u s = fun y => softMax (gauge y - s) (g y)`

where `softMax u v = (u + v)/2 + (√((u - v)² + 1) - 1)/2` is the *under-approximating* smooth maximum
(`max u v - 1/2 ≤ softMax u v ≤ max u v`, of class `C²`).  The two inclusions:

* `{h < -1/2} ∩ F ⊆ lowerRegion`: `h x < -1/2` gives `max (gauge x - s) (g x) < 0` (using the lower
  bound of the smooth max), hence `B x ≤ gauge x < s` (so `x ∈ PBox s c σ`) and `g x < 0` (so `x` is
  below the plane): `x ∈ boxRegion ∩ lowerHalf = lowerRegion`;
* `boxRegion ⊆ {h < b}` for every `b > δ` exceeding `g` on `boxRegion`: for `x ∈ boxRegion`,
  `gauge x - s ≤ B x + δ - s < δ < b` and `g x < b`, so `h x ≤ max (…) < b`.

Consequently, whenever the interval `[-1/2, b]` is **critical-value-free** for `h|_F`, the sibling
chapter's flow theorem `Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region` transports every loop
of `boxRegion` into `{h < -1/2} ⊆ lowerRegion` with the same winding vector, and
`Work.BoxShrink.Bubble.SlicePushOff` follows (`slicePushOff_of_gaugeSard`).  So the whole push-off
reduces to: the gauge (`boxGauge`, proved) plus the critical-value statement for the single explicit
smooth function `h` (Sard for `h|_F`) — neither the transversality of the plane nor a collar of the
slice is needed; both are absorbed by the gauge.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-! ## An under-approximating smooth maximum -/

/-- **The under-approximating smooth maximum**:
`softMax u v = (u + v)/2 + (√((u - v)² + 1) - 1)/2`. -/
noncomputable def softMax (u v : ℝ) : ℝ :=
  (u + v) / 2 + (Real.sqrt ((u - v) ^ 2 + 1) - 1) / 2

theorem softMax_le_max (u v : ℝ) : softMax u v ≤ max u v := by
  have h : Real.sqrt ((u - v) ^ 2 + 1) - 1 ≤ |u - v| := by
    have h0 : (u - v) ^ 2 + 1 ≤ (|u - v| + 1) ^ 2 := by
      have h00 : (u - v) ^ 2 = |u - v| ^ 2 := (sq_abs (u - v)).symm
      nlinarith [abs_nonneg (u - v), h00, sq_nonneg (|u - v|)]
    have h1 : Real.sqrt ((u - v) ^ 2 + 1) ≤ Real.sqrt ((|u - v| + 1) ^ 2) :=
      Real.sqrt_le_sqrt h0
    have h2 : Real.sqrt ((|u - v| + 1) ^ 2) = |u - v| + 1 := Real.sqrt_sq (by positivity)
    linarith
  have hmax : max u v = (u + v) / 2 + |u - v| / 2 := by
    rcases le_total u v with huv | huv
    · rw [max_eq_right huv, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left huv, abs_of_nonneg (by linarith)]; ring
  rw [softMax, hmax]; linarith

theorem max_sub_half_le_softMax (u v : ℝ) : max u v - 1 / 2 ≤ softMax u v := by
  have h : |u - v| ≤ Real.sqrt ((u - v) ^ 2 + 1) := by
    rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
    nlinarith [sq_abs (u - v)]
  have hmax : max u v = (u + v) / 2 + |u - v| / 2 := by
    rcases le_total u v with huv | huv
    · rw [max_eq_right huv, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left huv, abs_of_nonneg (by linarith)]; ring
  rw [softMax, hmax]; linarith

theorem contDiff_softMax : ContDiff ℝ 2 (fun p : ℝ × ℝ => softMax p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hpos : ((p.1 - p.2) ^ 2 + 1) ≠ 0 := by positivity
  have hinner : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 + 1) p := by fun_prop
  have hsqrt : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.sqrt ((q.1 - q.2) ^ 2 + 1)) p :=
    (Real.contDiffAt_sqrt hpos).comp p hinner
  have h2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (Real.sqrt ((q.1 - q.2) ^ 2 + 1) - 1) / 2) p :=
    (hsqrt.sub (contDiffAt_const (c := (1 : ℝ)))).div_const 2
  have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1 + q.2) / 2) p := by fun_prop
  have hres : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => softMax q.1 q.2) p := by
    have := h1.add h2
    simpa [softMax] using this
  exact hres

/-! ## The auxiliary function -/

/-- **The auxiliary function**: the smooth under-approximating maximum of the (shifted) gauge and the
plane coordinate. -/
noncomputable def auxFun (gauge : R3 → ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u s : ℝ) : R3 → ℝ :=
  fun y => softMax (gauge y - s) (planeCoord c σ u y)

theorem contDiff_auxFun {gauge : R3 → ℝ} (hgauge : ContDiff ℝ 2 gauge) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u s : ℝ) : ContDiff ℝ 2 (auxFun gauge c σ u s) := by
  have h1 : ContDiff ℝ 2 (fun y : R3 => gauge y - s) := hgauge.sub contDiff_const
  have h2 : ContDiff ℝ 2 (fun y : R3 => planeCoord c σ u y) := contDiff_planeCoord c σ u
  have h3 : ContDiff ℝ 2 (fun y : R3 => (gauge y - s, planeCoord c σ u y)) := h1.prodMk h2
  exact contDiff_softMax.comp h3

/-! ## The assembly: the push-off from the gauge and Sard -/

/-- **The push-off from the gauge and one critical-value statement.**

Let `gauge` be a `C²` gauge of the box (`B ≤ gauge ≤ B + δ`), let `b > δ` exceed the plane coordinate
on the region, and suppose that `[-1/2, b]` is critical-value-free for the auxiliary function
`h = auxFun gauge c σ u s`.  Then every loop of `boxRegion` is transported by the flow of `h` into
`{h < -1/2} ⊆ lowerRegion` with the same winding vector: `SlicePushOff` holds. -/
theorem slicePushOff_of_gaugeSard {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u δ b : ℝ} {gauge : R3 → ℝ}
    (hgauge : ContDiff ℝ 2 gauge)
    (hlo : ∀ y : R3, Submission.boxNorm c σ y ≤ gauge y)
    (hhi : ∀ y : R3, gauge y ≤ Submission.boxNorm c σ y + δ)
    (hb : 0 < b) (hδ : δ < b)
    (hbg : ∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
      planeCoord c σ u x < b)
    (hreg : ∀ t ∈ Set.Icc (-(1 / 2)) b,
      Work.Smooth.Morse.IsRegularValue ψ (auxFun gauge c σ u s) t) :
    SlicePushOff (Work.Smooth.Morse.torus ψ) s c σ u := by
  set h := auxFun gauge c σ u s with hh
  have hcont : ContDiff ℝ 2 h := contDiff_auxFun hgauge c σ u s
  have hab : (-(1 / 2) : ℝ) ≤ b := by linarith
  refine (Toolkit.subset_realizedWindings_iff).mpr ?_
  intro γ hγ
  -- the loop lies in `{h < b}`
  have hγb : ∀ t : ℝ, γ t ∈ Work.Smooth.Morse.region ψ h b := by
    intro t
    have hx : γ t ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ := hγ t
    have hB : Submission.boxNorm c σ (γ t) < s :=
      (Submission.mem_PBox_iff s c σ (γ t)).mp hx.2
    have hu : gauge (γ t) - s < b := by have := hhi (γ t); linarith
    have hv : planeCoord c σ u (γ t) < b := hbg (γ t) hx
    refine ⟨hx.1, ?_⟩
    show h (γ t) < b
    rw [hh]
    exact lt_of_le_of_lt (softMax_le_max _ _) (max_lt hu hv)
  -- the flow transports it into `{h < -1/2}`
  obtain ⟨γ', hγ', hhom⟩ := Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region ψ hcont hab
    hreg γ hγb
  refine ⟨γ', ?_, ?_⟩
  · intro t
    have hx := hγ' t
    have hmax : max (gauge (γ' t) - s) (planeCoord c σ u (γ' t)) < 0 := by
      have h1 := max_sub_half_le_softMax (gauge (γ' t) - s) (planeCoord c σ u (γ' t))
      rw [hh] at hx
      have h2 : softMax (gauge (γ' t) - s) (planeCoord c σ u (γ' t)) < -(1 / 2) := by
        have hmem : γ' t ∈ {x : R3 | softMax (gauge x - s) (planeCoord c σ u x) < -(1 / 2)} := by
          simpa only [auxFun] using hx.2
        exact hmem
      linarith
    have hu : gauge (γ' t) - s < 0 := lt_of_le_of_lt (le_max_left _ _) hmax
    have hv : planeCoord c σ u (γ' t) < 0 := lt_of_le_of_lt (le_max_right _ _) hmax
    have hB : Submission.boxNorm c σ (γ' t) < s := by have := hlo (γ' t); linarith
    refine Set.subset_union_right ?_
    refine (Work.BoxShrink.Core.mem_lowerRegion (P := Work.Smooth.Morse.torus ψ)).mpr
      ⟨hx.1, (Submission.mem_PBox_iff s c σ (γ' t)).mpr hB, ?_⟩
    have hv' := hv
    simp only [planeCoord] at hv'
    linarith
  · exact (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm

/-! ## The packaged form: the push-off from the Sard input alone -/

/-- **The push-off of the smooth case, from the gauge and one critical-value input.**

For every `ε > 0` the gauge exists (`Work.BoxShrink.Bubble.Smooth.boxGauge`); what is packaged here
is that, *given* any `C²` gauge of the box together with a `b` above the plane coordinate on the
region and the critical-value statement for the auxiliary function on `[-1/2, b]`, the push-off
holds.  This isolates the entire remaining content of `SlicePushOff` (and hence of the field
`Work.BoxShrink.Core.BubbleInput.bubble`) in a single Sard-type statement about the explicit smooth
function `auxFun gauge c σ u s ⊗ F`. -/
theorem smoothPushOff_of_sard {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∃ (δ b : ℝ) (gauge : R3 → ℝ),
      ContDiff ℝ 2 gauge ∧
        (∀ y : R3, Submission.boxNorm c σ y ≤ gauge y) ∧
        (∀ y : R3, gauge y ≤ Submission.boxNorm c σ y + δ) ∧
        0 < b ∧ δ < b ∧
        (∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
          planeCoord c σ u x < b) ∧
        (∀ t ∈ Set.Icc (-(1 / 2)) b,
          Work.Smooth.Morse.IsRegularValue ψ (auxFun gauge c σ u s) t)) :
    SlicePushOff (Work.Smooth.Morse.torus ψ) s c σ u := by
  obtain ⟨δ, b, gauge, hgauge, hlo, hhi, hb, hδ, hbg, hreg⟩ := h
  exact slicePushOff_of_gaugeSard (ψ := ψ) hgauge hlo hhi hb hδ hbg hreg

/-- **The field `bubble` of `Work.BoxShrink.Core.BubbleInput` for the smooth tori, from the
gauge-and-Sard input.** -/
noncomputable def bubbleSweep_of_sard {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∃ (δ b : ℝ) (gauge : R3 → ℝ),
      ContDiff ℝ 2 gauge ∧
        (∀ y : R3, Submission.boxNorm c σ y ≤ gauge y) ∧
        (∀ y : R3, gauge y ≤ Submission.boxNorm c σ y + δ) ∧
        0 < b ∧ δ < b ∧
        (∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
          planeCoord c σ u x < b) ∧
        (∀ t ∈ Set.Icc (-(1 / 2)) b,
          Work.Smooth.Morse.IsRegularValue ψ (auxFun gauge c σ u s) t)) :
    Work.BoxShrink.Core.BubbleSweep (Work.Smooth.Morse.torus ψ) s c σ u :=
  bubble_of_slicePushOff (smoothPushOff_of_sard (ψ := ψ) h)

/-! ## The honest state of the last mile

The packaged form `smoothPushOff_of_sard` / `bubbleSweep_of_sard` above takes the *existential*
triple `(δ, b, gauge)` together with the critical-value-freeness of `[-1/2, b]` as a **hypothesis**,
and that implication is sound: given such a triple, the flow of `auxFun` transports the loops of the
region into `lowerRegion`.

What is **not** established — and cannot be stated as an unconditional input — is that for every
configuration such a triple exists with that *fixed* left endpoint `-1/2`: when the box contains all
of the surface, `b` is forced above the maximum of `planeCoord` on the region, the auxiliary function
then attains a maximum there which is a critical value lying inside `[-1/2, b]`, and the final
conjunct fails.  (Thanks to the reviewer who found this: it is the reason the statement is recorded
here only as an implication.)

The correct last-mile target is the variant with a **variable** left endpoint `a < 0` and a smooth
maximum whose under-approximation error is tied to `a` (use
`softMaxEta u v = (u + v)/2 + (√((u - v)² + η²) - η)/2`, for which
`max u v - η/2 ≤ softMaxEta u v ≤ max u v`, with `η := -2a`): then `{h_a < a} ⊆ {max < 0} ⊆
lowerRegion` *and* the flow interval `[a, b]` may be chosen in the gap left by the critical values of
`h_a` below `0` (finitely many, by `Work.Smooth.Morse.LocallyFiniteCriticalValues ψ h_a`, none of them
`0` when `IsRegularValue ψ h_a 0`).  That is the statement to prove; `slicePushOff_of_gaugeSard`
below is its `η = 1/2`, `a = -1/2` instance and shows exactly how the pieces fit.
-/

end

end Work.BoxShrink.Bubble
