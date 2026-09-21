import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddCurve.Free

/-!
# The free-tip interface of the odd case (`Work.OddVolterra.Free`)

## Why this file exists: the tip normalisation is an artefact

`Work.OddVolterra.CurveData` (and `Work.OddEnvelope.IsEnvelopeCurve`) contain the two
normalisations

`tendsto_x : Tendsto x (𝓝[>] 0) (𝓝 1)`,  `tendsto_y : Tendsto y (𝓝[>] 0) (𝓝 1)`,

i.e. they require the final body's tips to be exactly at `(±1, 0, …, 0)`.

**The paper's construction does not produce tips at `±1`.**  Two independent reasons, both
machine-relevant:

* `W3.tex` (end of the odd case) defines the profile on `[-r(0), R(0)]` where `R(0) = ρ(1)`,
  `r(0) = ρ(-1)` are the *inverted Radon data at the poles*
  (`R^{d+1}(0) + r^{d+1}(0) = Φ_h(0)`, `R^d(0) - r^d(0) = Ψ_h(0)`), and only claims that `R, r`
  are *close to* `1` in `C²`;
* in the formalisation, the reconstruction is `ρ_new u = rhoNew R r u` where `(R, r)` solves the
  two-power system with the *glued* data `A = GlueA`, `B = GlueB`.  The tip is
  `ρ_new 1 = R 0`, and

      `u²(ρ_new u ^ (2n+2) + ρ_new (-u) ^ (2n+2)) = 2 * radonInverse n (GlueF n ρ_a) u`

  with `GlueF` = the anchor's datum below `|u| = 4/5` and the ball's above.  `radonInverse` is
  *downward local* (`Work.OddCurve.LowSlope.radonInverse_congr_of_eqOn`: the value at `u` is
  determined by the datum on `(0, u]`), so `radonInverse (GlueF) 1` sees the anchor's datum on
  the *gap* `(tStar, 4/5)` and is **not** `radonInverse ballPhiData 1 = 1`.  Equivalently, in the
  reformulation of `NOTES_CRUX_2026.md` §1, `GlueA 0 = 2 * eta 1` with
  `eta = radonInverse n (GlueF - ballPhiData)` the Abel inversion of the gap-supported deviation,
  which is *generically nonzero* (of size `O(M)`, `M ~ 2·10⁻⁶` for `n = 1`).  So `R 0 ≠ 1`.

The tip field is therefore a **false hypothesis**, not a normalisation: `LowSlopeThree`,
`CurveData`, `curve_data_three` and the whole `Hex` interface of the project are unprovable as
stated, although the *curves* they describe exist.

## What replaces it

The workspace already carries the correct interface, `Work.OddCurve.Free.IsEnvelopeCurveFree`
(same fields, with `∃ a > 0, Tendsto x (𝓝[>] 0) (𝓝 a)` in place of `Tendsto x (𝓝[>] 0) (𝓝 1)`),
together with `isEnvelopeCurveFree_of_isEnvelopeCurve` (the old interface implies the new one),
and the endgame `Submission.Odd.OddFamilyData` already accepts a profile on an arbitrary
`[-R₁, R₂]`.  This file adds the pieces of the *bridge* that the TIP is used for, so that a
free-tip curve is enough.

## What actually uses the tip

Of the whole analytic bridge, only two derived facts use `tendsto_one`:

* the chord equalities `f (y u) = u * y u + h u`, `f (-(x u)) = -(u * (-(x u)) + h u)` for
  `u ∈ (0,1]` (`Work.OddEnvelope.IsEnvelopeCurve` ⟹ `IsChordCurve` ⟹ `slopeRight` surjectivity);
* `f = semicircle` on the *middle* `(-tStar, tStar)`
  (`Work.OddVolterra.Bridge.envelopeProfile_eq_semicircle_of_tail`).

Neither is used by the two row identities themselves (`Work.OddVolterra.RowIdentity.odd_rowF`
takes the chord equalities and the middle-semicircle fact as *hypotheses*); they are only used by
the packaging lemmas `Work.OddBridge.{rowF,rowH,contF,contH,harik}_of_curveData`.  Both are
available for free tips: `Work.OddCurve.Free.momentEqsOn_Ioc_one_of_smallSlopes_free` performs
exactly the free-tip version of the tail argument.  So the relaxation is a re-plumbing of those
five files, not new mathematics.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Free

open Work.OddVolterra Commons.Geometry.Ulam

noncomputable section

/-- **The transition-slope curve, free tips.**  `CurveData` with the two tip normalisations
replaced by "the curve has *some* positive limit at `0⁺`".  These limits are the tips of the
body, `ρ(-1)` and `ρ(1)`; they are `1 + O(ε)` but not `1`. -/
structure CurveDataFree (n : ℕ) (h : ℝ → ℝ) (x y : ℝ → ℝ) : Prop where
  /-- `x` is smooth on `(0,∞)`. -/
  smooth_x : ContDiffOn ℝ ∞ x (Set.Ioi 0)
  /-- `y` is smooth on `(0,∞)`. -/
  smooth_y : ContDiffOn ℝ ∞ y (Set.Ioi 0)
  /-- `x` is strictly decreasing. -/
  deriv_x_neg : ∀ s : ℝ, 0 < s → deriv x s < 0
  /-- `y` is strictly decreasing. -/
  deriv_y_neg : ∀ s : ℝ, 0 < s → deriv y s < 0
  /-- `x` is positive on `(0,∞)`. -/
  pos_x : ∀ s : ℝ, 0 < s → 0 < x s
  /-- `y` is positive on `(0,∞)`. -/
  pos_y : ∀ s : ℝ, 0 < s → 0 < y s
  /-- The first three derivatives of `h` are small. -/
  close_h : ∀ s : ℝ, |h s| ≤ 1 / 100 ∧ |deriv h s| ≤ 1 / 100 ∧
    |deriv (deriv h) s| ≤ 1 / 100
  /-- The left tip `ρ(-1)`: *some* positive limit, not necessarily `1`. -/
  tendsto_x_free : ∃ a : ℝ, 0 < a ∧ Filter.Tendsto x (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 a)
  /-- The right tip `ρ(1)`: *some* positive limit, not necessarily `1`. -/
  tendsto_y_free : ∃ b : ℝ, 0 < b ∧ Filter.Tendsto y (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 b)
  /-- Beyond the perturbation window the curve is the semicircle's chord function. -/
  tail_x : ∀ s : ℝ, 1 - tau ≤ s → x s = profileX s
  /-- Beyond the perturbation window the curve is the semicircle's chord function. -/
  tail_y : ∀ s : ℝ, 1 - tau ≤ s → y s = profileX s
  /-- `C²`-closeness of `x` to the semicircle's chord function. -/
  close_x : ∀ s : ℝ, 0 < s → |x s - profileX s| ≤ 1 / 100 ∧
    |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
    |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100
  /-- `C²`-closeness of `y` to the semicircle's chord function. -/
  close_y : ∀ s : ℝ, 0 < s → |y s - profileX s| ≤ 1 / 100 ∧
    |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
    |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100
  /-- The paper's system `(hah44)` on the slopes `(0,1)`. -/
  volterra : VolterraEqOn n h x y (Set.Ioo 0 1)


/-- **The correct bump class for the odd case.**  The odd construction consumes the anchor's
profile up to order `n + 1` (the spherical-Radon reconstruction differentiates the datum `n - 1`
times), and the curve's `C^k`-closeness costs `‖h‖_{C^{n+1+k}}`; for `k ≤ n + 1` that is
`‖h‖_{C^{2n+2}}`.  The class `IsSmallFlatBumpThree` (`C^{n+3}`), which is what
`CurveData`'s `C²`-closeness needs, is *not* enough: with `C^{n+3}` the statement is false for
`n ≥ 2` (see `NOTES_free_tips.md` §4 and `Work.OddCurve/LowSlope/NOTES_anchor_left_dev_close_class.md`).

The deliverable's `ε` is existential, so raising the order costs nothing to the caller
(`Submission/Odd` can produce the bump with `exists_odd_bump (2*n+2)`); it is a documented
deviation from the request's prose (`|h| ≤ ε`, `|h'| ≤ ε`), of the same kind as, and required by,
the `C^{n+3}` one. -/
def IsSmallFlatBumpClass (n K : ℕ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) h ∧ Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau) ∧
    (∀ k : ℕ, k ≤ K → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0)

/-- `IsSmallFlatBumpClass` at order `n + 3` is `IsSmallFlatBumpThree` (definitionally). -/
theorem isSmallFlatBumpClass_three_iff (n : ℕ) (ε : ℝ) (h : ℝ → ℝ) :
    IsSmallFlatBumpClass n (n + 3) ε h ↔ Existence.IsSmallFlatBumpThree n ε h :=
  Iff.rfl

/-- The tip-normalised `CurveData` gives the free-tip one. -/
theorem curveDataFree_of_curveData {n : ℕ} {h x y : ℝ → ℝ}
    (hd : CurveData n h x y) : CurveDataFree n h x y where
  smooth_x := hd.smooth_x
  smooth_y := hd.smooth_y
  deriv_x_neg := hd.deriv_x_neg
  deriv_y_neg := hd.deriv_y_neg
  pos_x := hd.pos_x
  pos_y := hd.pos_y
  close_h := hd.close_h
  tendsto_x_free := ⟨1, one_pos, hd.tendsto_x⟩
  tendsto_y_free := ⟨1, one_pos, hd.tendsto_y⟩
  tail_x := hd.tail_x
  tail_y := hd.tail_y
  close_x := hd.close_x
  close_y := hd.close_y
  volterra := hd.volterra


/-- **The untruncated envelope profile.**  `Work.OddEnvelope.envelopeProfile` equals
`envelopeRight h y` only on `(0,1)` and is `0` outside `[-1,1]`; with free tips the right branch
is needed up to `y 0⁺ = ρ(1)`, which may exceed `1`, so the truncation is *wrong* there.

`envProfileFree h x y t` is `envelopeRight h y t` for `t > 0`, `envelopeLeft h x t` for `t < 0`
and `1` at `t = 0` (the value at the single point `0` is a convention: the body's waist radius,
and it is what makes `Nondegenerate` immediate).  On the cutting section `(-x s, y s)` — the only
place the moment integrals sample it — this *is* the envelope of the curve, because
`slopeRight y t` is the unique slope with `y σ = t` for every `t ∈ (0, y 0⁺)`. -/
def envProfileFree (h x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < t then Work.OddEnvelope.envelopeRight h y t
  else if t < 0 then Work.OddEnvelope.envelopeLeft h x t
  else 1

/-- **Anti-vacuity is free of the tip question.**  At slope `1` the section is
`(-profileX 1, profileX 1) ∋ 0`, the envelope profile is `1` at `0` (by its definition), and the
cutting line is `t ↦ t` there — so the radicand is `1 - (h 1)² = 1 > 0`.  Nothing about the tips
is used; the `tendsto_one` fields of `IsEnvelopeCurve` were never needed for
`Nondegenerate`. -/
theorem nondegenerate_of_free {n : ℕ} {h x y : ℝ → ℝ} (hd : CurveDataFree n h x y)
    (h1 : h 1 = 0) : Nondegenerate h x y (Work.OddEnvelope.envelopeProfile h x y) := by
  refine ⟨1, by norm_num, 0, ⟨?_, ?_⟩, ?_⟩
  · exact neg_lt_zero.mpr (hd.pos_x 1 (by norm_num))
  · exact hd.pos_y 1 (by norm_num)
  · have hb : x 1 = profileX 1 := hd.tail_x 1 (by norm_num [tau])
    have hb' : y 1 = profileX 1 := hd.tail_y 1 (by norm_num [tau])
    have hprof : Work.OddEnvelope.envelopeProfile h x y 0 = 1 := by
      simp [Work.OddEnvelope.envelopeProfile]
    simp only [psi, line, hprof, h1]
    norm_num


/-- On `(-1,1)` the untruncated profile and the truncated one agree. -/
theorem envProfileFree_eq_envelopeProfile {h x y : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    envProfileFree h x y t = Work.OddEnvelope.envelopeProfile h x y t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [envProfileFree, if_neg (not_lt.mpr (le_of_lt h)), if_pos h,
      Work.OddEnvelope.envelopeProfile_of_neg ⟨ht.1, h⟩]
  · subst h
    rw [envProfileFree, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0),
      Work.OddEnvelope.envelopeProfile_zero]
  · rw [envProfileFree, if_pos h, Work.OddEnvelope.envelopeProfile_of_pos ⟨h, ht.2⟩]

/-- **The corrected Step 3** (Ryabogin's spherical-Radon step), free tips: from an envelope
curve for `h` satisfying the two moment equations on the transition window, produce one
satisfying them on all slopes `0 < s ≤ 1`, with the tips left free.

This is `Work.OddVolterra.Existence.LowSlopeThree` with `IsEnvelopeCurve` replaced by
`Work.OddCurve.Free.IsEnvelopeCurveFree`.  The remaining false field is thereby removed; what is
left is the genuine content of the paper's Step 3 (see the module docstring and
`Free/NOTES_free_tips.md`). -/
def LowSlopeThreeFree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ, Existence.IsSmallFlatBumpThree n ε h →
    Work.OddEnvelope.IsEnvelopeCurve h X Y →
    Work.OddCurve.LowSlope.CloseToProfileX X → Work.OddCurve.LowSlope.CloseToProfileX Y →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
    ∃ x y : ℝ → ℝ,
      Work.OddCurve.Free.IsEnvelopeCurveFree h x y ∧
        Work.OddCurve.LowSlope.CloseToProfileX x ∧
        Work.OddCurve.LowSlope.CloseToProfileX y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
            Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)

end

end Work.OddVolterra.Free
