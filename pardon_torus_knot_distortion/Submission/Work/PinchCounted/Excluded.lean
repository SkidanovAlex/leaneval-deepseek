import Submission.Work.PinchCounted.Pardon3
import Submission.Work.PinchCounted.totalArcLength_le_two_mul_mul_diam
import Submission.Work.BoxShrink.Pinch.SphereTraceEssential

/-!
# What the counting excludes: the small box of the workshop's counterexample

Pardon's Lemma 3 conclusion fails at the standard round torus with the small box `s = 3/2`,
`c = 0`, `σ = swap 1 2`, `u = 0` (`Work.BoxShrink.Pinch.BubbleHalfRefuted`), so the counted form
`Work.BoxShrink.Pinch.CountingHalf` *must* have unsatisfiable hypotheses at that configuration —
otherwise it would be false.  This module proves exactly that, in the sharpest available form.

The mechanism is Pardon's Lemma 2, not the geometry of the box: the counting hypothesis at the box
sphere gives, through the innermost-disc argument (`Counting.sphereTrace_inessential_of_counts`),
that the sphere trace carries **no** essential loop.  But at that configuration the sphere trace
*does* carry an essential loop — the workshop's witness had been mis-analyzed:
`Work.BoxShrink.Pinch.sphereSet_threeHalves_essential` exhibits a curve of winding `(1,0)` inside
`sphereSet 0 (swap 1 2) (3/2)`.  Hence no counted configuration exists at those parameters.

Consequences recorded here:

* `no_counted_of_sphereTrace_essential` — the **general exclusion**: at *any* configuration whose box
  sphere trace carries an essential loop, there is no knot, distortion bound and pair of counts
  satisfying the hypotheses of the counted form.  Equivalently
  (`counted_iff_sphereTrace_inessential`): a configuration can carry the counted data only if its
  sphere trace is inessential;
* `no_counted_threeHalves` — the instance at the workshop's parameters, at the standard torus;
* `not_smoothHalfS_hypothesis_threeHalves` — the same configuration fails the *first hypothesis* of
  the endpoint-only form `Work.BoxShrink.Pinch.SmoothHalfS`, so it is not a counterexample to that
  form either (the correction recorded in `Refute.lean`, made precise).

The identity diffeomorphism `idDiffeo` is provided because the statements are about the standard
torus: `Work.Smooth.Morse.torus idDiffeo = Work.CoreTopology.standard` holds definitionally.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

/-! ## The identity diffeomorphism, and the standard torus -/

/-- The identity diffeomorphism of `ℝ³`. -/
def idDiffeo : Submission.Diffeo where
  toFun := id
  invFun := id
  smooth_toFun := contDiff_id
  smooth_invFun := contDiff_id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The surface of `idDiffeo` is the standard torus. -/
theorem torus_idDiffeo : Work.Smooth.Morse.torus idDiffeo = Work.CoreTopology.standard := rfl

/-- There is a diffeomorphism of `ℝ³` whose surface is the standard torus, so the statements below
are not vacuous. -/
theorem exists_diffeo_torus_eq_standard :
    ∃ ψ : Submission.Diffeo, Work.Smooth.Morse.torus ψ = Work.CoreTopology.standard :=
  ⟨idDiffeo, rfl⟩

/-! ## The general exclusion -/

/-- **No counted configuration exists at a level whose sphere trace is essential.**  If the box
sphere `sphereSet c σ s` carries an essential loop of the surface, then there are no `p`, `q`, `K`,
`d` satisfying the hypotheses of the counted form — the sphere trace is forced to be inessential by
Pardon's Lemma 2 (`Counting.sphereTrace_inessential_of_counts`).

This is the contrapuntal form of the counting bridge, and it is the precise sense in which
`Work.BoxShrink.Pinch.CountingHalf` is *not* refuted by the workshop's counterexample: its
hypotheses are unsatisfiable there. -/
theorem no_counted_of_sphereTrace_essential {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hess : (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s)) : False :=
  sphereTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall hs c σ hslice hcl hS hess

/-! ## The workshop's parameters -/

/-- **The counted hypotheses are unsatisfiable at the standard torus with `s = 3/2`, `c = 0`,
`σ = swap 1 2`** — the parameters of the workshop's counterexample to Pardon's Lemma 3.

At those parameters the sphere trace is essential
(`Work.BoxShrink.Pinch.sphereSet_threeHalves_essential`), which the counting hypothesis forbids. -/
theorem no_counted_threeHalves {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (hψ : Work.Smooth.Morse.torus ψ = Work.CoreTopology.standard)
    (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) y = 3 / 2})
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) (K.curve t) = 3 / 2}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) : False :=
  no_counted_of_sphereTrace_essential hp hq hc ψ K hd hbound himg hsmall hcl
    (by norm_num) 0 (Equiv.swap (1 : Fin 3) 2) hslice hS
    (by rw [hψ]; exact Work.BoxShrink.Pinch.sphereSet_threeHalves_essential)

/-- **The workshop's configuration also fails the first hypothesis of the endpoint-only form**: its
sphere trace carries an essential loop, so it is not a counterexample to
`Work.BoxShrink.Pinch.SmoothHalfS` (which assumes `¬ ContainsEssentialLoop (sphereSet c σ s)`).
This makes precise the correction recorded in `Refute.lean`: the *conclusion* of Pardon's Lemma 3
fails at those parameters, but the *uncounted* interface is not touched by them. -/
theorem not_smoothHalfS_hypothesis_threeHalves :
    ¬ (¬ Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap (1 : Fin 3) 2) (3 / 2))) :=
  fun h => h Work.BoxShrink.Pinch.sphereSet_threeHalves_essential

/-- **The same, for the surface of `idDiffeo`** (the standard torus): the counted hypotheses at the
workshop's parameters are unsatisfiable. -/
theorem no_counted_threeHalves_standard {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph idDiffeo.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus idDiffeo))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus idDiffeo)
      {y : R3 | Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) y = 3 / 2})
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) (K.curve t) = 3 / 2}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) : False :=
  no_counted_threeHalves hp hq hc idDiffeo rfl K hd hbound himg hsmall hcl hslice hS


/-! ## The quantitative constraint the counting puts on the knot

The counting of the crux is not only a hypothesis on the *trace*: together with the distortion bound
it constrains the *geometry* of the knot.  `Work.Sweep.IsDistortionBound K d` bounds the intrinsic
distance by the chord, so the total arclength of `K` is at most `2 d` times the diameter of its image
(`totalArcLength_le_two_mul_mul_diam`); and `countConst · d < m` (with `m = min p q = I(F,β)` at the
configuration of the crux) then forces

  `totalArcLength K < (2 m / countConst) · diam (range K.curve) = (m/75) · diam`.

In other words, **a counted configuration can only occur for a knot whose length-to-diameter ratio is
below `I(F,β)/75`**.  For the standard round torus with the standard `(p,q)` curve that ratio is
`≳ max(p,q)/2`, so no counted configuration exists there — the quantitative form of
`no_counted_threeHalves`.  (Turning that last step into a theorem needs the identification of the
total arclength of an arbitrary injective reparametrisation of a curve with the geometric length of
its image, which is the one piece of the reparametrisation calculus the workspace does not yet have;
it is *not* needed for the statements below, which are about the *given* parametrisation.) -/

/-- **The counting bounds the arclength of the knot.**  If `d` is a distortion bound for `K` and
`countConst · d < m`, then the total arclength of `K` is at most `(2m/countConst)` times the diameter
of its image — at the configuration of the crux, `(min p q / 75) · diam`. -/
theorem totalArcLength_lt_of_countedBound {K : Knot} {d m : ℝ} (hd : 0 < d)
    (h : Work.Sweep.IsDistortionBound K d)
    (hsmall : Submission.countConst * d < m) :
    totalArcLength K < (2 * m / Submission.countConst) * Metric.diam (Set.range K.curve) := by
  have hlen := totalArcLength_le_two_mul_mul_diam hd h
  have hcountConst : Submission.countConst = 150 := rfl
  have hdiam : 0 < Metric.diam (Set.range K.curve) := by
    have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_refl _, by positivity⟩
    have hpi : Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨Real.pi_pos.le, by have := Real.pi_pos; linarith⟩
    have hne : K.curve 0 ≠ K.curve Real.pi := fun hh => by
      have h01 : (0 : ℝ) = Real.pi := K.injOn h0 hpi hh
      linarith [Real.pi_pos]
    have hpos : 0 < dist (K.curve 0) (K.curve Real.pi) := dist_pos.mpr hne
    have hbdd : Bornology.IsBounded (Set.range K.curve) := by
      have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
      have himg : K.curve '' Set.Icc (0 : ℝ) (0 + 2 * Real.pi) = Set.range K.curve :=
        hper.image_Icc (by positivity) 0
      rw [← himg]
      exact ((isCompact_Icc (a := (0 : ℝ)) (b := 0 + 2 * Real.pi)).image
        K.smooth.continuous).isBounded
    exact lt_of_lt_of_le hpos
      (Metric.dist_le_diam_of_mem hbdd ⟨0, rfl⟩ ⟨Real.pi, rfl⟩)
  have hdm : d < m / Submission.countConst := by
    rw [hcountConst] at hsmall ⊢
    linarith
  calc totalArcLength K ≤ 2 * d * Metric.diam (Set.range K.curve) := hlen
    _ < 2 * (m / Submission.countConst) * Metric.diam (Set.range K.curve) := by
        have := mul_lt_mul_of_pos_right
          (show 2 * d < 2 * (m / Submission.countConst) by linarith) hdiam
        linarith
    _ = (2 * m / Submission.countConst) * Metric.diam (Set.range K.curve) := by ring

/-- **The criterion, in the form in which a configuration is excluded**: if the arclength of the
knot is at least `(2m/countConst)` times the diameter of its image, then no distortion bound `d` with
`countConst · d < m` can hold for it. -/
theorem not_isDistortionBound_of_length {K : Knot} {d m : ℝ} (hd : 0 < d)
    (hlarge : (2 * m / Submission.countConst) * Metric.diam (Set.range K.curve) ≤
      totalArcLength K)
    (hsmall : Submission.countConst * d < m) : ¬ Work.Sweep.IsDistortionBound K d :=
  fun h => absurd (totalArcLength_lt_of_countedBound hd h hsmall) (not_lt.mpr hlarge)


/-- **The exclusion reduced to a geometric input.**  If the knot of a counted configuration has
length-to-diameter ratio at least `min p q / countConst` (equivalently, if
`(2 min p q / countConst) · diam (range K.curve) ≤ totalArcLength K`), then *no* counted
configuration exists at those data: the counting forces the ratio to be *small*
(`totalArcLength_lt_of_countedBound`), while `IsDistortionBound K d` with `countConst · d < min p q`
rules it out.

This isolates the only geometric input the general exclusion needs: for the standard round torus with
the standard `(p,q)` curve the ratio is `≳ max(p,q)/2 ≥ min(p,q)/75`, so this hypothesis holds there
— but proving *that* from `range K.curve = range β.γ` requires the reparametrisation calculus
(see the note above), which is why the theorem below takes it as a hypothesis. -/
theorem no_counted_of_length_ratio {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 < d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hL : (2 * (Nat.min p q : ℝ) / Submission.countConst) *
        Metric.diam (Set.range K.curve) ≤ totalArcLength K) : False :=
  not_isDistortionBound_of_length hd hL hsmall hbound

end

end Work.PinchCounted
