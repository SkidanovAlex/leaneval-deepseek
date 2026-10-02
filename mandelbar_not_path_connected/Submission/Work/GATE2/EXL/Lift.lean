/-
# GATE2 / EXL — the shape function of the ray lift, and (W) as a depth bound

The two remaining non-structural inputs of the ray route to the exit loop
(`Work.GATE2.EXL.exitLoop_at`) are

* the **confinement** `Re (gamma_1 (s_0 - 1 + t)) < -3/2` of the fundamental piece, and
* the **offset-avoidance** `(W)` along the lift piece.

Both are statements about the single `1`-periodic **shape function** of the lift

    f s := Re (gamma_1 s) - s,        f (s + 1) = f s

(`Work.ELRig.RayCylLift.per_1` and `Work.ELRig.periodicShift_translate`), which is why they are
isolated here as bounds on its oscillation over one period,

    liftOsc L := sSup (|f| '' [0,1]),      |f s| <= liftOsc L   for all s,

(`liftOsc`, `abs_re_sub_le_liftOsc`).

Consequences (all in `Work.ELRig.RayCylLift`'s vocabulary, with only `gamma_1`, `per_1`, `cont_1`):

* `lift_re_lt_of_crossing`: at a real crossing `gamma_1 s_0 = (y_0 : C)` one has
  `Re (gamma_1 (s_0 - 1 + t)) < C` for all `t in [0,1]` as soon as `y_0 + 2 * liftOsc L < C`.
  In particular the design's confinement follows from the leak centre being **deep**:
  `y_0 + 2 * liftOsc L < -3/2`.
* `lift_im_eq_zero_lt_of_osc`: the *relaxed* no-dip condition
  (`Im (gamma_1 (s_0 - 1 + t)) = 0 -> y_0 - 3/2 < Re (gamma_1 (s_0 - 1 + t))`), i.e. the only form
  of (W) that `Work.GATE2.EXL.exitLoop_exists` actually consumes, follows from the oscillation
  bound `liftOsc L < 1/4`.
* `lift_im_eq_zero_lt_of_osc_iota`: the same condition for the **second** lift: because
  `gamma_2 = conj gamma_1 + 1/2` (`RayCylLift.anti`), the `gamma_2`-condition at the centre
  `y_0 + 1/2` is *literally* the `gamma_1`-condition at `y_0`.

So the whole lift side of the exit loop is controlled by two inequalities on `liftOsc L` and the
depth of the leak centre.  The `RayCylLift` fields `anti`, `hPsi_1`, `hPsi_2`, `img_1`, `img_2`,
`hzne`, `hinj`, `tailId_1`, `tailId_2` are *not* used.
-/
import Submission.Work.GATE2.EXL.At

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

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The oscillation of the shape function of the ray lift** `s ↦ Re (gamma_1 s) - s` over one
period.  By `RayCylLift.per_1` the function is `1`-periodic, so its supremum over `[0,1]` controls
it everywhere (`abs_re_sub_le_liftOsc`). -/
noncomputable def liftOsc {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) : ℝ :=
  sSup ((fun s : ℝ => |(L.γ₁ s).re - s|) '' Set.Icc (0 : ℝ) 1)

theorem bddAbove_liftOsc {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) :
    BddAbove ((fun s : ℝ => |(L.γ₁ s).re - s|) '' Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.bddAbove_image
    (((Complex.continuous_re.comp L.cont₁).sub continuous_id).abs).continuousOn

/-- **The oscillation bound.**  `|Re (gamma_1 s) - s| <= liftOsc L` for **every** `s`, by the
`1`-periodicity of the shape function (`Work.ELRig.periodicShift_translate`). -/
theorem abs_re_sub_le_liftOsc {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) :
    |(L.γ₁ s).re - s| ≤ liftOsc L := by
  have hper := Work.ELRig.periodicShift_translate L.γ₁ L.per₁ ⌊s⌋ (Int.fract s)
  rw [Int.fract_add_floor] at hper
  have hre : (L.γ₁ s).re = (L.γ₁ (Int.fract s)).re + (⌊s⌋ : ℝ) := by
    rw [hper, Complex.add_re, Complex.intCast_re]
  have hs : s = Int.fract s + (⌊s⌋ : ℝ) := (Int.fract_add_floor s).symm
  have hkey : (L.γ₁ s).re - s = (L.γ₁ (Int.fract s)).re - Int.fract s := by
    linarith
  rw [hkey]
  exact le_csSup (bddAbove_liftOsc L)
    ⟨Int.fract s, ⟨Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩, rfl⟩

/-- The oscillation is nonnegative. -/
theorem liftOsc_nonneg {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) : 0 ≤ liftOsc L :=
  le_trans (abs_nonneg _) (abs_re_sub_le_liftOsc L 0)

/-- The upper bound of the shape function. -/
theorem lift_re_le {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) :
    (L.γ₁ s).re ≤ s + liftOsc L := by
  have h := abs_re_sub_le_liftOsc L s
  rw [abs_le] at h
  linarith [h.2]

/-- The lower bound of the shape function. -/
theorem lift_le_re {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) :
    s - liftOsc L ≤ (L.γ₁ s).re := by
  have h := abs_re_sub_le_liftOsc L s
  rw [abs_le] at h
  linarith [h.1]

/-- **Confinement from depth.**  If the real crossing `gamma_1 s_0 = (y_0 : C)` is deep enough that
`y_0 + 2 * liftOsc L < C`, then the whole fundamental piece `gamma_1 '' [s_0 - 1, s_0]` lies below
`C`.  With `C = -3/2` this is the confinement of the exit loop for the `alpha_1` tongue (and, since
`Re gamma_2 = Re gamma_1 + 1/2`, also for the `alpha_2` one). -/
theorem lift_re_lt_of_crossing {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {y₀ s₀ C : ℝ}
    (hγ : L.γ₁ s₀ = ((y₀ : ℝ) : ℂ)) (hconf : y₀ + 2 * liftOsc L < C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₁ (s₀ - 1 + t)).re < C := by
  intro t ht
  have h1 := lift_re_le L (s₀ - 1 + t)
  have h2 := lift_le_re L s₀
  have h3 : (L.γ₁ s₀).re = y₀ := by rw [hγ]; simp
  have ht1 : t ≤ 1 := ht.2
  linarith

/-- **The relaxed no-dip condition from a small oscillation.**  If the oscillation of the shape
function is below `1/4`, then at a real crossing `gamma_1 s_0 = (y_0 : C)` every *real* point of the
fundamental piece is above `y_0 - 3/2` — which is exactly the hypothesis that
`Work.GATE2.EXL.exitLoop_exists` consumes (the offset receives a `+1`, which is why the constant
is `3/2` and not `1/2`). -/
theorem lift_im_eq_zero_lt_of_osc {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {y₀ s₀ : ℝ}
    (hγ : L.γ₁ s₀ = ((y₀ : ℝ) : ℂ)) (hosc : liftOsc L < 1 / 4) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₁ (s₀ - 1 + t)).im = 0 →
      y₀ - 3 / 2 < (L.γ₁ (s₀ - 1 + t)).re := by
  intro t ht _
  have h1 := lift_le_re L (s₀ - 1 + t)
  have h2 := lift_re_le L s₀
  have h3 : (L.γ₁ s₀).re = y₀ := by rw [hγ]; simp
  have h3' : y₀ ≤ s₀ + liftOsc L := by rw [← h3]; exact h2
  have ht0 : 0 ≤ t := ht.1
  linarith

/-- **The relaxed no-dip condition for the second lift.**  Since `gamma_2 = conj gamma_1 + 1/2`
(`Work.ELRig.RayCylLift.anti`), `Im (gamma_2 s) = - Im (gamma_1 s)` and
`Re (gamma_2 s) = Re (gamma_1 s) + 1/2`, so the `gamma_2`-condition at the centre `y_0 + 1/2` is
*literally* the `gamma_1`-condition at `y_0`. -/
theorem lift_im_eq_zero_lt_of_osc_iota {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {y₀ : ℝ}
    (h : ∀ s : ℝ, (L.γ₁ s).im = 0 → y₀ - 3 / 2 < (L.γ₁ s).re) :
    ∀ s : ℝ, (L.γ₂ s).im = 0 → (y₀ + 1 / 2) - 3 / 2 < (L.γ₂ s).re := by
  intro s hs
  have him : (L.γ₁ s).im = 0 := by
    have := L.anti s
    have h2 : (L.γ₂ s).im = -(L.γ₁ s).im := by rw [this]; simp
    rw [h2] at hs; linarith
  have hre : (L.γ₂ s).re = (L.γ₁ s).re + 1 / 2 := by rw [L.anti s]; simp
  have := h s him
  linarith

end Work.GATE2.EXL
