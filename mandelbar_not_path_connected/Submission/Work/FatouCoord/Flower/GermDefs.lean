/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower
import Submission.Work.FatouCoord.Petal.repelling_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Vocabulary for the ParabolicFlower construction in the normalized germ

We work with a *normalized* parabolic germ `f u = u + u ^ 2 * h u` with `h 0 = 1`
(`ParabolicBounds f h a r A A'`) together with an antiholomorphic square root `gU`
(`star ∘ gU` is holomorphic, `gU ∘ gU = f`, `gU 0 = 0`).

The parabolic chart is `W = -1/u` (so `u = -1/W`).  Everything geometric below is phrased in
the chart.

* `sgauge W = Re W + |Im W|` — the gauge of the *wide* sector of opening `3π/2` around the
  positive real axis (`sgauge W > M` is the sector).
* `WidePetal M = {u | u ≠ 0 ∧ M < sgauge (-1/u)}` — the corresponding wide petal in the
  dynamical plane.
* `gChart g W = -1 / g (-1 / W)` — the dynamics induced by an antiholomorphic square root `g`
  in the chart.
* `Window R T`, `Omega R T` — the two regions of the far left half-plane used for the
  repelling side: the *window* `-R-1 ≤ Re w < -R+1`, `|Im w| > T` (where the repelling
  coordinate is still controlled by the conjugacy `V`) and the far-left half-plane
  `Re w < -R`, `|Im w| > T`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Flower

noncomputable section

/-- The gauge of the wide sector: `sgauge W = Re W + |Im W|`.  The set `{M < sgauge W}` is the
sector of opening `3π/2` around the positive real axis. -/
def sgauge (W : ℂ) : ℝ := W.re + |W.im|

/-- The **wide petal** of level `M` in the germ plane: the set of `u ≠ 0` whose chart value
`W = -1/u` lies in the wide sector `M < sgauge W`. -/
def WidePetal (M : ℝ) : Set ℂ := {u : ℂ | u ≠ 0 ∧ M < sgauge (-1 / u)}

/-- The dynamics induced by a map `g` in the parabolic chart `W = -1/u`. -/
def gChart (g : ℂ → ℂ) (W : ℂ) : ℂ := -1 / g (-1 / W)

/-- The *window*: the strip of the chart plane just to the right of the half-plane
`{Re w < -R}`, restricted to large imaginary part. -/
def Window (R T : ℝ) : Set ℂ := {w : ℂ | -R - 1 ≤ w.re ∧ w.re < -R + 1 ∧ T < |w.im|}

/-- The far left half-plane with large imaginary part. -/
def Omega (R T : ℝ) : Set ℂ := {w : ℂ | w.re < -R ∧ T < |w.im|}

@[simp] theorem mem_sgauge (W : ℂ) : sgauge W = W.re + |W.im| := rfl

@[simp] theorem mem_WidePetal {M : ℝ} {u : ℂ} :
    u ∈ WidePetal M ↔ u ≠ 0 ∧ M < sgauge (-1 / u) := Iff.rfl

@[simp] theorem mem_gChart (g : ℂ → ℂ) (W : ℂ) : gChart g W = -1 / g (-1 / W) := rfl

@[simp] theorem mem_Window {R T : ℝ} {w : ℂ} :
    w ∈ Window R T ↔ -R - 1 ≤ w.re ∧ w.re < -R + 1 ∧ T < |w.im| := Iff.rfl

@[simp] theorem mem_Omega {R T : ℝ} {w : ℂ} :
    w ∈ Omega R T ↔ w.re < -R ∧ T < |w.im| := Iff.rfl

/-- `sgauge` is the maximum of the two real-linear forms `Re + Im` and `Re - Im`. -/
theorem sgauge_eq_max (W : ℂ) : sgauge W = max (W.re + W.im) (W.re - W.im) := by
  rw [sgauge]
  by_cases h : 0 ≤ W.im
  · rw [abs_of_nonneg h, max_eq_left]; linarith
  · have h' : W.im < 0 := lt_of_not_ge h
    have h2 : W.re + W.im ≤ W.re - W.im := by linarith
    rw [abs_of_neg h', max_eq_right h2]; ring

theorem convex_half₁ (M : ℝ) : Convex ℝ {W : ℂ | M < W.re + W.im} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hkey : (a • x + b • y).re + (a • x + b • y).im
      = a * (x.re + x.im) + b * (y.re + y.im) := by
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  rw [hkey]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy
  · have h5 : a * M < a * (x.re + x.im) := mul_lt_mul_of_pos_left hx hapos
    have h6 : b * M ≤ b * (y.re + y.im) := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    have h7 : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
    linarith

theorem convex_half₂ (M : ℝ) : Convex ℝ {W : ℂ | M < W.re - W.im} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hkey : (a • x + b • y).re - (a • x + b • y).im
      = a * (x.re - x.im) + b * (y.re - y.im) := by
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  rw [hkey]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy
  · have h5 : a * M < a * (x.re - x.im) := mul_lt_mul_of_pos_left hx hapos
    have h6 : b * M ≤ b * (y.re - y.im) := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    have h7 : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
    linarith

/-- The wide sector `{M < sgauge W}` is the union of the two half-planes `Re + Im > M` and
`Re - Im > M`, which are convex and meet. -/
theorem sgauge_gt_eq_union (M : ℝ) :
    {W : ℂ | M < sgauge W}
      = {W : ℂ | M < W.re + W.im} ∪ {W : ℂ | M < W.re - W.im} := by
  ext W
  rw [Set.mem_ofPred_eq, sgauge_eq_max, Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    lt_max_iff]

/-- The wide sector `{M < sgauge W}` is preconnected. -/
theorem isPreconnected_sgauge_gt (M : ℝ) : IsPreconnected {W : ℂ | M < sgauge W} := by
  rw [sgauge_gt_eq_union M]
  refine IsPreconnected.union ((M + 1 : ℝ) + 0 * Complex.I) ?_ ?_
    (convex_half₁ M).isPreconnected (convex_half₂ M).isPreconnected <;>
  · simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, sub_zero, Complex.ofReal_im, Complex.I_im, Complex.mul_im,
      add_zero, zero_mul]
    linarith

end

end Work.FatouCoord.Flower
