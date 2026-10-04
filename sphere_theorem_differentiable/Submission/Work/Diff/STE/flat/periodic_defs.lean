import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for the factorisation of a periodic smooth function

This module collects the auxiliary definitions used by
`Work.Diff.STE.flat.periodic_factor`: two cut-off functions on `ℝ`, two "angle" functions on `ℂ`
(read off from the two branches of the complex logarithm), and the resulting weights.

A smooth function `Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ` which is `1`-periodic in its real variables
is a smooth function of the characters `x ↦ exp (2 π i x j)`.  The construction of the factored
function `Ξ` is a finite partition-of-unity argument: for every choice `s : Fin n → Bool` of a
branch of the logarithm per coordinate one forms the composed function `Φ (thetaB s ·, ·)`, and the
weights `wB (s j)` interpolate between the two choices; the radial factor `kBump (‖z‖²)` kills the
artefacts near the origin, where the branch cuts meet, and equals `1` on the unit circle.
-/

namespace Work.Diff.STE.flat

noncomputable section

/-- Horizontal cut-off: `0` for `t ≤ -1/8`, `1` for `t ≥ 0`, smooth, with values in `[0,1]`. -/
def hBump (t : ℝ) : ℝ := Real.smoothTransition (8 * t + 1)

/-- Radial cut-off: `0` for `t ≤ 1/16`, `1` for `t ∈ [5/16, 2]`, `0` for `t ≥ 3`, with values
in `[0,1]`. -/
def kBump (t : ℝ) : ℝ :=
  Real.smoothTransition (4 * t - 1 / 4) * Real.smoothTransition (3 - t)

/-- The angle (in units of `2 π`) read off from the principal branch of the logarithm, which is
smooth on the slit plane `ℂ ∖ (-∞, 0]`.  On the unit circle, `exp (2 π i · thetaP z) = z`. -/
def thetaP (z : ℂ) : ℝ := (Complex.log z).im / (2 * Real.pi)

/-- The angle read off from the branch of the logarithm on `ℂ ∖ [0, ∞)`; on the unit circle,
`exp (2 π i · thetaM z) = z`. -/
def thetaM (z : ℂ) : ℝ := (Complex.log (-z)).im / (2 * Real.pi) + 1 / 2

/-- The angle function selected by the boolean `s` (`true` for the principal branch, `false` for
the branch on `ℂ ∖ [0, ∞)`). -/
def thetaB (s : Bool) (z : ℂ) : ℝ := if s then thetaP z else thetaM z

/-- The weight of the branch `s` at `z`. -/
def wB (s : Bool) (z : ℂ) : ℝ :=
  (if s then hBump z.re else 1 - hBump z.re) * kBump (‖z‖ ^ 2)

/-- `z` lies in the domain of smoothness of the branch `s`. -/
def good (s : Bool) (z : ℂ) : Prop := if s then z ∈ Complex.slitPlane else -z ∈ Complex.slitPlane

lemma hBump_zero {t : ℝ} (h : t ≤ -1 / 8) : hBump t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma hBump_one {t : ℝ} (h : 0 ≤ t) : hBump t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma hBump_nonneg (t : ℝ) : 0 ≤ hBump t := Real.smoothTransition.nonneg _

lemma hBump_le_one (t : ℝ) : hBump t ≤ 1 := Real.smoothTransition.le_one _

lemma kBump_zero_of_le {t : ℝ} (h : t ≤ 1 / 16) : kBump t = 0 := by
  have : 4 * t - 1 / 4 ≤ 0 := by linarith
  simp only [kBump, Real.smoothTransition.zero_of_nonpos this, zero_mul]

lemma kBump_zero_of_ge {t : ℝ} (h : 3 ≤ t) : kBump t = 0 := by
  have : 3 - t ≤ 0 := by linarith
  simp only [kBump, Real.smoothTransition.zero_of_nonpos this, mul_zero]

lemma kBump_one {t : ℝ} (h₁ : 5 / 16 ≤ t) (h₂ : t ≤ 2) : kBump t = 1 := by
  have h₁' : 1 ≤ 4 * t - 1 / 4 := by linarith
  have h₂' : 1 ≤ 3 - t := by linarith
  simp only [kBump, Real.smoothTransition.one_of_one_le h₁', Real.smoothTransition.one_of_one_le h₂',
    mul_one]

lemma kBump_nonneg (t : ℝ) : 0 ≤ kBump t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma kBump_le_one (t : ℝ) : kBump t ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (4 * t - 1 / 4)
  have h2 := Real.smoothTransition.le_one (3 - t)
  have h1' := Real.smoothTransition.nonneg (4 * t - 1 / 4)
  have h2' := Real.smoothTransition.nonneg (3 - t)
  simp only [kBump]
  nlinarith

@[simp] lemma thetaB_true (z : ℂ) : thetaB true z = thetaP z := rfl
@[simp] lemma thetaB_false (z : ℂ) : thetaB false z = thetaM z := rfl
@[simp] lemma good_true (z : ℂ) : good true z ↔ z ∈ Complex.slitPlane := Iff.rfl
@[simp] lemma good_false (z : ℂ) : good false z ↔ -z ∈ Complex.slitPlane := Iff.rfl

lemma wB_true (z : ℂ) : wB true z = hBump z.re * kBump (‖z‖ ^ 2) := rfl
lemma wB_false (z : ℂ) : wB false z = (1 - hBump z.re) * kBump (‖z‖ ^ 2) := rfl

end

end Work.Diff.STE.flat
