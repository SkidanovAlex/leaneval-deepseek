import Mathlib
import Submission.Work.Smooth.SphereJordan.annulusCuts
import Submission.Work.Smooth.SphereJordan.annulusSchoenflies_of_plain

/-!
# The standard half-annuli, as explicit discs

This file sets up the explicit map

  `z ↦ u · (R z) · e^{i (Φ z)}`,  `(R z, Φ z) = ctr + ‖z‖ • (bdVec z - ctr)`

of the closed unit disc onto the closed half-annulus
`{z : 1/2 ≤ ‖z‖ ≤ 1, 0 ≤ Im (z/u)}` (`u = cutDir S`), whose boundary circle is mapped to the
parametrised boundary curve `srcUpB S` of
`Submission/Work/Smooth/SphereJordan/annulusInjectionTwoCutsAlt.lean`.

The construction is carried out in the *radial coordinates* `(R, Φ)` of the annulus: the four
boundary arcs of the half annulus correspond to the four sides of the rectangle
`upRect = [1/2,1] × [0,π]`, and the boundary correspondence is parametrised linearly in the angle
parameter.  `bdVec z` is the point of `∂upRect` in the direction of `z` (`z ≠ 0`), and
`radVec z` interpolates it linearly from the centre `ctr = (3/4, π/2)` with parameter `‖z‖`.
-/

open Set

namespace Work.SphereJordan

noncomputable section

open Work.Smooth.SphereJordan (perPt circlePoint srcUpB srcDnB cutDir)

/-- The rectangle `[1/2,1] × [0,π]` of radial coordinates of the **upper** half annulus. -/
def upRect : Set (ℝ × ℝ) := {p | 1/2 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ Real.pi}

/-- The rectangle of radial coordinates of the **lower** half annulus. -/
def dnRect : Set (ℝ × ℝ) := {p | 1/2 ≤ p.1 ∧ p.1 ≤ 1 ∧ -Real.pi ≤ p.2 ∧ p.2 ≤ 0}

/-- The boundary of `upRect`: the rectangle, with one coordinate at an endpoint. -/
def upRectBd : Set (ℝ × ℝ) :=
  {p | p ∈ upRect ∧ (p.1 = 1/2 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = Real.pi)}

/-- The centre of the rectangle, `(3/4, π/2)`. -/
def ctrUp : ℝ × ℝ := (3/4, Real.pi / 2)

/-- The linear interpolation of a radial-coordinate point from the centre with parameter `s`. -/
def segVec (p : ℝ × ℝ) (s : ℝ) : ℝ × ℝ := ctrUp + s • (p - ctrUp)

/-- The complex number `R · e^{iΦ}` of a pair of radial coordinates. -/
def toCplx (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)

/-- **The boundary point of the rectangle in the direction of `z`.**

For `z ≠ 0` this is the (unique) point of `∂upRect` on the ray from the centre `ctrUp` in the
direction of `z`; the four branches are the four sides of the rectangle, each parametrised linearly
in `arcsin (Im z / ‖z‖)`. -/
def bdVec (z : ℂ) : ℝ × ℝ :=
  if 0 ≤ z.im then
    (if 0 ≤ z.re then (1, 2 * Real.arcsin (z.im / ‖z‖))
     else (1 / 2 + Real.arcsin (z.im / ‖z‖) / Real.pi, Real.pi))
  else
    (if 0 ≤ z.re then (1 - Real.arcsin (-z.im / ‖z‖) / Real.pi, 0)
     else (1 / 2, Real.pi - 2 * Real.arcsin (-z.im / ‖z‖)))

/-- The radial coordinates of the image of `z`: the boundary point `bdVec z` pulled in from the
centre by the factor `‖z‖`. -/
def radVec (z : ℂ) : ℝ × ℝ := segVec (bdVec z) ‖z‖

/-- The (radius, angle) coordinates of the standard boundary curve of the upper half annulus. -/
def stdVec (τ : ℝ) : ℝ × ℝ :=
  let σ := perPt τ
  if σ ≤ Real.pi / 2 then (1, 2 * σ)
  else if σ ≤ Real.pi then (3 / 2 - σ / Real.pi, Real.pi)
  else if σ ≤ 3 * Real.pi / 2 then (1 / 2, 3 * Real.pi - 2 * σ)
  else (σ / Real.pi - 1, 0)

/-- The standard boundary curve of the upper half annulus, as a complex number. -/
def stdHalf (τ : ℝ) : ℂ := toCplx (stdVec τ)

/-- The standard boundary curve of the lower half annulus, as a complex number. -/
def stdHalfDn (τ : ℝ) : ℂ := -stdHalf τ

/-! ## Elementary facts -/

theorem toCplx_pair (a b : ℝ) :
    toCplx (a, b) = (a : ℂ) * Complex.exp ((b : ℂ) * Complex.I) := rfl

theorem segVec_apply (p : ℝ × ℝ) (s : ℝ) :
    segVec p s = (ctrUp.1 + s * (p.1 - ctrUp.1), ctrUp.2 + s * (p.2 - ctrUp.2)) := rfl

theorem radVec_fst (z : ℂ) : (radVec z).1 = 3 / 4 + ‖z‖ * ((bdVec z).1 - 3 / 4) := rfl

theorem radVec_snd (z : ℂ) :
    (radVec z).2 = Real.pi / 2 + ‖z‖ * ((bdVec z).2 - Real.pi / 2) := rfl

theorem segVec_zero (p : ℝ × ℝ) : segVec p 0 = ctrUp := by simp [segVec]

theorem segVec_one (p : ℝ × ℝ) : segVec p 1 = p := by simp [segVec]

/-- Multiplication of the direction by a positive scalar does not change the boundary point. -/
theorem bdVec_smul_pos (z : ℂ) {c : ℝ} (hc : 0 < c) : bdVec (c • z) = bdVec z := by
  have hnorm : ‖c • z‖ = c * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hre : (c • z).re = c * z.re := by rw [Complex.smul_re, smul_eq_mul]
  have him : (c • z).im = c * z.im := by rw [Complex.smul_im, smul_eq_mul]
  have h1 : c * z.im / (c * ‖z‖) = z.im / ‖z‖ := mul_div_mul_left _ _ hc.ne'
  have h2 : -(c * z.im) / (c * ‖z‖) = -z.im / ‖z‖ := by
    rw [neg_div, neg_div, mul_div_mul_left _ _ hc.ne']
  have hq : ∀ a : ℝ, (0 ≤ c * a) ↔ (0 ≤ a) := fun a => by
    constructor <;> intro h <;> nlinarith
  simp only [bdVec, hnorm, hre, him, h1, h2, hq]

end

end Work.SphereJordan
