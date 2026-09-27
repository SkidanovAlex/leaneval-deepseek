import Mathlib
import Submission.Work.KT.Fund.SpectralAux
import Submission.Work.KT.Fund.SpectralQ
import Submission.Work.KT.Fund.circleIntegral_inv_sub_eq_zero

/-!
# `Work.KT.Fund.spectral_unit_z`

The homotopy `z • 1 + t • (Proj b ρ * b)`, `‖z‖ = 1`, `t ∈ [0,1]`, consists of units.

The proof uses the contour-integral definition of the spectral projection `Proj b ρ`: for every
`ζ` with `ρ < ‖ζ‖` the element
`Q b ρ ζ = (2πi)⁻¹ ∮_{|w|=ρ} (ζ - w)⁻¹ (w - b)⁻¹ dw` (see `Work.KT.Fund.SpectralQ`)
satisfies `(ζ • 1 - b) * Q b ρ ζ = Proj b ρ` and `Q b ρ ζ * (ζ • 1 - b) = Proj b ρ`
(`Q_mul_left`, `Q_mul_right`).  Hence, writing `p = Proj b ρ` and `u = p * Q * p`, the element
`ζ • p - p * b * p` has the two-sided inverse `u` inside the corner `pAp`, and the Peirce
decomposition `ζ • 1 - p * b * p = ζ • (1 - p) + (ζ • p - p * b * p)` (with both off-diagonal
blocks zero) makes `ζ • 1 - p * b * p` a unit of `A`
(`isUnit_of_corner_inv`).  For `‖z‖ = 1` and `t > 0` the statement follows from
`z • 1 + t • (p * b) = (-t) • (ζ • 1 - p * b * p)` with `ζ = -(z / t)`, `‖ζ‖ = 1/t ≥ 1 > ρ`.
-/

namespace Work.KT.Fund

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

section Idem

variable {B : Type*} [Ring B] [Algebra ℂ B]

lemma idem_mul_one_sub {p : B} (hp : p * p = p) : p * (1 - p) = 0 := by
  rw [mul_sub, mul_one, hp, sub_self]

lemma one_sub_mul_idem {p : B} (hp : p * p = p) : (1 - p) * p = 0 := by
  rw [sub_mul, one_mul, hp, sub_self]

lemma one_sub_mul_one_sub {p : B} (hp : p * p = p) : (1 - p) * (1 - p) = 1 - p := by
  rw [sub_mul, one_mul, mul_sub, mul_one, hp, sub_self, sub_zero]

/-- **Peirce-decomposition unit criterion.**  If `p` is an idempotent, if `u` is a two-sided
inverse of the corner element `c • p - p * b * p` in the sense that
`(c • p - p * b * p) * u = p = u * (c • p - p * b * p)`, and if `u` lies in the corner `pAp`,
then `c • 1 - p * b * p` is a unit of `A` (with explicit inverse `c⁻¹ • (1 - p) + u`). -/
lemma isUnit_of_corner_inv {p b u : B} {c : ℂ} (hp : p * p = p) (hu : p * u * p = u)
    (h1 : (c • p - p * b * p) * u = p) (h2 : u * (c • p - p * b * p) = p)
    (hc : c ≠ 0) : IsUnit (c • 1 - p * b * p) := by
  have hp1 := idem_mul_one_sub hp
  have h1p := one_sub_mul_idem hp
  have h11 := one_sub_mul_one_sub hp
  have hu1 : (1 - p) * u = 0 := by
    have h : (1 - p) * u = (1 - p) * (p * u * p) := by rw [hu]
    rw [h, show (1 - p) * (p * u * p) = ((1 - p) * p) * u * p by simp only [mul_assoc],
      h1p, zero_mul, zero_mul]
  have hu2 : u * (1 - p) = 0 := by
    have h : u * (1 - p) = (p * u * p) * (1 - p) := by rw [hu]
    rw [h, show (p * u * p) * (1 - p) = p * u * (p * (1 - p)) by simp only [mul_assoc],
      hp1, mul_zero]
  have hcross1 : (c • (1 - p)) * u = 0 := by rw [smul_mul_assoc, hu1, smul_zero]
  have hcross2 : (c • p - p * b * p) * (1 - p) = 0 := by
    rw [sub_mul, smul_mul_assoc, hp1, smul_zero,
      show p * b * p * (1 - p) = p * b * (p * (1 - p)) by simp only [mul_assoc],
      hp1, mul_zero, sub_zero]
  have hcross3 : (1 - p) * (c • p - p * b * p) = 0 := by
    rw [mul_sub, mul_smul_comm, h1p, smul_zero,
      show (1 - p) * (p * b * p) = ((1 - p) * p) * b * p by simp only [mul_assoc],
      h1p, zero_mul, zero_mul, sub_zero]
  have hdecomp : c • 1 - p * b * p = c • (1 - p) + (c • p - p * b * p) := by
    rw [smul_sub]; abel
  have hAc : (c • (1 - p)) * (c⁻¹ • (1 - p)) = 1 - p := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul, h11]
  have hBc : (c⁻¹ • (1 - p)) * (c • (1 - p)) = 1 - p := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hc, one_smul, h11]
  have hD1 : (c • p - p * b * p) * (c⁻¹ • (1 - p)) = 0 := by
    rw [mul_smul_comm, hcross2, smul_zero]
  have hD2 : (c⁻¹ • (1 - p)) * (c • p - p * b * p) = 0 := by
    rw [smul_mul_assoc, hcross3, smul_zero]
  have hD3 : u * (c • (1 - p)) = 0 := by rw [mul_smul_comm, hu2, smul_zero]
  refine ⟨⟨c • 1 - p * b * p, c⁻¹ • (1 - p) + u, ?_, ?_⟩, rfl⟩
  · calc (c • 1 - p * b * p) * (c⁻¹ • (1 - p) + u)
        = (c • (1 - p) + (c • p - p * b * p)) * (c⁻¹ • (1 - p) + u) := by rw [hdecomp]
      _ = (c • (1 - p)) * (c⁻¹ • (1 - p)) + (c • p - p * b * p) * (c⁻¹ • (1 - p))
            + ((c • (1 - p)) * u + (c • p - p * b * p) * u) := by
            simp only [add_mul, mul_add]
      _ = 1 - p + 0 + (0 + p) := by rw [hAc, hD1, hcross1, h1]
      _ = 1 := by abel
  · calc (c⁻¹ • (1 - p) + u) * (c • 1 - p * b * p)
        = (c⁻¹ • (1 - p) + u) * (c • (1 - p) + (c • p - p * b * p)) := by rw [hdecomp]
      _ = (c⁻¹ • (1 - p)) * (c • (1 - p)) + u * (c • (1 - p))
            + ((c⁻¹ • (1 - p)) * (c • p - p * b * p) + u * (c • p - p * b * p)) := by
            simp only [add_mul, mul_add]
      _ = 1 - p + 0 + (0 + p) := by rw [hBc, hD3, hD2, h2]
      _ = 1 := by abel

end Idem

section Aux

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

lemma continuousOn_res (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) :
    ContinuousOn (fun w : ℂ => Res b w) (Metric.sphere 0 ρ) := by
  have hunits : ContinuousOn Ring.inverse {x : A | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous (fun w : ℂ => w • (1 : A) - b) :=
    (continuous_id.smul continuous_const).sub continuous_const
  have hmaps : Set.MapsTo (fun w : ℂ => w • (1 : A) - b) (Metric.sphere 0 ρ)
      {x : A | IsUnit x} := by
    intro w hw
    have hwρ : ‖w‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact hunit w (by rw [hwρ]) (by rw [hwρ]; exact le_of_lt hρlt)
  have h := hunits.comp hlin.continuousOn hmaps
  simpa only [Res, Function.comp_def] using h

lemma circleIntegrable_res (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) :
    CircleIntegrable (fun w : ℂ => Res b w) 0 ρ :=
  ContinuousOn.circleIntegrable (le_of_lt hρpos) (continuousOn_res b hρpos hρlt hunit)

lemma continuousOn_inv_sub_const {ρ : ℝ} (hρpos : 0 < ρ) {ζ : ℂ} (hζ : ρ < ‖ζ‖) :
    ContinuousOn (fun w : ℂ => (ζ - w)⁻¹) (Metric.sphere 0 ρ) := by
  refine ContinuousOn.inv₀ (continuous_const.sub continuous_id).continuousOn ?_
  intro w hw
  have hwρ : ‖w‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
  intro h
  have hwζ : w = ζ := (sub_eq_zero.mp h).symm
  rw [hwζ] at hwρ
  linarith

lemma circleIntegrable_inv_sub_const_smul_one {ρ : ℝ} (hρpos : 0 < ρ) {ζ : ℂ}
    (hζ : ρ < ‖ζ‖) :
    CircleIntegrable (fun w : ℂ => (ζ - w)⁻¹ • (1 : A)) 0 ρ :=
  ContinuousOn.circleIntegrable (le_of_lt hρpos)
    (ContinuousOn.smul (continuousOn_inv_sub_const hρpos hζ) continuousOn_const)

lemma circleIntegrable_inv_sub_const_smul_res (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) {ζ : ℂ} (hζ : ρ < ‖ζ‖) :
    CircleIntegrable (fun w : ℂ => (ζ - w)⁻¹ • Res b w) 0 ρ :=
  ContinuousOn.circleIntegrable (le_of_lt hρpos)
    (ContinuousOn.smul (continuousOn_inv_sub_const hρpos hζ)
      (continuousOn_res b hρpos hρlt hunit))

lemma circleIntegral_sub_inv_eq_zero {ρ : ℝ} (hρpos : 0 < ρ) {ζ : ℂ} (hζ : ρ < ‖ζ‖) :
    (∮ w in C(0, ρ), (ζ - w)⁻¹) = 0 := by
  have hfun : (fun w : ℂ => (ζ - w)⁻¹) = fun w : ℂ => (-1 : ℂ) * (w - ζ)⁻¹ := by
    funext w
    rw [show ζ - w = -(w - ζ) by ring, inv_neg, neg_eq_neg_one_mul]
  rw [hfun, circleIntegral.integral_const_mul, circleIntegral_inv_sub_eq_zero hρpos hζ, mul_zero]

lemma resolvent_pointwise_left (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) {ζ : ℂ} (hζ : ρ < ‖ζ‖) :
    ∀ w ∈ Metric.sphere (0 : ℂ) ρ,
      (ζ • 1 - b) * ((ζ - w)⁻¹ • Res b w) = Res b w + (ζ - w)⁻¹ • (1 : A) := by
  intro w hw
  have hwρ : ‖w‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
  have hu : IsUnit (w • 1 - b) := hunit w (by rw [hwρ]) (by rw [hwρ]; exact le_of_lt hρlt)
  have hwne : ζ - w ≠ 0 := by
    intro h
    have hwζ : w = ζ := (sub_eq_zero.mp h).symm
    rw [hwζ] at hwρ
    linarith
  have hmul : (w • 1 - b) * Res b w = 1 := by
    have h := Ring.mul_inverse_cancel (w • 1 - b) hu
    simpa only [Res] using h
  have hsplit : (ζ • 1 - b : A) = (ζ - w) • (1 : A) + (w • 1 - b) := by
    rw [sub_smul]
    abel
  calc (ζ • 1 - b) * ((ζ - w)⁻¹ • Res b w)
      = (ζ - w)⁻¹ • ((ζ • 1 - b) * Res b w) := by rw [mul_smul_comm]
    _ = (ζ - w)⁻¹ • (((ζ - w) • (1 : A) + (w • 1 - b)) * Res b w) := by rw [hsplit]
    _ = (ζ - w)⁻¹ • (((ζ - w) • (1 : A)) * Res b w + (w • 1 - b) * Res b w) := by rw [add_mul]
    _ = (ζ - w)⁻¹ • ((ζ - w) • Res b w + 1) := by
          rw [hmul]
          congr 1
          rw [smul_mul_assoc, one_mul]
    _ = Res b w + (ζ - w)⁻¹ • (1 : A) := by
          rw [smul_add, smul_smul, inv_mul_cancel₀ hwne, one_smul]

lemma resolvent_pointwise_right (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) {ζ : ℂ} (hζ : ρ < ‖ζ‖) :
    ∀ w ∈ Metric.sphere (0 : ℂ) ρ,
      ((ζ - w)⁻¹ • Res b w) * (ζ • 1 - b) = Res b w + (ζ - w)⁻¹ • (1 : A) := by
  intro w hw
  have hwρ : ‖w‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
  have hu : IsUnit (w • 1 - b) := hunit w (by rw [hwρ]) (by rw [hwρ]; exact le_of_lt hρlt)
  have hwne : ζ - w ≠ 0 := by
    intro h
    have hwζ : w = ζ := (sub_eq_zero.mp h).symm
    rw [hwζ] at hwρ
    linarith
  have hmul : Res b w * (w • 1 - b) = 1 := by
    have h := Ring.inverse_mul_cancel (w • 1 - b) hu
    simpa only [Res] using h
  have hsplit : (ζ • 1 - b : A) = (ζ - w) • (1 : A) + (w • 1 - b) := by
    rw [sub_smul]
    abel
  calc ((ζ - w)⁻¹ • Res b w) * (ζ • 1 - b)
      = (ζ - w)⁻¹ • (Res b w * (ζ • 1 - b)) := by rw [smul_mul_assoc]
    _ = (ζ - w)⁻¹ • (Res b w * ((ζ - w) • (1 : A) + (w • 1 - b))) := by rw [hsplit]
    _ = (ζ - w)⁻¹ • (Res b w * ((ζ - w) • (1 : A)) + Res b w * (w • 1 - b)) := by rw [mul_add]
    _ = (ζ - w)⁻¹ • ((ζ - w) • Res b w + 1) := by
          rw [hmul]
          congr 1
          rw [mul_smul_comm, mul_one]
    _ = Res b w + (ζ - w)⁻¹ • (1 : A) := by
          rw [smul_add, smul_smul, inv_mul_cancel₀ hwne, one_smul]

lemma Q_mul_left (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    {ζ : ℂ} (hζ : ρ < ‖ζ‖) :
    (ζ • 1 - b) * Q b ρ ζ = Proj b ρ := by
  have hR : (0 : ℝ) ≤ ρ := le_of_lt hρpos
  have hres := circleIntegrable_res b hρpos hρlt hunit
  have hscal := circleIntegrable_inv_sub_const_smul_one (A := A) hρpos hζ
  have hcirc := circleIntegrable_inv_sub_const_smul_res b hρpos hρlt hunit hζ
  have hzero : (∮ w in C(0, ρ), (ζ - w)⁻¹ • (1 : A)) = 0 := by
    rw [circleIntegral.integral_smul_const, circleIntegral_sub_inv_eq_zero hρpos hζ, zero_smul]
  calc (ζ • 1 - b) * Q b ρ ζ
      = (ζ • 1 - b) *
          ((2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (ζ - w)⁻¹ • Res b w) := by
          simp only [Q]
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          ((ζ • 1 - b) * ∮ w in C(0, ρ), (ζ - w)⁻¹ • Res b w) := by
          rw [mul_smul_comm]
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), (ζ • 1 - b) * ((ζ - w)⁻¹ • Res b w)) := by
          rw [← circleIntegral_const_mul (ζ • 1 - b)
            (fun w : ℂ => (ζ - w)⁻¹ • Res b w) 0 ρ hcirc]
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), (Res b w + (ζ - w)⁻¹ • (1 : A))) := by
          congr 1
          exact circleIntegral.integral_congr hR (resolvent_pointwise_left b hρpos hρlt hunit hζ)
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          ((∮ w in C(0, ρ), Res b w) + ∮ w in C(0, ρ), (ζ - w)⁻¹ • (1 : A)) := by
          rw [circleIntegral.integral_add hres hscal]
    _ = (2 * Real.pi * Complex.I)⁻¹ • CircA b ρ := by rw [hzero, add_zero, CircA]
    _ = Proj b ρ := by simp only [Proj, CircA]

lemma Q_mul_right (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    {ζ : ℂ} (hζ : ρ < ‖ζ‖) :
    Q b ρ ζ * (ζ • 1 - b) = Proj b ρ := by
  have hR : (0 : ℝ) ≤ ρ := le_of_lt hρpos
  have hres := circleIntegrable_res b hρpos hρlt hunit
  have hscal := circleIntegrable_inv_sub_const_smul_one (A := A) hρpos hζ
  have hcirc := circleIntegrable_inv_sub_const_smul_res b hρpos hρlt hunit hζ
  have hzero : (∮ w in C(0, ρ), (ζ - w)⁻¹ • (1 : A)) = 0 := by
    rw [circleIntegral.integral_smul_const, circleIntegral_sub_inv_eq_zero hρpos hζ, zero_smul]
  calc Q b ρ ζ * (ζ • 1 - b)
      = ((2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (ζ - w)⁻¹ • Res b w) * (ζ • 1 - b) := by
          simp only [Q]
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          ((∮ w in C(0, ρ), (ζ - w)⁻¹ • Res b w) * (ζ • 1 - b)) := by
          rw [smul_mul_assoc]
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), ((ζ - w)⁻¹ • Res b w) * (ζ • 1 - b)) := by
          rw [← circleIntegral_mul_const (ζ • 1 - b)
            (fun w : ℂ => (ζ - w)⁻¹ • Res b w) 0 ρ hcirc]
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), (Res b w + (ζ - w)⁻¹ • (1 : A))) := by
          congr 1
          exact circleIntegral.integral_congr hR (resolvent_pointwise_right b hρpos hρlt hunit hζ)
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          ((∮ w in C(0, ρ), Res b w) + ∮ w in C(0, ρ), (ζ - w)⁻¹ • (1 : A)) := by
          rw [circleIntegral.integral_add hres hscal]
    _ = (2 * Real.pi * Complex.I)⁻¹ • CircA b ρ := by rw [hzero, add_zero, CircA]
    _ = Proj b ρ := by simp only [Proj, CircA]

end Aux

theorem spectral_unit_z {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    (hidem : Proj b ρ * Proj b ρ = Proj b ρ) (hcomm : b * Proj b ρ = Proj b ρ * b) :
    ∀ (z : ℂ) (t : ℝ), ‖z‖ = 1 → 0 ≤ t → t ≤ 1 →
      IsUnit (z • 1 + t • (Proj b ρ * b)) := by
  intro z t hz ht0 ht1
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  rcases eq_or_lt_of_le ht0 with ht | htpos
  · rw [← ht, zero_smul, add_zero]
    refine ⟨⟨z • 1, z⁻¹ • 1, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hzne, one_smul]
    · rw [smul_mul_assoc, one_mul, smul_smul, inv_mul_cancel₀ hzne, one_smul]
  · set ζ : ℂ := -(z * (t : ℂ)⁻¹) with hζdef
    have htC : (t : ℂ) ≠ 0 := by
      intro h
      have hre := Complex.ofReal_re t
      rw [h] at hre
      simp at hre
      linarith [htpos]
    have hζne : ζ ≠ 0 := by
      rw [hζdef, neg_ne_zero]
      exact mul_ne_zero hzne (inv_ne_zero htC)
    have htn : ‖(t : ℂ)‖ = t := by
      have h2 : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      nlinarith [norm_nonneg (t : ℂ), htpos]
    have hζnorm : ‖ζ‖ = 1 / t := by
      rw [hζdef, norm_neg, norm_mul, hz, one_mul, norm_inv, htn, one_div]
    have hζgt : ρ < ‖ζ‖ := by
      rw [hζnorm]
      have h1t : (1 : ℝ) ≤ 1 / t := by
        rw [le_div_iff₀ htpos, one_mul]
        exact ht1
      linarith
    have hQl : (ζ • 1 - b) * Q b ρ ζ = Proj b ρ := Q_mul_left b hρpos hρlt hunit hζgt
    have hQr : Q b ρ ζ * (ζ • 1 - b) = Proj b ρ := Q_mul_right b hρpos hρlt hunit hζgt
    have hpbp : Proj b ρ * b * Proj b ρ = Proj b ρ * b := by
      rw [mul_assoc, hcomm, ← mul_assoc, hidem]
    have hQp : Proj b ρ * Q b ρ ζ = Q b ρ ζ * Proj b ρ := by
      rw [← hQr, mul_assoc, hQl, hQr]
    have hpζ : Proj b ρ * (ζ • 1 - b) = (ζ • 1 - b) * Proj b ρ := by
      rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, one_mul, hcomm]
    have hdecomp1 : ζ • Proj b ρ - Proj b ρ * b * Proj b ρ = Proj b ρ * (ζ • 1 - b) := by
      rw [mul_sub, mul_smul_comm, mul_one, hpbp]
    have hQpp : Proj b ρ * Q b ρ ζ * Proj b ρ = Q b ρ ζ * Proj b ρ := by
      rw [hQp, mul_assoc, hidem]
    have hpQual : Proj b ρ * (Proj b ρ * Q b ρ ζ * Proj b ρ) = Q b ρ ζ * Proj b ρ := by
      rw [show Proj b ρ * (Proj b ρ * Q b ρ ζ * Proj b ρ)
            = (Proj b ρ * Proj b ρ) * (Q b ρ ζ * Proj b ρ) by simp only [mul_assoc],
        hidem, ← mul_assoc, hQp, mul_assoc, hidem]
    have hu : Proj b ρ * (Proj b ρ * Q b ρ ζ * Proj b ρ) * Proj b ρ
        = Proj b ρ * Q b ρ ζ * Proj b ρ := by
      rw [show Proj b ρ * (Proj b ρ * Q b ρ ζ * Proj b ρ) * Proj b ρ
            = (Proj b ρ * Proj b ρ) * Q b ρ ζ * (Proj b ρ * Proj b ρ) by
            simp only [mul_assoc], hidem]
    have hu1 : (ζ • Proj b ρ - Proj b ρ * b * Proj b ρ) * (Proj b ρ * Q b ρ ζ * Proj b ρ)
        = Proj b ρ := by
      rw [hdecomp1, hpζ, mul_assoc, hpQual, ← mul_assoc, hQl, hidem]
    have hu2 : (Proj b ρ * Q b ρ ζ * Proj b ρ) * (ζ • Proj b ρ - Proj b ρ * b * Proj b ρ)
        = Proj b ρ := by
      rw [hQpp, hdecomp1,
        show (Q b ρ ζ * Proj b ρ) * (Proj b ρ * (ζ • 1 - b))
            = Q b ρ ζ * (Proj b ρ * Proj b ρ) * (ζ • 1 - b) by simp only [mul_assoc],
        hidem, mul_assoc, hpζ, ← mul_assoc, hQr, hidem]
    have hsc : (-(t : ℂ)) * ζ = z := by
      have h1 : (t : ℂ) * ζ = -z := by
        rw [hζdef, mul_neg]
        congr 1
        rw [← mul_assoc, mul_comm (t : ℂ) z, mul_assoc, mul_inv_cancel₀ htC, mul_one]
      rw [neg_mul, h1, neg_neg]
    have htsmul : t • (Proj b ρ * b) = (t : ℂ) • (Proj b ρ * b) := by
      rw [← algebraMap_smul (A := ℂ) t (Proj b ρ * b)]
      rfl
    have hw : z • 1 + t • (Proj b ρ * b)
        = (-(t : ℂ)) • (ζ • 1 - Proj b ρ * b * Proj b ρ) := by
      rw [smul_sub, smul_smul, hsc, neg_smul, hpbp, sub_neg_eq_add]
      simp only [htsmul]
    have htz : IsUnit ((-(t : ℂ)) • (1 : A)) := by
      refine ⟨⟨(-(t : ℂ)) • (1 : A), (-(t : ℂ))⁻¹ • (1 : A), ?_, ?_⟩, rfl⟩
      · rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ (neg_ne_zero.mpr htC), one_smul]
      · rw [smul_mul_assoc, one_mul, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr htC), one_smul]
    have hfac : (-(t : ℂ)) • (ζ • 1 - Proj b ρ * b * Proj b ρ)
        = ((-(t : ℂ)) • (1 : A)) * (ζ • 1 - Proj b ρ * b * Proj b ρ) := by
      rw [smul_mul_assoc, one_mul]
    rw [hw, hfac]
    exact IsUnit.mul htz (isUnit_of_corner_inv hidem hu hu1 hu2 hζne)

end

end Work.KT.Fund
