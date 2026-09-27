import Mathlib
import Submission.Work.KT.Fund.spectral_split

/-!
# `Work.KT.Fund.spectral_split_out`

The "outside" companion of the spectral splitting `Work.KT.Fund.spectral_split`.

For `b` a matrix of continuous complex-valued functions on a compact Hausdorff space `X` whose
pointwise spectrum avoids the unit circle (i.e. `z • 1 + b x` is invertible for every `x` and
every `z` with `‖z‖ = 1`), the spectral projection `E = Proj b ρ` onto the part of the spectrum
inside a small circle of radius `ρ < 1` is an idempotent matrix of continuous functions commuting
with `b`, the "inside" part `E b` has all of its spectrum inside the open unit disc
(`spectral_unit_z`), and the "outside" part splits off:

* `(1 - E) b + E` is a unit (`spectral_unit_d`), and
* `(t z) • (1 - E) + (1 - E) b + E` is a unit for every `t ∈ [0,1]` and `‖z‖ = 1`.

The third statement is the new content here.  Writing `Q = 1 - E` and `c = t z`, the element is
`Q * (b + c • 1) + E`.  The Peirce-decomposition unit criterion `isUnit_of_mul_eq_idem` (a
generalisation of the algebraic core of `spectral_unit_d`) reduces it to exhibiting an element
`X` with `(b + c • 1) * X = X * (b + c • 1) = Q`.  Such an `X` is produced by two complementary
arguments:

* if `ρ ≤ ‖c‖`, then `-c` lies in the annulus `ρ ≤ ‖·‖ ≤ 1`, so `z • 1 - b` is a unit at
  `z = -c`, i.e. `b + c • 1` is a unit of `A`;  take `X = (b + c • 1)⁻¹ * Q`;
* if `‖c‖ < ρ`, the contour integral
  `X = -(2πi)⁻¹ ∮_{|w| = ρ} (w + c)⁻¹ (w - b)⁻¹ dw`
  converges (the pole `-c` lies inside the circle) and the pointwise resolvent identity
  `(b + c) (w + c)⁻¹ (w - b)⁻¹ = (w - b)⁻¹ - (w + c)⁻¹` plus `∮_{|w| = ρ} (w + c)⁻¹ dw = 2πi`
  give the required two-sided relation `(b + c • 1) X = X (b + c • 1) = 1 - Proj b ρ`.
-/

namespace Work.KT.Fund

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-! ## The Peirce-decomposition unit criterion -/

/-- **Peirce unit criterion (abstract).**  If `e` is an idempotent of a ring and `a`, `t` satisfy
`a * t = t * a = e`, then `e * a + (1 - e)` is a unit (with two-sided inverse
`e * t + (1 - e)`).  This is the algebraic core of `Work.KT.Fund.spectral_unit_d`. -/
theorem isUnit_of_mul_eq_idem {A : Type*} [Ring A] {e a t : A}
    (he : e * e = e) (h1 : a * t = e) (h2 : t * a = e) :
    IsUnit (e * a + (1 - e)) := by
  have hae : a * e = e * a := by
    calc a * e = a * (t * a) := by rw [h2]
      _ = (a * t) * a := by noncomm_ring
      _ = e * a := by rw [h1]
  have hte : t * e = e * t := by
    calc t * e = t * (a * t) := by rw [h1]
      _ = (t * a) * t := by noncomm_ring
      _ = e * t := by rw [h2]
  have hea : e * a * e = e * a := by
    calc e * a * e = e * (a * e) := by noncomm_ring
      _ = e * (e * a) := by rw [hae]
      _ = (e * e) * a := by noncomm_ring
      _ = e * a := by rw [he]
  have het : e * t * e = e * t := by
    calc e * t * e = e * (t * e) := by noncomm_ring
      _ = e * (e * t) := by rw [hte]
      _ = (e * e) * t := by noncomm_ring
      _ = e * t := by rw [he]
  have heP : e * (1 - e) = 0 := by
    have h : e * (1 - e) = e - e * e := by noncomm_ring
    rw [h, he, sub_self]
  have hPe : (1 - e) * e = 0 := by
    have h : (1 - e) * e = e - e * e := by noncomm_ring
    rw [h, he, sub_self]
  have hee : (1 - e) * (1 - e) = 1 - e := by
    have h : (1 - e) * (1 - e) = 1 - e - e + e * e := by noncomm_ring
    rw [h, he]; abel
  have hmainL : e * a * e * t = e := by
    calc e * a * e * t = (e * a) * t := by rw [hea]
      _ = e * (a * t) := by noncomm_ring
      _ = e * e := by rw [h1]
      _ = e := by rw [he]
  have he1P : e * a * (1 - e) = 0 := by
    have h : e * a * (1 - e) = e * a - e * a * e := by noncomm_ring
    rw [h, hea, sub_self]
  have hP1e : (1 - e) * e * t = 0 := by rw [hPe, zero_mul]
  have hmainR : e * t * e * a = e := by
    calc e * t * e * a = (e * t) * a := by rw [het]
      _ = e * (t * a) := by noncomm_ring
      _ = e * e := by rw [h2]
      _ = e := by rw [he]
  have het1P : e * t * (1 - e) = 0 := by
    have h : e * t * (1 - e) = e * t - e * t * e := by noncomm_ring
    rw [h, het, sub_self]
  have hP1a : (1 - e) * e * a = 0 := by rw [hPe, zero_mul]
  refine ⟨⟨e * a + (1 - e), e * t + (1 - e), ?_, ?_⟩, rfl⟩
  · have h : (e * a + (1 - e)) * (e * t + (1 - e))
        = e * a * e * t + e * a * (1 - e) + (1 - e) * e * t + (1 - e) * (1 - e) := by
      noncomm_ring
    rw [h, hmainL, he1P, hP1e, hee]; abel
  · have h : (e * t + (1 - e)) * (e * a + (1 - e))
        = e * t * e * a + e * t * (1 - e) + (1 - e) * e * a + (1 - e) * (1 - e) := by
      noncomm_ring
    rw [h, hmainR, het1P, hP1a, hee]; abel

/-! ## The contour-integral relations for the perturbed element `b + c` -/

/-- **The contour integral giving the "outside inverse" of `b + c`.**  For `‖c‖ < ρ` the pole
`-c` lies strictly inside the circle `|w| = ρ`, and the weighted contour integral of the resolvent
of `b` is a right inverse of `b + c • 1` modulo the projection `1 - Proj b ρ`:

  `(b + c • 1) * (-(2πi)⁻¹ ∮_{|w|=ρ} (w + c)⁻¹ (w - b)⁻¹ dw) = 1 - Proj b ρ`. -/
theorem out_contour_mul_left {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    {c : ℂ} (hc : ‖c‖ < ρ) :
    (b + c • 1) * (-(2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (w + c)⁻¹ • Res b w)
      = 1 - Proj b ρ := by
  have hρle : 0 ≤ ρ := le_of_lt hρpos
  have hsphere : ∀ w : ℂ, w ∈ Metric.sphere (0:ℂ) ρ → ‖w‖ = ρ := by
    intro w hw; rw [Metric.mem_sphere, dist_zero_right] at hw; exact hw
  have hwne : ∀ w ∈ Metric.sphere (0:ℂ) ρ, w + c ≠ 0 := by
    intro w hw h
    have hwr : ‖w‖ = ρ := hsphere w hw
    have hw' : w = -c := add_eq_zero_iff_eq_neg.mp h
    rw [hw', norm_neg] at hwr
    linarith
  have hcont_inv : ContinuousOn (fun w : ℂ => (w + c)⁻¹) (Metric.sphere (0:ℂ) ρ) :=
    ContinuousOn.inv₀ (continuous_id.add continuous_const).continuousOn (fun w hw => hwne w hw)
  have hcont_res : ContinuousOn (fun w : ℂ => Res b w) (Metric.sphere (0:ℂ) ρ) :=
    continuousOn_res b hρpos hρlt hunit
  have hres_int : CircleIntegrable (fun w : ℂ => Res b w) 0 ρ := hcont_res.circleIntegrable hρle
  have hscal_int : CircleIntegrable (fun w : ℂ => (w + c)⁻¹ • (1 : A)) 0 ρ :=
    (hcont_inv.smul continuousOn_const).circleIntegrable hρle
  have hcirc_int : CircleIntegrable (fun w : ℂ => (w + c)⁻¹ • Res b w) 0 ρ :=
    (hcont_inv.smul hcont_res).circleIntegrable hρle
  have hone : (∮ w in C(0, ρ), (w + c)⁻¹) = 2 * Real.pi * Complex.I := by
    have hmem : (-c) ∈ Metric.ball (0:ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_neg]; exact hc
    have h := circleIntegral.integral_sub_inv_of_mem_ball (c := (0:ℂ)) (R := ρ) (w := -c) hmem
    simpa only [sub_neg_eq_add] using h
  have hpt : ∀ w ∈ Metric.sphere (0:ℂ) ρ,
      (b + c • 1) * ((w + c)⁻¹ • Res b w) = Res b w - (w + c)⁻¹ • (1 : A) := by
    intro w hw
    have hwr : ‖w‖ = ρ := hsphere w hw
    have hunitw : IsUnit (w • 1 - b) :=
      hunit w (le_of_eq hwr.symm) (by rw [hwr]; exact le_of_lt hρlt)
    have hw0 : w + c ≠ 0 := hwne w hw
    have key : (b + c • 1) * Res b w = (w + c) • Res b w - 1 := by
      have hb := mul_res_bY b hunitw
      have hc1 : (c • (1 : A)) * Res b w = c • Res b w := by rw [smul_mul_assoc, one_mul]
      rw [add_mul, hb, hc1, add_smul]
      abel
    rw [mul_smul_comm, key, smul_sub, smul_smul, inv_mul_cancel₀ hw0, one_smul]
  have hR : (∮ w in C(0,ρ), (w + c)⁻¹ • (1:A)) = (2 * Real.pi * Complex.I) • (1:A) := by
    rw [circleIntegral.integral_smul_const, hone]
  have hsne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  calc (b + c • 1) * (-(2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (w + c)⁻¹ • Res b w)
      = -(2 * Real.pi * Complex.I)⁻¹ •
          ((b + c • 1) * ∮ w in C(0, ρ), (w + c)⁻¹ • Res b w) := by
        rw [mul_smul_comm]
    _ = -(2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), (b + c • 1) * ((w + c)⁻¹ • Res b w)) := by
        rw [circleIntegral_const_mul (b + c • 1) (fun w => (w + c)⁻¹ • Res b w) 0 ρ hcirc_int]
    _ = -(2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), (Res b w - (w + c)⁻¹ • (1:A))) := by
        congr 1
        exact circleIntegral.integral_congr hρle hpt
    _ = -(2 * Real.pi * Complex.I)⁻¹ •
          ((∮ w in C(0,ρ), Res b w) - ∮ w in C(0,ρ), (w + c)⁻¹ • (1:A)) := by
        rw [circleIntegral.integral_sub hres_int hscal_int]
    _ = -(2 * Real.pi * Complex.I)⁻¹ • (CircA b ρ - (2 * Real.pi * Complex.I) • (1:A)) := by
        rw [hR]; rfl
    _ = 1 - Proj b ρ := by
        have hw : (2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I) = 1 :=
          inv_mul_cancel₀ hsne
        rw [smul_sub, smul_smul,
          show (-(2 * Real.pi * Complex.I)⁻¹) * (2 * Real.pi * Complex.I) = -1 by
            rw [neg_mul, hw],
          neg_one_smul, Proj, neg_smul]
        abel

/-- **The contour integral giving the "outside inverse" of `b + c`, right-hand version.** -/
theorem out_contour_mul_right {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    {c : ℂ} (hc : ‖c‖ < ρ) :
    (-(2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (w + c)⁻¹ • Res b w) * (b + c • 1)
      = 1 - Proj b ρ := by
  have hρle : 0 ≤ ρ := le_of_lt hρpos
  have hsphere : ∀ w : ℂ, w ∈ Metric.sphere (0:ℂ) ρ → ‖w‖ = ρ := by
    intro w hw; rw [Metric.mem_sphere, dist_zero_right] at hw; exact hw
  have hwne : ∀ w ∈ Metric.sphere (0:ℂ) ρ, w + c ≠ 0 := by
    intro w hw h
    have hwr : ‖w‖ = ρ := hsphere w hw
    have hw' : w = -c := add_eq_zero_iff_eq_neg.mp h
    rw [hw', norm_neg] at hwr
    linarith
  have hcont_inv : ContinuousOn (fun w : ℂ => (w + c)⁻¹) (Metric.sphere (0:ℂ) ρ) :=
    ContinuousOn.inv₀ (continuous_id.add continuous_const).continuousOn (fun w hw => hwne w hw)
  have hcont_res : ContinuousOn (fun w : ℂ => Res b w) (Metric.sphere (0:ℂ) ρ) :=
    continuousOn_res b hρpos hρlt hunit
  have hres_int : CircleIntegrable (fun w : ℂ => Res b w) 0 ρ := hcont_res.circleIntegrable hρle
  have hscal_int : CircleIntegrable (fun w : ℂ => (w + c)⁻¹ • (1 : A)) 0 ρ :=
    (hcont_inv.smul continuousOn_const).circleIntegrable hρle
  have hcirc_int : CircleIntegrable (fun w : ℂ => (w + c)⁻¹ • Res b w) 0 ρ :=
    (hcont_inv.smul hcont_res).circleIntegrable hρle
  have hone : (∮ w in C(0, ρ), (w + c)⁻¹) = 2 * Real.pi * Complex.I := by
    have hmem : (-c) ∈ Metric.ball (0:ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_neg]; exact hc
    have h := circleIntegral.integral_sub_inv_of_mem_ball (c := (0:ℂ)) (R := ρ) (w := -c) hmem
    simpa only [sub_neg_eq_add] using h
  have hpt : ∀ w ∈ Metric.sphere (0:ℂ) ρ,
      ((w + c)⁻¹ • Res b w) * (b + c • 1) = Res b w - (w + c)⁻¹ • (1 : A) := by
    intro w hw
    have hwr : ‖w‖ = ρ := hsphere w hw
    have hunitw : IsUnit (w • 1 - b) :=
      hunit w (le_of_eq hwr.symm) (by rw [hwr]; exact le_of_lt hρlt)
    have hw0 : w + c ≠ 0 := hwne w hw
    have key : Res b w * (b + c • 1) = (w + c) • Res b w - 1 := by
      have hb := res_mul_self b hunitw
      have hc1 : Res b w * (c • (1 : A)) = c • Res b w := by rw [mul_smul_comm, mul_one]
      rw [mul_add, hb, hc1, add_smul]
      abel
    rw [smul_mul_assoc, key, smul_sub, smul_smul, inv_mul_cancel₀ hw0, one_smul]
  have hR : (∮ w in C(0,ρ), (w + c)⁻¹ • (1:A)) = (2 * Real.pi * Complex.I) • (1:A) := by
    rw [circleIntegral.integral_smul_const, hone]
  have hsne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  calc (-(2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (w + c)⁻¹ • Res b w) * (b + c • 1)
      = -(2 * Real.pi * Complex.I)⁻¹ •
          ((∮ w in C(0, ρ), (w + c)⁻¹ • Res b w) * (b + c • 1)) := by
        rw [smul_mul_assoc]
    _ = -(2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), ((w + c)⁻¹ • Res b w) * (b + c • 1)) := by
        rw [circleIntegral_mul_const (b + c • 1) (fun w => (w + c)⁻¹ • Res b w) 0 ρ hcirc_int]
    _ = -(2 * Real.pi * Complex.I)⁻¹ •
          (∮ w in C(0, ρ), (Res b w - (w + c)⁻¹ • (1:A))) := by
        congr 1
        exact circleIntegral.integral_congr hρle hpt
    _ = -(2 * Real.pi * Complex.I)⁻¹ •
          ((∮ w in C(0,ρ), Res b w) - ∮ w in C(0,ρ), (w + c)⁻¹ • (1:A)) := by
        rw [circleIntegral.integral_sub hres_int hscal_int]
    _ = -(2 * Real.pi * Complex.I)⁻¹ • (CircA b ρ - (2 * Real.pi * Complex.I) • (1:A)) := by
        rw [hR]; rfl
    _ = 1 - Proj b ρ := by
        have hw : (2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I) = 1 :=
          inv_mul_cancel₀ hsne
        rw [smul_sub, smul_smul,
          show (-(2 * Real.pi * Complex.I)⁻¹) * (2 * Real.pi * Complex.I) = -1 by
            rw [neg_mul, hw],
          neg_one_smul, Proj, neg_smul]
        abel

/-! ## Assembly of the outside unit statement -/

/-- Given `X` with `(b + c • 1) * X = X * (b + c • 1) = 1 - Proj b ρ`, the element
`c • (1 - Proj b ρ) + (1 - Proj b ρ) * b + Proj b ρ` is a unit. -/
theorem isUnit_of_out_relations {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (b : A) (ρ : ℝ) (c : ℂ) (X : A) (hidem : Proj b ρ * Proj b ρ = Proj b ρ)
    (hleft : (b + c • 1) * X = 1 - Proj b ρ) (hright : X * (b + c • 1) = 1 - Proj b ρ) :
    IsUnit (c • (1 - Proj b ρ) + (1 - Proj b ρ) * b + Proj b ρ) := by
  have hQQ : (1 - Proj b ρ) * (1 - Proj b ρ) = 1 - Proj b ρ := by
    have h : (1 - Proj b ρ) * (1 - Proj b ρ)
        = 1 - Proj b ρ - Proj b ρ + Proj b ρ * Proj b ρ := by noncomm_ring
    rw [h, hidem]; abel
  have hkey := isUnit_of_mul_eq_idem hQQ hleft hright
  have h1 : (1 - Proj b ρ) * (b + c • 1) = (1 - Proj b ρ) * b + c • (1 - Proj b ρ) := by
    rw [mul_add, mul_smul_comm, mul_one]
  have hconv : (1 - Proj b ρ) * (b + c • 1) + (1 - (1 - Proj b ρ))
      = c • (1 - Proj b ρ) + (1 - Proj b ρ) * b + Proj b ρ := by
    rw [h1]; abel
  rwa [hconv] at hkey

/-- The outside unit statement for `ρ ≤ ‖c‖`: then `-c` lies in the annulus, so `b + c • 1` is a
unit and `X = (b + c • 1)⁻¹ * (1 - Proj b ρ)` satisfies the required relations. -/
theorem isUnit_out_of_unit {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (b : A) {ρ : ℝ}
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    (hidem : Proj b ρ * Proj b ρ = Proj b ρ) (hcomm : b * Proj b ρ = Proj b ρ * b)
    {c : ℂ} (hcρ : ρ ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1) :
    IsUnit (c • (1 - Proj b ρ) + (1 - Proj b ρ) * b + Proj b ρ) := by
  have hu : IsUnit (b + c • 1) := by
    have hu0 : IsUnit ((-c) • (1:A) - b) :=
      hunit (-c) (by rw [norm_neg]; exact hcρ) (by rw [norm_neg]; exact hc1)
    have h : (-c) • (1:A) - b = -(c • 1 + b) := by rw [neg_smul]; abel
    have h2 : IsUnit (c • 1 + b) := by
      have h3 : IsUnit (-((-c) • (1:A) - b)) := hu0.neg
      rwa [h, neg_neg] at h3
    rwa [add_comm] at h2
  obtain ⟨u, hu_eq⟩ := hu
  set Q := 1 - Proj b ρ with hQ
  have hul : (↑u : A) * (↑(u⁻¹) : A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hlu : (↑(u⁻¹) : A) * (↑u : A) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hQb : Q * b = b * Q := by
    rw [hQ]; rw [sub_mul, one_mul, mul_sub, mul_one, ← hcomm]
  have hQc : Q * (c • (1:A)) = (c • (1:A)) * Q := by
    rw [hQ, mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
  have hQadd : Q * (b + c • 1) = (b + c • 1) * Q := by
    rw [mul_add, add_mul, hQb, hQc]
  have hleft : (b + c • 1) * ((↑(u⁻¹) : A) * Q) = 1 - Proj b ρ := by
    rw [← mul_assoc, ← hu_eq, hul, one_mul, hQ]
  have hright : ((↑(u⁻¹) : A) * Q) * (b + c • 1) = 1 - Proj b ρ := by
    rw [mul_assoc, hQadd, ← mul_assoc, ← hu_eq, hlu, one_mul, hQ]
  exact isUnit_of_out_relations b ρ c ((↑(u⁻¹) : A) * Q) hidem hleft hright

/-- The outside unit statement for `‖c‖ < ρ`, via the contour integral `out_contour_mul_left`
and `out_contour_mul_right`. -/
theorem isUnit_out_of_contour {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    (hidem : Proj b ρ * Proj b ρ = Proj b ρ) {c : ℂ} (hc : ‖c‖ < ρ) :
    IsUnit (c • (1 - Proj b ρ) + (1 - Proj b ρ) * b + Proj b ρ) :=
  isUnit_of_out_relations b ρ c
    (-(2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (w + c)⁻¹ • Res b w)
    hidem
    (out_contour_mul_left b hρpos hρlt hunit hc)
    (out_contour_mul_right b hρpos hρlt hunit hc)

/-- **The outside unit statement.**  With `Proj b ρ` the "inside" spectral projection of `b`
(the annulus `ρ ≤ ‖z‖ ≤ 1` being free of spectrum), for every `c` with `‖c‖ ≤ 1` the element
`c • (1 - Proj b ρ) + (1 - Proj b ρ) * b + Proj b ρ` is a unit. -/
theorem spectral_out_unit {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    (hidem : Proj b ρ * Proj b ρ = Proj b ρ) (hcomm : b * Proj b ρ = Proj b ρ * b)
    (c : ℂ) (hc1 : ‖c‖ ≤ 1) :
    IsUnit (c • (1 - Proj b ρ) + (1 - Proj b ρ) * b + Proj b ρ) := by
  by_cases h : ρ ≤ ‖c‖
  · exact isUnit_out_of_unit b hunit hidem hcomm h hc1
  · exact isUnit_out_of_contour b hρpos hρlt hunit hidem (not_le.mp h)

/-! ## The main statement -/

theorem spectral_split_out (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b : Matrix (Fin n) (Fin n) C(X, ℂ))
    (hb : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f x))) :
    ∃ E : Matrix (Fin n) (Fin n) C(X, ℂ),
      E * E = E ∧ E * b = b * E ∧
      (∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
        IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) +
          t • ((E * b).map (fun f => f x)))) ∧
      (∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
        IsUnit ((((t : ℂ) * z) • (1 - E) + (1 - E) * b + E).map (fun f => f x))) ∧
      (∀ x : X, IsUnit (((1 - E) * b + E).map (fun f => f x))) := by
  classical
  letI : NormedRing (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  have hCS : CompleteSpace (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  obtain ⟨ε, hε0, hε1, hgap⟩ := gap_annulus X n b hb
  set ρ : ℝ := 1 - ε / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < 1 := by rw [hρdef]; linarith
  have hρle : ρ ≤ 1 := le_of_lt hρlt
  -- the invertibility of the resolvent on the annulus `ρ ≤ ‖z‖ ≤ 1`
  have hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b) := by
    intro z hz1 hz2
    rw [isUnit_matrix_forall n]
    intro x
    have h1 : 1 - ε ≤ ‖(-z)‖ := by rw [norm_neg]; linarith
    have h2 : ‖(-z)‖ ≤ 1 + ε := by rw [norm_neg]; linarith
    have hgapx := hgap x (-z) h1 h2
    have hglob : z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b
        = -((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b) := by
      rw [neg_add, neg_smul, neg_neg, sub_eq_add_neg]
    have hφ : ((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
          (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b)
        = -(((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
            ((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b)) := by
      rw [hglob, map_neg]
    have hφ' : ((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
          ((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b)
        = (-z) • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f x) := by
      rw [map_add, map_smul, map_one]
      rfl
    have h1' : IsUnit (((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
        ((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b)) := by
      rw [hφ']
      exact hgapx
    change IsUnit (((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
      (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b))
    rw [hφ]
    exact h1'.neg
  -- the four algebraic facts
  have hbY := @spectral_bY _ _ _ hCS b ρ hρpos hρlt hunit
  have hYb := @spectral_Yb _ _ _ hCS b ρ hρpos hρlt hunit
  have htwo := @twoRadius_alt _ _ _ hCS b ρ hρpos hρlt hunit
  have hidem : Proj b ρ * Proj b ρ = Proj b ρ :=
    @spectral_idem _ _ _ hCS b ρ hρpos hρle hunit htwo
  have hcomm : b * Proj b ρ = Proj b ρ * b :=
    @spectral_comm _ _ _ hCS b ρ hρpos
      (fun z hz => hunit z (by rw [hz]) (by rw [hz]; exact hρle))
  have huz := @spectral_unit_z _ _ _ hCS b ρ hρpos hρlt hunit hidem hcomm
  have hud := @spectral_unit_d _ _ _ hCS b ρ hρpos hρlt hunit hbY hYb hidem
  have hout := @spectral_out_unit _ _ _ hCS b ρ hρpos hρlt hunit hidem hcomm
  refine ⟨Proj b ρ, hidem, hcomm.symm, ?_, ?_, ?_⟩
  · intro x t z ht0 ht1 hz
    have hu := huz z t hz ht0 ht1
    have hu' : IsUnit ((z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + t • (Proj b ρ * b)).map
        (fun f => f x)) := (isUnit_matrix_forall n _).mp hu x
    have hone : ((1 : Matrix (Fin n) (Fin n) C(X, ℂ)).map (fun f => f x))
        = (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, h]
    have hm : (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + t • (Proj b ρ * b)).map
          (fun f => f x)
        = z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((Proj b ρ * b).map (fun f => f x)) := by
      rw [Matrix.map_add _ (fun a b => rfl) _ _,
        Matrix.map_smul _ z (fun a => by simp [Algebra.smul_def]) _,
        hone,
        Matrix.map_smul _ t (fun a => by simp [Algebra.smul_def]) _]
    rwa [hm] at hu'
  · intro x t z ht0 ht1 hz
    have hc1 : ‖((t : ℂ) * z)‖ ≤ 1 := by
      rw [norm_mul, hz, mul_one, Complex.norm_of_nonneg ht0]
      exact ht1
    exact (isUnit_matrix_forall n _).mp (hout ((t : ℂ) * z) hc1) x
  · intro x
    have hu' : IsUnit (((1 - Proj b ρ) * b + Proj b ρ).map (fun f => f x)) :=
      (isUnit_matrix_forall n _).mp hud x
    exact hu'

end

end Work.KT.Fund
