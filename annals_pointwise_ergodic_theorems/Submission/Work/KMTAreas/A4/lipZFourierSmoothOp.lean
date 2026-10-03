import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The Fourier transform of a translate of `G`, for an arbitrary (not necessarily finitely
supported) `G`.  This is the hypothesis-free form of
`Work.Analysis.InverseTheory.ZFourier_sub_right`: that statement carries a `FinSupp G` assumption
which its proof never uses, so the identity is available for every `G : ℤ → ℂ`. -/
theorem ZFourier_sub_right' {G : ℤ → ℂ} (Q : ℤ) (ξ : FreqCircle) :
    ZFourier (fun x => G (x - Q)) ξ = (fourier (-Q) ξ : ℂ) * ZFourier G ξ := by
  rw [ZFourier, ZFourier]
  calc ∑' y : ℤ, G (y - Q) * (fourier (-y) ξ : ℂ)
      = ∑' y : ℤ, (fourier (-Q) ξ : ℂ) * (G (y - Q) * (fourier (-(y - Q)) ξ : ℂ)) := by
        refine tsum_congr fun y => ?_
        have h1 : (-y : ℤ) = (-(y - Q)) + (-Q) := by ring
        rw [h1, fourier_add]
        ring
    _ = (fourier (-Q) ξ : ℂ) * ∑' y : ℤ, G (y - Q) * (fourier (-(y - Q)) ξ : ℂ) := tsum_mul_left
    _ = (fourier (-Q) ξ : ℂ) * ∑' z : ℤ, G z * (fourier (-z) ξ : ℂ) := by
        congr 1
        simpa only [Equiv.subRight_apply] using
          Equiv.tsum_eq (Equiv.subRight Q) (fun z : ℤ => G z * (fourier (-z) ξ : ℂ))

/-- The exponential `e(n ξ)` has modulus `1`. -/
theorem fourier_norm_one (n : ℤ) (ξ : FreqCircle) : ‖(fourier n ξ : ℂ)‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- **The Fourier transform of the smoothing operator**, in the absolutely summable setting.
For `w, G : ℤ → ℂ` with `∑_m ‖w m‖ < ∞` and `∑_x ‖G x‖ < ∞`, and any `Q : ℤ`, the Fourier
transform of `x ↦ ∑_m w(m) G(x - Q m)` factors as `𝓕_ℤ G(ξ)` times the multiplier
`∑_m w(m) e(-Q m ξ)`.

This is the hypothesis-free (`Summable` instead of `FinSupp`) form of
`Work.Analysis.InverseTheory.ZFourier_smoothOp`, proved by absolute convergence of the double
series: the shift `(m, x) ↦ (m, x - Q m)` is a bijection of `ℤ × ℤ`, so the double family
`‖w m‖ ‖G (x - Q m)‖` is summable, and Fubini for absolutely summable series applies. -/
theorem lipZFourierSmoothOp {w G : ℤ → ℂ} (hw : Summable fun m : ℤ => ‖w m‖)
    (hG : Summable fun x : ℤ => ‖G x‖) (Q : ℤ) (ξ : Work.Analysis.InverseTheory.FreqCircle) :
    Work.Analysis.InverseTheory.ZFourier (Work.KMTAreas.A4.smoothOp w G Q) ξ
      = Work.Analysis.InverseTheory.ZFourier G ξ
        * ∑' m : ℤ, w m * (fourier (-(Q * m)) ξ : ℂ) := by
  have hnw : (0 : ℤ → ℝ) ≤ fun m => ‖w m‖ := fun m => norm_nonneg _
  have hnG : (0 : ℤ → ℝ) ≤ fun x => ‖G x‖ := fun x => norm_nonneg _
  -- summability of the product of the two norm families
  have hprod : Summable fun p : ℤ × ℤ => ‖w p.1‖ * ‖G p.2‖ :=
    Summable.mul_of_nonneg hw hG hnw hnG
  -- the shear `(m, x) ↦ (m, x - Q m)` is a bijection of `ℤ × ℤ`
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1, p.2 - Q * p.1)
      invFun := fun p => (p.1, p.2 + Q * p.1)
      left_inv := by rintro ⟨a, b⟩; simp
      right_inv := by rintro ⟨a, b⟩; simp }
  have hbnd : Summable fun p : ℤ × ℤ => ‖w p.1‖ * ‖G (p.2 - Q * p.1)‖ :=
    (Equiv.summable_iff e).mpr hprod
  -- absolute summability of the double family
  have hφ : Summable fun p : ℤ × ℤ =>
      w p.1 * G (p.2 - Q * p.1) * (fourier (-p.2) ξ : ℂ) := by
    refine Summable.of_norm_bounded hbnd fun p => ?_
    rw [norm_mul, norm_mul, fourier_norm_one, mul_one]
  have h1 : ZFourier (smoothOp w G Q) ξ
      = ∑' x : ℤ, ∑' m : ℤ, w m * G (x - Q * m) * (fourier (-x) ξ : ℂ) := by
    rw [ZFourier]
    refine tsum_congr fun x => ?_
    rw [smoothOp, ← tsum_mul_right]
  have h2 : ∑' x : ℤ, ∑' m : ℤ, w m * G (x - Q * m) * (fourier (-x) ξ : ℂ)
      = ∑' m : ℤ, ∑' x : ℤ, w m * G (x - Q * m) * (fourier (-x) ξ : ℂ) :=
    Summable.tsum_comm hφ
  have hinner : ∀ m : ℤ, ∑' x : ℤ, w m * G (x - Q * m) * (fourier (-x) ξ : ℂ)
      = w m * ((fourier (-(Q * m)) ξ : ℂ) * ZFourier G ξ) := by
    intro m
    rw [show (∑' x : ℤ, w m * G (x - Q * m) * (fourier (-x) ξ : ℂ))
        = ∑' x : ℤ, w m * (G (x - Q * m) * (fourier (-x) ξ : ℂ)) from
        tsum_congr fun x => by ring]
    rw [tsum_mul_left]
    congr 1
    simpa only [ZFourier] using ZFourier_sub_right' (Q * m) ξ
  have h4 : ∑' m : ℤ, w m * ((fourier (-(Q * m)) ξ : ℂ) * ZFourier G ξ)
      = (∑' m : ℤ, w m * (fourier (-(Q * m)) ξ : ℂ)) * ZFourier G ξ := by
    rw [show (∑' m : ℤ, w m * ((fourier (-(Q * m)) ξ : ℂ) * ZFourier G ξ))
        = ∑' m : ℤ, (w m * (fourier (-(Q * m)) ξ : ℂ)) * ZFourier G ξ from
        tsum_congr fun m => by ring]
    rw [tsum_mul_right]
  calc ZFourier (smoothOp w G Q) ξ
      = ∑' x : ℤ, ∑' m : ℤ, w m * G (x - Q * m) * (fourier (-x) ξ : ℂ) := h1
    _ = ∑' m : ℤ, ∑' x : ℤ, w m * G (x - Q * m) * (fourier (-x) ξ : ℂ) := h2
    _ = ∑' m : ℤ, w m * ((fourier (-(Q * m)) ξ : ℂ) * ZFourier G ξ) :=
          tsum_congr fun m => hinner m
    _ = (∑' m : ℤ, w m * (fourier (-(Q * m)) ξ : ℂ)) * ZFourier G ξ := h4
    _ = ZFourier G ξ * ∑' m : ℤ, w m * (fourier (-(Q * m)) ξ : ℂ) := by rw [mul_comm]

end Work.KMTAreas.A4
