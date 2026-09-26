import Mathlib
import Submission.Work.CKFinal.U0ArcSetup
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis

namespace Work.CKFinal.ArcCont

open scoped MatrixGroups
open UpperHalfPlane

/-!
# Which `SL(2,ℤ)`-translate of the imaginary axis produces a point of an arc

`Work.Kernels.imagAxis t ht` is the point `it` of the positive imaginary axis.  Suppose
`γ • (it) = τ` for some `γ ∈ SL(2,ℤ)`.

The bottom arcs of `U₀` are the circles `‖τ ∓ 1/2‖ = 1/2`; by `U0ArcSetup` they are exactly the
preimages of the imaginary axis under `Gam1` and `Gam2`:

* `Re (Gam1 • τ) = 0 ↔ ‖τ - 1/2‖ = 1/2`,
* `Re (Gam2 • τ) = 0 ↔ ‖τ + 1/2‖ = 1/2`.

So `‖τ - 1/2‖ = 1/2` means that `Gam1 • τ` is again on the imaginary axis, i.e. the product
`Gam1 * γ` carries `it` to the point `i(Gam1 • τ).im` of the imaginary axis.  By
`eq_one_or_neg_one_or_S_of_smul_imagAxis`, the stabiliser of the imaginary axis in `SL(2,ℤ)` is
`{±1, ±S}`, so `Gam1 * γ ∈ {±1, ±S}`, i.e. `γ ∈ {Gam1⁻¹, -Gam1⁻¹, Gam1⁻¹ S, -Gam1⁻¹ S}`.  Spelling
`Gam1 = !![1,0;-1,1]` out in generators gives `Gam1⁻¹ = T S T` and `Gam1⁻¹ S = S T⁻¹`.  The
second branch is the mirror, with `Gam2 = !![1,0;1,1] = Gam1⁻¹`.
-/

/-- A point `w` of the upper half plane with vanishing real part **is** a point of the imaginary
axis: it equals `imagAxis w.im w.im_pos`. -/
lemma imagAxis_eq_of_re_eq_zero (w : UpperHalfPlane) (hw : (w : ℂ).re = 0) :
    Work.Kernels.imagAxis w.im w.im_pos = w := by
  apply UpperHalfPlane.ext
  rw [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
  have h1 : ((w:ℂ).re : ℂ) + ((w:ℂ).im : ℂ) * Complex.I = (w:ℂ) := Complex.re_add_im _
  have h2 : ((w:ℂ).re : ℂ) = 0 := by rw [hw]; norm_num
  rw [h2, zero_add] at h1
  rw [UpperHalfPlane.coe_im] at h1
  exact h1

/-- `Gam1⁻¹ = T S T`. -/
lemma Gam1_inv_eq :
    Work.CKFinal.Gam1⁻¹ = ModularGroup.T * ModularGroup.S * ModularGroup.T := by decide

/-- `Gam2⁻¹ = (T S T)⁻¹`. -/
lemma Gam2_inv_eq :
    Work.CKFinal.Gam2⁻¹ = (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ := by decide

/-- `Gam1⁻¹ S = S T⁻¹`. -/
lemma Gam1_inv_mul_S :
    Work.CKFinal.Gam1⁻¹ * ModularGroup.S = ModularGroup.S * ModularGroup.T⁻¹ := by decide

/-- `Gam2⁻¹ S = S T`. -/
lemma Gam2_inv_mul_S :
    Work.CKFinal.Gam2⁻¹ * ModularGroup.S = ModularGroup.S * ModularGroup.T := by decide

/-- **Classification of the `SL(2,ℤ)`-translates of the imaginary axis producing an arc point.**

If `γ • (it) = τ` with `t > 0` and `τ` on one of the two bottom arcs of `U₀`, then `γ` is one of
the four translates determined by that arc: `±T S T`, `±S T⁻¹` for the arc `‖τ - 1/2‖ = 1/2`, and
`±(T S T)⁻¹`, `±S T` for the arc `‖τ + 1/2‖ = 1/2`. -/
theorem arc_branch_classify {τ : UpperHalfPlane} {t : ℝ} (ht : 0 < t)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : γ • Work.Kernels.imagAxis t ht = τ) :
    (‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2 →
      γ = ModularGroup.T * ModularGroup.S * ModularGroup.T ∨
      γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T) ∨
      γ = ModularGroup.S * ModularGroup.T⁻¹ ∨
      γ = -(ModularGroup.S * ModularGroup.T⁻¹)) ∧
    (‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2 →
      γ = (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ ∨
      γ = -((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) ∨
      γ = ModularGroup.S * ModularGroup.T ∨
      γ = -(ModularGroup.S * ModularGroup.T)) := by
  constructor
  · -- **The arc `‖τ - 1/2‖ = 1/2`.**  Then `Gam1 • τ` lies on the imaginary axis, so `Gam1 * γ`
    -- stabilises the positive imaginary axis.
    intro hc
    have hre : (((Work.CKFinal.Gam1 • τ : UpperHalfPlane)) : ℂ).re = 0 :=
      (Work.CKFinal.re_Gam1_smul_eq_zero_iff τ).mpr hc
    have hgoal : (Work.CKFinal.Gam1 * γ) • Work.Kernels.imagAxis t ht
        = Work.Kernels.imagAxis (Work.CKFinal.Gam1 • τ).im (Work.CKFinal.Gam1 • τ).im_pos := by
      rw [mul_smul, h]
      exact (imagAxis_eq_of_re_eq_zero (Work.CKFinal.Gam1 • τ) hre).symm
    have hcls := Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis ht
      (Work.CKFinal.Gam1 • τ).im_pos hgoal
    rcases hcls with h1 | h1 | h1 | h1
    · left
      have hγ : γ = Work.CKFinal.Gam1⁻¹ := by
        have h2 : γ = Work.CKFinal.Gam1⁻¹ * (Work.CKFinal.Gam1 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1, mul_one]
      rw [hγ, Gam1_inv_eq]
    · right; left
      have hγ : γ = -(Work.CKFinal.Gam1⁻¹) := by
        have h2 : γ = Work.CKFinal.Gam1⁻¹ * (Work.CKFinal.Gam1 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1, mul_neg_one]
      rw [hγ, Gam1_inv_eq]
    · right; right; left
      have hγ : γ = Work.CKFinal.Gam1⁻¹ * ModularGroup.S := by
        have h2 : γ = Work.CKFinal.Gam1⁻¹ * (Work.CKFinal.Gam1 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1]
      rw [hγ, Gam1_inv_mul_S]
    · right; right; right
      have hγ : γ = -(Work.CKFinal.Gam1⁻¹ * ModularGroup.S) := by
        have h2 : γ = Work.CKFinal.Gam1⁻¹ * (Work.CKFinal.Gam1 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1, mul_neg]
      rw [hγ, Gam1_inv_mul_S]
  · -- **The arc `‖τ + 1/2‖ = 1/2`.**  The mirror image of the previous case, with `Gam2`.
    intro hc
    have hre : (((Work.CKFinal.Gam2 • τ : UpperHalfPlane)) : ℂ).re = 0 :=
      (Work.CKFinal.re_Gam2_smul_eq_zero_iff τ).mpr hc
    have hgoal : (Work.CKFinal.Gam2 * γ) • Work.Kernels.imagAxis t ht
        = Work.Kernels.imagAxis (Work.CKFinal.Gam2 • τ).im (Work.CKFinal.Gam2 • τ).im_pos := by
      rw [mul_smul, h]
      exact (imagAxis_eq_of_re_eq_zero (Work.CKFinal.Gam2 • τ) hre).symm
    have hcls := Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis ht
      (Work.CKFinal.Gam2 • τ).im_pos hgoal
    rcases hcls with h1 | h1 | h1 | h1
    · left
      have hγ : γ = Work.CKFinal.Gam2⁻¹ := by
        have h2 : γ = Work.CKFinal.Gam2⁻¹ * (Work.CKFinal.Gam2 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1, mul_one]
      rw [hγ, Gam2_inv_eq]
    · right; left
      have hγ : γ = -(Work.CKFinal.Gam2⁻¹) := by
        have h2 : γ = Work.CKFinal.Gam2⁻¹ * (Work.CKFinal.Gam2 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1, mul_neg_one]
      rw [hγ, Gam2_inv_eq]
    · right; right; left
      have hγ : γ = Work.CKFinal.Gam2⁻¹ * ModularGroup.S := by
        have h2 : γ = Work.CKFinal.Gam2⁻¹ * (Work.CKFinal.Gam2 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1]
      rw [hγ, Gam2_inv_mul_S]
    · right; right; right
      have hγ : γ = -(Work.CKFinal.Gam2⁻¹ * ModularGroup.S) := by
        have h2 : γ = Work.CKFinal.Gam2⁻¹ * (Work.CKFinal.Gam2 * γ) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h2, h1, mul_neg]
      rw [hγ, Gam2_inv_mul_S]

end Work.CKFinal.ArcCont
