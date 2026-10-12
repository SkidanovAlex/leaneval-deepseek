import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.Rb5Lin

/-- The inverse-norm bookkeeping of the dilation `p ↦ ℓ⁻¹ • p`:
`(2‖ℓ⁻¹ • p‖²)⁻¹ = ℓ²(2‖p‖²)⁻¹`, from `‖ℓ⁻¹ • p‖² = ℓ⁻²‖p‖²`. -/
private lemma inv_two_mul_norm_sq_inv_smul {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (2 * ‖(ℓ⁻¹) • p‖ ^ 2)⁻¹ = ℓ ^ 2 * (2 * ‖p‖ ^ 2)⁻¹ := by
  have hℓn : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have hnorm : ‖(ℓ⁻¹) • p‖ ^ 2 = (ℓ⁻¹) ^ 2 * ‖p‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓn]
    ring
  calc (2 * ‖(ℓ⁻¹) • p‖ ^ 2)⁻¹
      = (2 * ((ℓ⁻¹) ^ 2 * ‖p‖ ^ 2))⁻¹ := by rw [hnorm]
    _ = ((ℓ⁻¹) ^ 2 * (2 * ‖p‖ ^ 2))⁻¹ := by
          rw [show 2 * ((ℓ⁻¹) ^ 2 * ‖p‖ ^ 2) = (ℓ⁻¹) ^ 2 * (2 * ‖p‖ ^ 2) by ring]
    _ = (2 * ‖p‖ ^ 2)⁻¹ * ((ℓ⁻¹) ^ 2)⁻¹ := mul_inv_rev _ _
    _ = (2 * ‖p‖ ^ 2)⁻¹ * ℓ ^ 2 := by
          rw [show ((ℓ⁻¹) ^ 2)⁻¹ = ℓ ^ 2 by rw [← inv_pow, inv_inv]]
    _ = ℓ ^ 2 * (2 * ‖p‖ ^ 2)⁻¹ := by rw [mul_comm]

/-- The same identity in the form used for the pointwise integrand:
`(2‖p‖²)⁻¹ = ℓ⁻²(2‖ℓ⁻¹ • p‖²)⁻¹`. -/
private lemma inv_two_mul_norm_sq_eq {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (2 * ‖p‖ ^ 2)⁻¹ = (ℓ ^ 2)⁻¹ * (2 * ‖(ℓ⁻¹) • p‖ ^ 2)⁻¹ := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  calc (2 * ‖p‖ ^ 2)⁻¹
      = (ℓ ^ 2)⁻¹ * (ℓ ^ 2 * (2 * ‖p‖ ^ 2)⁻¹) := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hℓ0), one_mul]
    _ = (ℓ ^ 2)⁻¹ * (2 * ‖(ℓ⁻¹) • p‖ ^ 2)⁻¹ := by
          rw [← inv_two_mul_norm_sq_inv_smul hℓ p]

/-- **Fourier dilation.**  With the `p`-convention Fourier transform of the corpus
(`chat W p = Re ∫ y, e^{−i⟪p,y⟫}W(y)dy`), rescaling the *argument* of `W` by `ℓ` and
multiplying by the Jacobian `ℓ³` rescales the *frequency* by `ℓ⁻¹`:

`chat (fun x => ℓ³ * W (ℓ • x)) p = chat W (ℓ⁻¹ • p)`  for `ℓ > 0`.

This is the substitution `y = ℓ⁻¹ • z` in the defining integral, with
`⟪p, ℓ⁻¹ • z⟫ = ⟪ℓ⁻¹ • p, z⟫` and the volume factor `ℓ⁻³` cancelled by the `ℓ³`
in front. -/
lemma chat_smul_scale {W : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (fun x => ℓ ^ 3 * W (ℓ • x)) p = Work.BoseFixR.chat W (ℓ⁻¹ • p) := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have hℓi : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp [EuclideanSpace]
  have hGinv :
      (∫ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
          * ((ℓ ^ 3 * W (ℓ • y) : ℝ) : ℂ))
        = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ s : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p (ℓ⁻¹ • s) : ℂ)))
          * ((ℓ ^ 3 * W (ℓ • (ℓ⁻¹ • s)) : ℝ) : ℂ)) := by
    have hsub := Measure.integral_comp_smul_of_nonneg
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (fun y : EuclideanSpace ℝ (Fin 3) => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
        * ((ℓ ^ 3 * W (ℓ • y) : ℝ) : ℂ)) (ℓ⁻¹) (hR := hℓi.le)
    rw [hfr, Complex.real_smul] at hsub
    have h3 : ((ℓ⁻¹) ^ 3)⁻¹ = ℓ ^ 3 := by rw [← inv_pow, inv_inv]
    rw [h3] at hsub
    rw [hsub, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 3 hℓ0)]
    simp
  have hpt : ∀ s : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(Complex.I * (inner ℝ p (ℓ⁻¹ • s) : ℂ)))
          * ((ℓ ^ 3 * W (ℓ • (ℓ⁻¹ • s)) : ℝ) : ℂ)
        = ((ℓ ^ 3 : ℝ) : ℂ) * (Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • p) s : ℂ)))
            * ((W s : ℝ) : ℂ)) := by
    intro s
    have h1 : ℓ • (ℓ⁻¹ • s) = s := by rw [smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
    have h2 : (inner ℝ p (ℓ⁻¹ • s) : ℂ) = (inner ℝ (ℓ⁻¹ • p) s : ℂ) := by
      rw [real_inner_smul_right, real_inner_smul_left]
    rw [h1, h2]
    push_cast
    ring
  have hmain :
      (∫ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
          * ((ℓ ^ 3 * W (ℓ • y) : ℝ) : ℂ))
        = (∫ s : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • p) s : ℂ)))
            * ((W s : ℝ) : ℂ)) := by
    rw [hGinv, integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (pow_ne_zero 3 hℓ0)]
    simp
  simpa only [Work.BoseFixR.chat, Submission.BoseGases.kinFT] using congrArg Complex.re hmain

/-- **The change of variables `p ↦ ℓ⁻¹ • p` in the kinetic integral.**  Since
`‖ℓ⁻¹ • p‖² = ℓ⁻²‖p‖²`, substituting `p = ℓ • s` in the integral of
`(chat W p)²/(2‖p‖²)` produces the factor `ℓ³ · ℓ⁻² = ℓ`. -/
lemma chat_integral_comp_inv_smul {W : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ p : EuclideanSpace ℝ (Fin 3), (Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2 / (2 * ‖p‖ ^ 2))
      = ℓ * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2) := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have hcomp :
      (∫ p : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2 / (2 * ‖(ℓ⁻¹) • p‖ ^ 2))
        = ℓ ^ 3 * ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2) := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp [EuclideanSpace]
    have h := Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (fun q : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2)) hℓ.le
    rw [hfr, smul_eq_mul] at h
    rw [h]
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3),
      (Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2 / (2 * ‖p‖ ^ 2)
        = (ℓ ^ 2)⁻¹ * ((Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2
            / (2 * ‖(ℓ⁻¹) • p‖ ^ 2)) := by
    intro p
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_two_mul_norm_sq_eq hℓ p]
    ring
  have hcoef : (ℓ ^ 2)⁻¹ * ℓ ^ 3 = ℓ := by
    rw [show ℓ ^ 3 = ℓ * ℓ ^ 2 by ring, mul_comm ℓ (ℓ ^ 2), ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hℓ0), one_mul]
  calc (∫ p : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2 / (2 * ‖p‖ ^ 2))
      = ∫ p : EuclideanSpace ℝ (Fin 3), (ℓ ^ 2)⁻¹
          * ((Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2 / (2 * ‖(ℓ⁻¹) • p‖ ^ 2)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (ℓ ^ 2)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2 / (2 * ‖(ℓ⁻¹) • p‖ ^ 2)) :=
        integral_const_mul _ _
    _ = (ℓ ^ 2)⁻¹ * (ℓ ^ 3 * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
        rw [hcomp]
    _ = ℓ * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2) := by
        rw [← mul_assoc, hcoef]

theorem latticeSum_scaling {W : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h_unit : (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
        (Work.BoseFixR.chat (fun x => ℓ ^ 3 * W (ℓ • x)) (Work.BoseB4.vec (k : Fin 3 → ℤ))) ^ 2
          / (2 * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))
      ≤ 4 * ((2 * Real.pi) ^ 3)⁻¹
        * ∫ p : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (fun x => ℓ ^ 3 * W (ℓ • x)) p) ^ 2 / (2 * ‖p‖ ^ 2)) :
    (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
        (Work.BoseFixR.chat W ((ℓ⁻¹) • Work.BoseB4.vec (k : Fin 3 → ℤ))) ^ 2
          / (2 * ‖(ℓ⁻¹) • Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))
      ≤ 4 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3
        * ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2) := by
  set S : ℝ := ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
        (Work.BoseFixR.chat W ((ℓ⁻¹) • Work.BoseB4.vec (k : Fin 3 → ℤ))) ^ 2
          / (2 * ‖(ℓ⁻¹) • Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) with hS
  set T : ℝ := ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
        (Work.BoseFixR.chat W ((ℓ⁻¹) • Work.BoseB4.vec (k : Fin 3 → ℤ))) ^ 2
          / (2 * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) with hT
  set J : ℝ := ∫ q : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2) with hJ
  have hT' : (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
        (Work.BoseFixR.chat (fun x => ℓ ^ 3 * W (ℓ • x)) (Work.BoseB4.vec (k : Fin 3 → ℤ))) ^ 2
          / (2 * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) = T := by
    rw [hT]
    exact tsum_congr (fun k => by rw [chat_smul_scale hℓ])
  have hI' : (∫ p : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (fun x => ℓ ^ 3 * W (ℓ • x)) p) ^ 2 / (2 * ‖p‖ ^ 2)) = ℓ * J := by
    rw [hJ]
    calc (∫ p : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (fun x => ℓ ^ 3 * W (ℓ • x)) p) ^ 2 / (2 * ‖p‖ ^ 2))
        = (∫ p : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat W (ℓ⁻¹ • p)) ^ 2 / (2 * ‖p‖ ^ 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun p => by
            show Work.BoseFixR.chat (fun x => ℓ ^ 3 * W (ℓ • x)) p ^ 2 / (2 * ‖p‖ ^ 2)
              = Work.BoseFixR.chat W (ℓ⁻¹ • p) ^ 2 / (2 * ‖p‖ ^ 2)
            rw [chat_smul_scale hℓ]))
      _ = ℓ * ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2) := chat_integral_comp_inv_smul hℓ
  have hu : T ≤ 4 * ((2 * Real.pi) ^ 3)⁻¹ * (ℓ * J) := by
    rw [hT', hI'] at h_unit
    exact h_unit
  have hST : S = ℓ ^ 2 * T := by
    rw [hS, hT, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_two_mul_norm_sq_inv_smul hℓ
      (Work.BoseB4.vec (k : Fin 3 → ℤ))]
    ring
  calc S = ℓ ^ 2 * T := hST
    _ ≤ ℓ ^ 2 * (4 * ((2 * Real.pi) ^ 3)⁻¹ * (ℓ * J)) :=
        mul_le_mul_of_nonneg_left hu (sq_nonneg ℓ)
    _ = 4 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * J := by ring

end Work.BoseFixR.Rb5Lin
