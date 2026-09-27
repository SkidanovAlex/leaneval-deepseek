import Mathlib
import Submission.Work.Drive.N2Lead.saddleArcs

/-!
# `w ↦ Re (arcZ η w)` is strictly increasing (for `η > 0`)

The model arc of the saddle window is `arcZ η w = I * sqrt (η - I w)` (`saddleArcs.lean`).  This file
proves that `w ↦ arcZ η w` is `C^1` and that the derivative of its real part is *strictly positive*,
i.e. `w ↦ (arcZ η w).re` is strictly increasing.  Since the complex square root is the principal one,
the arc `w ↦ arcZ η w` runs along the branch of the hyperbola `Z ^ 2 = -η + I w` whose *imaginary*
part is positive, and the derivative of its real part is the (positive) quantity
`Im (arcZ η w) / (2 * ‖arcZ η w‖²)`.

The proof differentiates the composite `w ↦ I * sqrt (η - I w)` with the chain rule
(`Complex.hasDerivAt_sqrt`, whose hypothesis `η - I w ∈ slitPlane` holds because `Re (η - I w) = η > 0`)
and converts the resulting value `g ^ (-1/2) / 2` into the equivalent form
`I / (2 * (I * sqrt g)) = I / (2 * arcZ η w)`, whose real part is manifestly positive:
`(I / (2 * z)).re = z.im / (2 * ‖z‖²)` with `z = arcZ η w`, and `Im (arcZ η w) = Re (sqrt (η - I w)) > 0`.
-/

namespace Work.Drive.N2Lead.ReStrictMono

open scoped ContDiff Topology

/-! ## The derivative of the model arc -/

/-- The elementary rewrite of the derivative of `sqrt` at a point of the slit plane: the value
`g ^ (-1/2) / 2` given by `Complex.hasDerivAt_sqrt` is the `arcZ`-form `I / (2 * (I * sqrt g))`. -/
lemma sqrt_inv_div_two (s : ℂ) : s⁻¹ / 2 = Complex.I / (2 * (Complex.I * s)) := by
  field_simp

/-- The derivative value of `z ↦ I * sqrt z` composed with a function with derivative `-I`:
`I * ((g ^ (-1/2) / 2) * (-I)) = I / (2 * (I * sqrt g))`. -/
lemma deriv_value_arcZ (g : ℂ) :
    Complex.I * ((g ^ (-1/2 : ℂ) / 2) * (-Complex.I))
      = Complex.I / (2 * (Complex.I * Complex.sqrt g)) := by
  have h1 : g ^ (-1/2 : ℂ) = (Complex.sqrt g)⁻¹ := by
    rw [show (-1/2 : ℂ) = -(2⁻¹ : ℂ) by norm_num, Complex.cpow_neg]
    rfl
  rw [h1]
  have hII : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I]; ring
  rw [show Complex.I * ((Complex.sqrt g)⁻¹ / 2 * (-Complex.I))
      = (Complex.I * (-Complex.I)) * ((Complex.sqrt g)⁻¹ / 2) by ring, hII, one_mul]
  exact sqrt_inv_div_two (Complex.sqrt g)

/-- The model arc is (real-)differentiable, with derivative `I / (2 * arcZ η w)`. -/
lemma hasDerivAt_arcZ (η : ℝ) (hη : 0 < η) (w : ℝ) :
    HasDerivAt (fun u : ℝ => Work.Drive.N2Lead.arcZ η u)
      (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w)) w := by
  have hG : HasDerivAt (fun u : ℝ => (η:ℂ) - (u:ℂ) * Complex.I) (-Complex.I) w := by
    have h1 : HasDerivAt (fun u : ℝ => ((u:ℝ):ℂ)) (1:ℂ) w := by
      simpa using (hasDerivAt_id w).ofReal_comp
    have h2 : HasDerivAt (fun u : ℝ => (u:ℂ) * Complex.I) ((1:ℂ) * Complex.I) w :=
      h1.mul_const Complex.I
    have h3 := h2.const_sub (η : ℂ)
    simpa using h3
  have hz : ((η:ℂ) - (w:ℂ) * Complex.I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, mul_one]
    linarith
  have hS : HasDerivAt Complex.sqrt (((η:ℂ) - (w:ℂ) * Complex.I) ^ (-1/2 : ℂ) / 2)
      ((η:ℂ) - (w:ℂ) * Complex.I) := Complex.hasDerivAt_sqrt hz
  have hSG : HasDerivAt (Complex.sqrt ∘ (fun u : ℝ => (η:ℂ) - (u:ℂ) * Complex.I))
      ((((η:ℂ) - (w:ℂ) * Complex.I) ^ (-1/2 : ℂ) / 2) * (-Complex.I)) w :=
    HasDerivAt.comp w hS hG
  have h1 : HasDerivAt (fun u : ℝ => Complex.I * Complex.sqrt ((η:ℂ) - (u:ℂ) * Complex.I))
      (Complex.I * ((((η:ℂ) - (w:ℂ) * Complex.I) ^ (-1/2 : ℂ) / 2) * (-Complex.I))) w :=
    hSG.const_mul Complex.I
  have h2 : Complex.I * ((((η:ℂ) - (w:ℂ) * Complex.I) ^ (-1/2 : ℂ) / 2) * (-Complex.I))
      = Complex.I / (2 * Work.Drive.N2Lead.arcZ η w) := by
    rw [deriv_value_arcZ ((η:ℂ) - (w:ℂ) * Complex.I)]
    rfl
  rw [h2] at h1
  simpa only [Work.Drive.N2Lead.arcZ, Function.comp_apply] using h1

/-- The derivative of the real part of the model arc. -/
lemma hasDerivAt_re_arcZ (η : ℝ) (hη : 0 < η) (w : ℝ) :
    HasDerivAt (fun u : ℝ => (Work.Drive.N2Lead.arcZ η u).re)
      (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w)).re w := by
  have h := hasDerivAt_arcZ η hη w
  have hF : HasFDerivAt (fun u : ℝ => Work.Drive.N2Lead.arcZ η u)
      (ContinuousLinearMap.toSpanSingleton ℝ (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w))) w :=
    h.hasFDerivAt
  have hF2 : HasFDerivAt (fun u : ℝ => (Work.Drive.N2Lead.arcZ η u).re)
      (Complex.reCLM.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w)))) w :=
    HasFDerivAt.comp w (ContinuousLinearMap.hasFDerivAt Complex.reCLM) hF
  have h3 := hF2.hasDerivAt
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply] using h3

/-! ## Positivity of the derivative of the real part -/

/-- The principal square root of a complex number of positive real part has positive real part. -/
lemma sqrt_re_pos_of_re_pos {g : ℂ} (hg : 0 < g.re) : 0 < (Complex.sqrt g).re := by
  have h : (Complex.sqrt g).re = Real.sqrt ((‖g‖ + g.re) / 2) := by
    simpa [Complex.sqrt] using Complex.cpow_inv_two_re g
  rw [h]
  apply Real.sqrt_pos.mpr
  have := norm_nonneg g
  linarith

/-- The model arc never vanishes (for `η > 0`). -/
lemma arcZ_ne_zero_of_eta_pos {η : ℝ} (hη : 0 < η) (w : ℝ) :
    Work.Drive.N2Lead.arcZ η w ≠ 0 := by
  intro h
  have h2 : ((Work.Drive.N2Lead.arcZ η w) ^ 2).re = -η := by
    rw [Work.Drive.N2Lead.arcZ_sq]; simp
  rw [h] at h2
  simp at h2
  linarith

/-- The model arc has positive imaginary part: it is `I` times a square root whose real part is
positive (that of `η - I w`). -/
lemma im_arcZ_pos {η : ℝ} (hη : 0 < η) (w : ℝ) :
    0 < (Work.Drive.N2Lead.arcZ η w).im := by
  have hre : 0 < ((η:ℂ) - (w:ℂ) * Complex.I).re := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, mul_one]
    linarith
  have h := sqrt_re_pos_of_re_pos hre
  rw [Work.Drive.N2Lead.arcZ, Complex.mul_im, Complex.I_re, Complex.I_im]
  simpa using h

/-- `(I / (2 * arcZ η w)).re = Im (arcZ η w) / (2 * ‖arcZ η w‖²) > 0`. -/
lemma deriv_re_arcZ_pos {η : ℝ} (hη : 0 < η) (w : ℝ) :
    0 < (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w)).re := by
  set z := Work.Drive.N2Lead.arcZ η w with hz
  have hzim : 0 < z.im := im_arcZ_pos hη w
  have hz0 : z ≠ 0 := arcZ_ne_zero_of_eta_pos hη w
  have h1 : (2 * z).im = 2 * z.im := by simp
  have h2 : Complex.normSq (2 * z) = 4 * Complex.normSq z := by
    rw [map_mul]
    norm_num [Complex.normSq_apply]
  rw [Complex.div_re]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul]
  rw [h1, h2]
  have h3 : 0 < Complex.normSq z := by rw [Complex.normSq_pos]; exact hz0
  positivity

end Work.Drive.N2Lead.ReStrictMono

namespace Work.Drive.N2Lead

open scoped ContDiff Topology

theorem arcZ_re_strictMono {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ 1 (fun w : ℝ => Work.Drive.N2Lead.arcZ η w) ∧
      ∀ w : ℝ, 0 < deriv (fun u : ℝ => (Work.Drive.N2Lead.arcZ η u).re) w := by
  have hd : ∀ w : ℝ, HasDerivAt (fun u : ℝ => Work.Drive.N2Lead.arcZ η u)
      (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w)) w :=
    fun w => ReStrictMono.hasDerivAt_arcZ η hη w
  constructor
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun w => (hd w).differentiableAt, ?_⟩
    have hderiv : deriv (fun u : ℝ => Work.Drive.N2Lead.arcZ η u)
        = fun w : ℝ => Complex.I / (2 * Work.Drive.N2Lead.arcZ η w) := by
      funext w
      exact (hd w).deriv
    rw [hderiv]
    have hcont : Continuous (fun w : ℝ => Work.Drive.N2Lead.arcZ η w) :=
      Differentiable.continuous fun w => (hd w).differentiableAt
    have h2 : Continuous (fun w : ℝ => (2 : ℂ) * Work.Drive.N2Lead.arcZ η w) :=
      continuous_const.mul hcont
    exact Continuous.div continuous_const h2
      (fun w => mul_ne_zero two_ne_zero (ReStrictMono.arcZ_ne_zero_of_eta_pos hη w))
  · intro w
    rw [(ReStrictMono.hasDerivAt_re_arcZ η hη w).deriv]
    exact ReStrictMono.deriv_re_arcZ_pos hη w

end Work.Drive.N2Lead
