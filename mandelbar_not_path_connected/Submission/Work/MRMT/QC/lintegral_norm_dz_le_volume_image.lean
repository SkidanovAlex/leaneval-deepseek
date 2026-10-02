import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory Complex Function Filter
open scoped Topology ENNReal

/-! ## The area (change-of-variables) bound for a quasiconformal map

We prove `∫⁻_{B(0,R)} ‖∂φ‖² ≤ (1-k²)⁻¹ · vol (φ '' B(0,R))` for `φ` quasiconformal on `ℂ`
with dilatation `μ` bounded by `k < 1` a.e.

The proof has three ingredients:

* the algebraic identity `det L = ‖∂L‖² - ‖∂̄L‖²` for a real-linear map `L : ℂ → ℂ`
  (`clm_det_eq_normSq`), which together with `∂̄φ = μ ∂φ` gives the pointwise bound
  `‖∂φ z‖² ≤ (1-k²)⁻¹ |det (fderiv ℝ φ z)|` a.e.;
* Mathlib's change of variables formula `lintegral_abs_det_fderiv_eq_addHaar_image`, applied to
  the measurable set of differentiability points of `φ`, where `fderiv ℝ φ = 0` off it;
* elementary `lintegral` manipulations. -/

/-- **Wirtinger derivatives and the determinant of a real-linear map.**  For a real-linear
`L : ℂ →L[ℝ] ℂ` with `∂L = (L 1 - I * L I)/2` and `∂̄L = (L 1 + I * L I)/2` one has
`det L = ‖∂L‖² - ‖∂̄L‖²`. -/
theorem clm_det_eq_normSq {L : ℂ →L[ℝ] ℂ} :
    L.det = ‖(L 1 - Complex.I * L Complex.I) / 2‖ ^ 2
             - ‖(L 1 + Complex.I * L Complex.I) / 2‖ ^ 2 := by
  -- in the real basis `(1, I)` the matrix of `L` is `![![a.re, a.im], ![b.re, b.im]]`
  -- where `a = L 1`, `b = L I`, and `det = a.re * b.im - b.re * a.im`;
  -- writing `a = ∂L + ∂̄L`, `b = I (∂L - ∂̄L)` this is `‖∂L‖² - ‖∂̄L‖²`.
  have key : ∀ A B : ℂ, (‖A - Complex.I * B‖ / 2) ^ 2 - (‖A + Complex.I * B‖ / 2) ^ 2
      = A.re * B.im - B.re * A.im := by
    intro A B
    rw [div_pow, div_pow, ← sub_div]
    norm_num
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI (L : ℂ →ₗ[ℝ] ℂ),
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
  norm_num
  exact (key (L 1) (L Complex.I)).symm

/-- The determinant of the zero real-linear endomorphism of `ℂ`. -/
theorem clm_det_zero : (0 : ℂ →L[ℝ] ℂ).det = 0 := by
  have h := clm_det_eq_normSq (L := 0)
  simpa using h

/-- `det (fderiv ℝ φ z) = ‖∂φ(z)‖² - ‖∂̄φ(z)‖²`. -/
theorem det_fderiv_eq (φ : ℂ → ℂ) (z : ℂ) :
    (fderiv ℝ φ z).det = ‖Work.MRMT.dz φ z‖ ^ 2 - ‖Work.MRMT.dzbar φ z‖ ^ 2 := by
  rw [clm_det_eq_normSq]
  simp only [Work.MRMT.dz, Work.MRMT.dzbar]

/-- **Pointwise bound a.e.**  If `∂̄φ = μ ∂φ` a.e. and `‖μ‖ ≤ k` a.e. with `0 ≤ k < 1`, then
a.e. `‖∂φ z‖² ≤ (1-k²)⁻¹ |det (fderiv ℝ φ z)|`.  (At points where `φ` is not differentiable all
the junk values are `0`.) -/
theorem ofReal_normSq_dz_le_det {φ μ : ℂ → ℂ} {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hrel : ∀ᵐ z ∂(volume : Measure ℂ), Work.MRMT.dzbar φ z = μ z * Work.MRMT.dz φ z) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ENNReal.ofReal (‖Work.MRMT.dz φ z‖ ^ 2) ≤
        ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ φ z).det| := by
  have hpos : 0 < 1 - k ^ 2 := by nlinarith
  filter_upwards [hμ, hrel] with z hz hzr
  by_cases hd : DifferentiableAt ℝ φ z
  · have hdet := det_fderiv_eq φ z
    have hnorm : ‖Work.MRMT.dzbar φ z‖ ≤ k * ‖Work.MRMT.dz φ z‖ := by
      rw [hzr, norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    have hnorm2 : ‖Work.MRMT.dzbar φ z‖ ^ 2 ≤ k ^ 2 * ‖Work.MRMT.dz φ z‖ ^ 2 := by
      calc ‖Work.MRMT.dzbar φ z‖ ^ 2 ≤ (k * ‖Work.MRMT.dz φ z‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = k ^ 2 * ‖Work.MRMT.dz φ z‖ ^ 2 := by ring
    have hmain : (1 - k ^ 2) * ‖Work.MRMT.dz φ z‖ ^ 2 ≤ (fderiv ℝ φ z).det := by
      rw [hdet]; nlinarith
    have hdetnn : 0 ≤ (fderiv ℝ φ z).det := by
      nlinarith [mul_nonneg hpos.le (sq_nonneg ‖Work.MRMT.dz φ z‖)]
    have hineq : ‖Work.MRMT.dz φ z‖ ^ 2 ≤ (1 - k ^ 2)⁻¹ * |(fderiv ℝ φ z).det| := by
      rw [abs_of_nonneg hdetnn]
      exact (le_inv_mul_iff₀ hpos).2 hmain
    calc ENNReal.ofReal (‖Work.MRMT.dz φ z‖ ^ 2)
        ≤ ENNReal.ofReal ((1 - k ^ 2)⁻¹ * |(fderiv ℝ φ z).det|) :=
          ENNReal.ofReal_le_ofReal hineq
      _ = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ φ z).det| :=
          ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)
  · have h0 : fderiv ℝ φ z = 0 := fderiv_zero_of_not_differentiableAt (𝕜 := ℝ) hd
    have hz0 : Work.MRMT.dz φ z = 0 := by simp [Work.MRMT.dz, h0]
    rw [hz0, h0, clm_det_zero]
    simp

/-- **Area bound for a QC map.** For `φ` quasiconformal on `ℂ` with dilatation `μ` bounded by `k`
a.e. (`0 ≤ k < 1`), the `L²` norm of `dz φ` over a ball is controlled by the area of the image of
that ball: `∫⁻_{B(0,R)} ‖dz φ‖² ≤ (1-k²)⁻¹ · vol (φ '' B(0,R))`.

Hints for the prover: (i) for a real-linear map `L : ℂ →L[ℝ] ℂ` one has
`L.det = ‖dzL‖² - ‖dzbarL‖²` where `dzL = (L 1 - I * L I)/2`, `dzbarL = (L 1 + I * L I)/2`;
(ii) `IsQCOn φ univ μ` gives `∀ᵐ z, dzbar φ z = μ z * dz φ z`, so a.e.
`|det (fderiv ℝ φ z)| = det (fderiv ℝ φ z) ≥ (1-k²) ‖dz φ z‖²`;
(iii) apply Mathlib's change of variables formula
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` to `f := φ` on the measurable set
`s = {x | DifferentiableAt ℝ φ x}` (measurable by `measurableSet_of_differentiableAt`), using
`InjOn φ s` from the homeomorphism in `IsQCOn`, and `|det(fderiv ℝ φ x)| = 0` at points where `φ`
is not differentiable (the junk value of `fderiv` is `0`), to get
`∫⁻_{B(0,R)} ‖det (fderiv ℝ φ)‖ ≤ volume (φ '' B(0,R))`. -/
theorem lintegral_norm_dz_le_volume_image {φ μ : ℂ → ℂ} {k R : ℝ}
    (hφ : Work.MRMT.IsQCOn φ Set.univ μ) (hk : 0 ≤ k) (hk1 : k < 1)
    (hμ : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∫⁻ z in Metric.ball 0 R, ENNReal.ofReal (‖Work.MRMT.dz φ z‖ ^ 2) ≤
      ENNReal.ofReal ((1 - k ^ 2)⁻¹) * MeasureTheory.volume (φ '' Metric.ball 0 R) := by
  -- `φ` is a homeomorphism of `ℂ` onto its image, hence injective
  obtain ⟨-, hhomeo, -, -, hrel'⟩ := hφ
  obtain ⟨-, ginv, -, hgl, -⟩ := hhomeo
  have hinj : Function.Injective φ := by
    intro a b hab
    have ha := hgl a (Set.mem_univ a)
    have hb := hgl b (Set.mem_univ b)
    rw [hab] at ha
    exact ha.symm.trans hb
  -- the a.e. Beltrami equation, on all of `ℂ`
  have hrel : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Work.MRMT.dzbar φ z = μ z * Work.MRMT.dz φ z := by
    filter_upwards [hrel'] with z hz
    simpa using hz
  have hae := ofReal_normSq_dz_le_det (φ := φ) (μ := μ) hk hk1 hμ hrel
  set B : Set ℂ := Metric.ball 0 R with hBdef
  set s : Set ℂ := {x : ℂ | DifferentiableAt ℝ φ x} with hsdef
  have hBmeas : MeasurableSet B := by rw [hBdef]; exact Metric.isOpen_ball.measurableSet
  have hsmeas : MeasurableSet s := by rw [hsdef]; exact measurableSet_of_differentiableAt ℝ φ
  have hBs : MeasurableSet (B ∩ s) := hBmeas.inter hsmeas
  have hBd : MeasurableSet (B \ s) := hBmeas.diff hsmeas
  -- on the differentiability set, `fderiv ℝ φ` is a genuine derivative
  have hderiv : ∀ x ∈ B ∩ s, HasFDerivWithinAt φ (fderiv ℝ φ x) (B ∩ s) x := by
    intro x hx
    have hd : DifferentiableAt ℝ φ x := by simpa [hsdef] using hx.2
    exact hd.hasFDerivAt.hasFDerivWithinAt
  -- change of variables on `B ∩ s`
  have hcov : ∫⁻ x in B ∩ s, ENNReal.ofReal |(fderiv ℝ φ x).det| = volume (φ '' (B ∩ s)) :=
    lintegral_abs_det_fderiv_eq_addHaar_image volume hBs hderiv (fun a _ b _ h => hinj h)
  -- off the differentiability set the determinant vanishes, so the integral over `B` is the one
  -- over `B ∩ s`
  have hsplit : ∫⁻ x in B, ENNReal.ofReal |(fderiv ℝ φ x).det|
      = ∫⁻ x in B ∩ s, ENNReal.ofReal |(fderiv ℝ φ x).det| := by
    have hdisj : Disjoint (B ∩ s) (B \ s) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx'.2 hx.2
    have hunion : (B ∩ s) ∪ (B \ s) = B := by
      ext x
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro hx
        by_cases hxs : x ∈ s
        · exact Or.inl ⟨hx, hxs⟩
        · exact Or.inr ⟨hx, hxs⟩
    have hzero : ∫⁻ x in B \ s, ENNReal.ofReal |(fderiv ℝ φ x).det| = 0 := by
      have h1 : (fun x : ℂ => ENNReal.ofReal |(fderiv ℝ φ x).det|)
          =ᵐ[volume.restrict (B \ s)] (fun _ => 0) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' hBd]
        filter_upwards with x hx
        have hnd : ¬ DifferentiableAt ℝ φ x := by simpa [hsdef] using hx.2
        rw [fderiv_zero_of_not_differentiableAt (𝕜 := ℝ) hnd, clm_det_zero]
        simp
      rw [lintegral_congr_ae h1]
      simp
    conv_lhs => rw [← hunion]
    rw [lintegral_union (μ := volume) hBd hdisj, hzero, add_zero]
  -- pull the constant out of the integral
  have hconst : ∫⁻ x in B, ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ φ x).det|
      = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ∫⁻ x in B, ENNReal.ofReal |(fderiv ℝ φ x).det| :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hstep1 : ∫⁻ x in B, ENNReal.ofReal (‖Work.MRMT.dz φ x‖ ^ 2) ≤
      ∫⁻ x in B, ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ φ x).det| :=
    setLIntegral_mono_ae' hBmeas (hae.mono (fun z hz _ => hz))
  have hmono : ENNReal.ofReal ((1 - k ^ 2)⁻¹) * volume (φ '' (B ∩ s))
      ≤ ENNReal.ofReal ((1 - k ^ 2)⁻¹) * volume (φ '' B) :=
    mul_le_mul_right (measure_mono (Set.image_mono Set.inter_subset_left)) _
  calc ∫⁻ z in B, ENNReal.ofReal (‖Work.MRMT.dz φ z‖ ^ 2)
      ≤ ∫⁻ z in B, ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ φ z).det| :=
        hstep1
    _ = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ∫⁻ z in B, ENNReal.ofReal |(fderiv ℝ φ z).det| :=
        hconst
    _ = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ∫⁻ z in B ∩ s, ENNReal.ofReal |(fderiv ℝ φ z).det| := by
        rw [hsplit]
    _ = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * volume (φ '' (B ∩ s)) := by rw [hcov]
    _ ≤ ENNReal.ofReal ((1 - k ^ 2)⁻¹) * volume (φ '' B) := hmono

end Work.MRMT.QC
