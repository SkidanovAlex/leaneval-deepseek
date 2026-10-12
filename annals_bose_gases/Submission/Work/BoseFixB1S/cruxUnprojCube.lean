import Mathlib
import Submission.Work.BoseFixB1S.cubeFamFormFtruncTendsto2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)


section Helpers

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal Convolution
open _root_.BoseGases Submission.BoseGases

set_option maxHeartbeats 1600000

/-! ## The `p`-convention Fourier transform of the cube cutoff is the cosine profile -/

/-- **The Fourier transform of the cube bump equals its real cosine profile** (cube analogue of
the proved `Work.OneBodyKin.kinFT_chi_eq`): since `chiSmall M` is even, the sine part of
`kinFT (chiSmall M : E3 → ℂ)` vanishes, leaving `profHatCube M`. -/
theorem cuc_kinFT_chiSmall (M : ℕ) (hM : 1 ≤ M) (p : E3) :
    Submission.BoseGases.kinFT (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p
      = (profHatCube M p : ℂ) := by
  have hcont : Continuous (fun y : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (Submission.BoseGases.chiSmall M y : ℂ)) := by
    apply Continuous.mul
    · apply Complex.continuous_exp.comp
      apply Continuous.neg
      apply Continuous.mul continuous_const
      exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
    · exact Complex.continuous_ofReal.comp (Submission.BoseGases.chiSmall_continuous hM)
  have hcs : HasCompactSupport (fun y : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (Submission.BoseGases.chiSmall M y : ℂ)) := by
    refine (Submission.BoseGases.chiSmall_hasCompactSupport hM).mono (fun y hy => ?_)
    intro hchi
    exact hy (by simp [hchi])
  have hf : Integrable (fun y : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (Submission.BoseGases.chiSmall M y : ℂ)) volume :=
    hcont.integrable_of_hasCompactSupport hcs
  have hexp : ∀ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      = ((Real.cos (inner ℝ p y) : ℝ) : ℂ) - ((Real.sin (inner ℝ p y) : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [show -(Complex.I * ((inner ℝ p y : ℝ) : ℂ))
          = ((-(inner ℝ p y) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hpt : ∀ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (Submission.BoseGases.chiSmall M y : ℂ)
      = ((Submission.BoseGases.chiSmall M y * Real.cos (inner ℝ p y) : ℝ) : ℂ)
        + ((-(Submission.BoseGases.chiSmall M y * Real.sin (inner ℝ p y)) : ℝ) : ℂ)
            * Complex.I := by
    intro y
    rw [hexp y]
    push_cast
    ring
  have hre_pt : ∀ y : E3, (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (Submission.BoseGases.chiSmall M y : ℂ)).re
      = Submission.BoseGases.chiSmall M y * Real.cos (inner ℝ p y) := by
    intro y
    rw [hpt y]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him_pt : ∀ y : E3, (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (Submission.BoseGases.chiSmall M y : ℂ)).im
      = -(Submission.BoseGases.chiSmall M y * Real.sin (inner ℝ p y)) := by
    intro y
    rw [hpt y]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [Submission.BoseGases.kinFT]
  change (∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      * (Submission.BoseGases.chiSmall M y : ℂ)) = (profHatCube M p : ℂ)
  apply Complex.ext
  · have hre : (∫ y : E3,
          Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (Submission.BoseGases.chiSmall M y : ℂ)).re
        = ∫ y : E3,
          (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (Submission.BoseGases.chiSmall M y : ℂ)).re := by
      have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
      simpa using this.symm
    rw [hre]
    rw [show (∫ y : E3,
            (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
              * (Submission.BoseGases.chiSmall M y : ℂ)).re)
          = ∫ y : E3, Submission.BoseGases.chiSmall M y * Real.cos (inner ℝ p y) from by
      apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ hre_pt]
    simp [profHatCube]
  · have him : (∫ y : E3,
          Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (Submission.BoseGases.chiSmall M y : ℂ)).im
        = ∫ y : E3,
          (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
            * (Submission.BoseGases.chiSmall M y : ℂ)).im := by
      have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hf
      simpa using this.symm
    rw [him]
    rw [show (∫ y : E3,
            (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
              * (Submission.BoseGases.chiSmall M y : ℂ)).im)
          = ∫ y : E3, -(Submission.BoseGases.chiSmall M y * Real.sin (inner ℝ p y)) from by
      apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ him_pt]
    rw [MeasureTheory.integral_neg]
    have hzero : (∫ y : E3,
        Submission.BoseGases.chiSmall M y * Real.sin (inner ℝ p y)) = 0 := by
      have hinv := MeasureTheory.integral_neg_eq_self
        (fun y : E3 => Submission.BoseGases.chiSmall M y * Real.sin (inner ℝ p y))
        (volume : Measure ℝ³)
      have hshift : (∫ y : E3,
            (fun y : E3 => Submission.BoseGases.chiSmall M y * Real.sin (inner ℝ p y)) (-y))
          = -(∫ y : E3,
              Submission.BoseGases.chiSmall M y * Real.sin (inner ℝ p y)) := by
        rw [← MeasureTheory.integral_neg]
        apply integral_congr_ae
        exact MeasureTheory.ae_of_all _ (fun y => by
          simp only [inner_neg_right, Real.sin_neg, Submission.BoseGases.chiSmall_even hM]
          ring)
      rw [hshift] at hinv
      linarith
    rw [hzero, neg_zero]
    simp

/-! ## The cube family form in Fourier space (the `L¹`-symbol identity, inlined)

The declarations below are the (renamed) content of `Submission.Work.BoseFixB1S.cubeFamFormEqSymbol`
(proved there), inlined here because that module imports this one for `cuc_kinFT_chiSmall`.
-/



set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## 1. The cube overlap kernel: continuity, compact support, integrability -/

/-- `convScaleCube M a` is `(fun z ↦ conv3Small M (a⁻¹ • z))`, definitionally. -/
private lemma cuc_convScaleCube_eq_conv3Small_fun (M : ℕ) (a : ℝ) :
    convScaleCube M a = fun z : E3 => Submission.BoseGases.conv3Small M (a⁻¹ • z) := by
  funext z
  rfl

/-- `convScaleCube M a` is continuous (`1 ≤ M`). -/
theorem cuc_continuous_convScaleCube (M : ℕ) (hM : 1 ≤ M) (a : ℝ) :
    Continuous (convScaleCube M a) := by
  rw [cuc_convScaleCube_eq_conv3Small_fun M a]
  exact (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)

/-- `conv3Small M` has compact support (`1 ≤ M`), being the convolution `χ_M ⋆ χ_M`. -/
private lemma cuc_hasCompactSupport_conv3Small (M : ℕ) (hM : 1 ≤ M) :
    HasCompactSupport (fun x : E3 => Submission.BoseGases.conv3Small M x) := by
  rw [Submission.BoseGases.conv3Small_eq_convolution M]
  exact (Submission.BoseGases.chiSmall_hasCompactSupport hM).convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) (Submission.BoseGases.chiSmall_hasCompactSupport hM)

/-- `convScaleCube M a` has compact support for `a ≠ 0`: it is the dilation of `conv3Small M`. -/
theorem cuc_hasCompactSupport_convScaleCube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : a ≠ 0) :
    HasCompactSupport (convScaleCube M a) := by
  rw [cuc_convScaleCube_eq_conv3Small_fun M a]
  have h := (cuc_hasCompactSupport_conv3Small M hM).comp_homeomorph
    (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha))
  simpa [Homeomorph.smulOfNeZero, Function.comp_def] using h

/-- **The cube overlap kernel is `L¹`**: continuous with compact support. -/
theorem cuc_integrable_convScaleCube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : a ≠ 0) :
    MeasureTheory.Integrable (convScaleCube M a) :=
  (cuc_continuous_convScaleCube M hM a).integrable_of_hasCompactSupport
    (cuc_hasCompactSupport_convScaleCube M hM ha)

/-- The convolution kernel `convScaleCube M a · kinKernel F` of the unprojected family form is
integrable: `convScaleCube M a ∈ L¹` and `kinKernel F` is bounded (`kinKernel_bdd`). -/
theorem cuc_integrable_convScaleCube_mul_kinKernel (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : a ≠ 0)
    {F : ℝ → ℝ} (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) :
    MeasureTheory.Integrable
      (fun z : E3 => convScaleCube M a z * Submission.BoseGases.kinKernel F z) := by
  refine (cuc_integrable_convScaleCube M hM ha).mul_bdd
    (c := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖)
    ((Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable hFi).aestronglyMeasurable) ?_
  filter_upwards with z
  exact Work.SmallBoxBridge.Resolve.kinKernel_bdd F hFi z

/-! ## 2. Evenness of the cube profile, and the change of variables in `symACube` -/

/-- `profHatCube M` is even (it is the cosine transform of `chiSmall M`). -/
private lemma cuc_profHatCube_even (M : ℕ) (p : E3) : profHatCube M (-p) = profHatCube M p := by
  unfold profHatCube
  apply integral_congr_ae
  filter_upwards with z
  rw [inner_neg_left, Real.cos_neg]

/-- The symbol `symACube M a F q = (2π)⁻³∫_p F‖q + a⁻¹•p‖ profHatCube(p)²` with the `F`-factor
carrying the momentum: the dilation `v = a • x` (`v`-volume factor `a³`), the translation
`x = p − q` and the evenness of `profHatCube` give

  `symACube M a F q = (2π)⁻³ · a³ ∫_p F‖p‖ · profHatCube(a • (q − p))²`. -/
theorem cuc_symACube_eq_shiftedIntegral (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ)
    (q : E3) :
    symACube M a F q = ((2 * Real.pi) ^ 3)⁻¹ *
      (a ^ 3 * ∫ p : E3, F ‖p‖ * (profHatCube M (a • (q - p))) ^ 2) := by
  have hdil : (∫ v : E3, F ‖q + a⁻¹ • v‖ * (profHatCube M v) ^ 2)
      = a ^ 3 * ∫ x : E3, F ‖q + x‖ * (profHatCube M (a • x)) ^ 2 := by
    rw [Submission.BoseGases.integral_comp_smul_right
      (fun v : E3 => F ‖q + a⁻¹ • v‖ * (profHatCube M v) ^ 2) ha]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    have hx : a⁻¹ • (a • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
    rw [hx]
  have htr : (∫ x : E3, F ‖q + x‖ * (profHatCube M (a • x)) ^ 2)
      = ∫ p : E3, F ‖p‖ * (profHatCube M (a • (p - q))) ^ 2 := by
    rw [← Submission.BoseGases.integral_comp_add_left
      (fun p : E3 => F ‖p‖ * (profHatCube M (a • (p - q))) ^ 2) q]
    apply integral_congr_ae
    filter_upwards with x
    have h1 : q + x - q = x := by abel
    rw [h1]
  have heven : (∫ p : E3, F ‖p‖ * (profHatCube M (a • (p - q))) ^ 2)
      = ∫ p : E3, F ‖p‖ * (profHatCube M (a • (q - p))) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with p
    have h1 : a • (p - q) = -(a • (q - p)) := by module
    rw [h1, cuc_profHatCube_even]
  unfold symACube
  rw [hdil, htr, heven]

/-! ## 3. The Fourier transform of the cube overlap kernel -/

/-- The two-phase product formula around a shift:
`e^{i⟪p,z⟫}·e^{-i⟪q,z⟫} = e^{-i⟪q−p,z⟫}`. -/
private lemma cuc_exp_inner_mul_exp_inner_neg (p q z : E3) :
    Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ (q - p) z : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_sub_left]
  push_cast
  ring

/-- **The convolution theorem at the cube bump**: `kinFT (χ_M ⋆ χ_M) = profHatCube M²`.  Cube
analogue of the proved `Work.OneBodyKin.kinFT_conv3_chi`; the sine part of `kinFT χ_M` vanishes by
evenness (`cuc_kinFT_chiSmall`). -/
theorem cuc_kinFT_conv3Small_eq_profHatCube_sq (M : ℕ) (hM : 1 ≤ M) (p : E3) :
    Submission.BoseGases.kinFT (fun w : E3 => (Submission.BoseGases.conv3Small M w : ℂ)) p
      = (profHatCube M p : ℂ) ^ 2 := by
  have hχ : MeasureTheory.Integrable (fun y : E3 => (Submission.BoseGases.chiSmall M y : ℂ)) :=
    Complex.ofRealCLM.integrable_comp
      ((Submission.BoseGases.chiSmall_continuous hM).integrable_of_hasCompactSupport
        (Submission.BoseGases.chiSmall_hasCompactSupport hM))
  have hconv : (fun w : E3 => ((Submission.BoseGases.conv3Small M w : ℝ) : ℂ))
      = (fun y : E3 => (Submission.BoseGases.chiSmall M y : ℂ))
          ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun y : E3 => (Submission.BoseGases.chiSmall M y : ℂ)) := by
    funext x
    rw [convolution_mul]
    simp only [Submission.BoseGases.conv3Small]
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ (fun t => ?_))
    simp only [Complex.ofReal_mul]
  rw [hconv, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
    Real.fourier_mul_convolution_eq hχ hχ]
  rw [← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, cuc_kinFT_chiSmall M hM]
  ring

/-- **The Fourier transform of the scaled cube autocorrelation.**  With
`convScaleCube M a z = (χ_M ⋆ χ_M)(z/a)` and the `p`-convention Fourier transform `kinFT`, the
substitution `z = a•w` gives

    `∫_z (χ_M⋆χ_M)(z/a)·e^{−i⟪q,z⟫} dz = a³ · kinFT (χ_M⋆χ_M) (a q)`.

Cube analogue of the proved `Work.OneBodyKin.fourier_convScale_scaling`. -/
private lemma cuc_fourier_convScaleCube_scaling (M : ℕ) {a : ℝ} (ha : 0 < a) (q : E3) :
    (∫ z : E3, (convScaleCube M a z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = (a : ℂ) ^ 3 * Submission.BoseGases.kinFT
          (fun w : E3 => (Submission.BoseGases.conv3Small M w : ℂ)) (a • q) := by
  have hpt : ∀ w : E3,
      (convScaleCube M a (a • w) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q (a • w) : ℂ)))
        = Complex.exp (-(Complex.I * (inner ℝ (a • q) w : ℂ))) *
          ((Submission.BoseGases.conv3Small M w : ℝ) : ℂ) := by
    intro w
    have hcs : convScaleCube M a (a • w) = Submission.BoseGases.conv3Small M w := by
      show Submission.BoseGases.conv3Small M (a⁻¹ • (a • w)) = Submission.BoseGases.conv3Small M w
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
    have hinner : inner ℝ q (a • w) = inner ℝ (a • q) w := by
      rw [inner_smul_right, inner_smul_left]
      simp
    rw [hcs, hinner, mul_comm]
  rw [Work.OneBodyKin.integral_eq_smul_integral_comp_smul
    (g := fun z : E3 => (convScaleCube M a z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))) ha]
  rw [show (∫ s : E3, (fun z : E3 => (convScaleCube M a z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))) (a • s))
      = ∫ w : E3, Complex.exp (-(Complex.I * (inner ℝ (a • q) w : ℂ))) *
        ((Submission.BoseGases.conv3Small M w : ℝ) : ℂ) from by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpt]
  rw [Submission.BoseGases.kinFT, Complex.real_smul, Complex.ofReal_pow]

/-- **The Fourier transform of the scaled cube autocorrelation, in closed form**:
`∫_z convScaleCube M a z · e^{−i⟪q,z⟫}dz = a³ · profHatCube M (a q)²`.  Cube analogue of the proved
`Work.OneBodyKin.fourier_convScale`. -/
theorem cuc_fourier_convScaleCube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (q : E3) :
    (∫ z : E3, (convScaleCube M a z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = (a : ℂ) ^ 3 * ((profHatCube M (a • q) : ℝ) : ℂ) ^ 2 := by
  rw [cuc_fourier_convScaleCube_scaling M ha q, cuc_kinFT_conv3Small_eq_profHatCube_sq M hM (a • q)]

/-! ## 4. The window-generic Fubini computation -/

set_option maxHeartbeats 3200000 in
/-- **The Fourier transform of `κ · kinKernel F` for a window family `κ`.**  If `κ ∈ L¹(ℝ³)` has
Fourier transform `∫_z κ z·e^{−i⟪r,z⟫}dz = s·G r`, then for a radial symbol `F(‖·‖)` and any `q`

  `∫_z κ z·kinKernel F z·e^{−i⟪q,z⟫}dz = (2π)⁻³ · s · ∫_p F‖p‖·G(q−p) dp`.

The proof expands `kinKernel F z = kinKernelC F z = (2π)⁻³∫_p F‖p‖·e^{i⟪p,z⟫}dp`, interchanges the
`(z,p)`-integrals (dominated by the product `κ ⊗ F`, integrable for the product measure), evaluates
the `z`-integral at fixed `p` by the hypothesis on `κ`, and folds the `p`-integral back to a real
integral.  This is exactly the computation of the proved
`Work.OneBodyKin.ftKernelConvScale_eq_symA_core`, with the window family abstracted. -/
theorem cuc_ftKernel_eq_smul_integral_of_fourier
    {κ : E3 → ℝ} (hκ : MeasureTheory.Integrable κ)
    {s : ℝ} {G : E3 → ℝ}
    (hft : ∀ r : E3, (∫ z : E3, (κ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ r z : ℂ))))
      = (s : ℂ) * ((G r : ℝ) : ℂ))
    {F : ℝ → ℝ} (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) (q : E3) :
    (∫ z : E3, (κ z : ℂ) * (Submission.BoseGases.kinKernel F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ((((2 * Real.pi) ^ 3)⁻¹ * (s * ∫ p : E3, F ‖p‖ * G (q - p)) : ℝ) : ℂ) := by
  set Φ : E3 → E3 → ℂ := fun z p =>
      (κ z : ℂ) * ((F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))) with hΦ
  -- joint integrability of the `(z,p)`-integrand: it is dominated by the product
  -- `‖κ z‖ · ‖F ‖p‖‖`, which is integrable for the product measure
  have hΦint : MeasureTheory.Integrable (Function.uncurry Φ) (volume.prod volume) := by
    have hdom : MeasureTheory.Integrable
        (fun w : E3 × E3 => ‖κ w.1‖ * ‖F ‖w.2‖‖) (volume.prod volume) :=
      hκ.norm.mul_prod hFi.norm
    refine Integrable.mono' hdom ?_ ?_
    · have h1 : AEStronglyMeasurable (fun w : E3 × E3 => (κ w.1 : ℂ))
          (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hκ.aestronglyMeasurable.comp_fst
      have h2 : AEStronglyMeasurable (fun w : E3 × E3 => (F ‖w.2‖ : ℂ))
          (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hFi.aestronglyMeasurable.comp_snd
      have h3 : Continuous (fun w : E3 × E3 =>
          Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) := by
        apply Complex.continuous_exp.comp
        exact continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_snd.prodMk continuous_fst)))
      have h4 : Continuous (fun w : E3 × E3 =>
          Complex.exp (-(Complex.I * (inner ℝ q w.1 : ℂ)))) := by
        apply Complex.continuous_exp.comp
        apply Continuous.neg
        exact continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_const.prodMk continuous_fst)))
      have h5 : AEStronglyMeasurable (fun w : E3 × E3 =>
          (κ w.1 : ℂ) * ((F ‖w.2‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) *
            Complex.exp (-(Complex.I * (inner ℝ q w.1 : ℂ)))) (volume.prod volume) := by
        convert (h1.mul (h2.mul h3.aestronglyMeasurable)).mul h4.aestronglyMeasurable using 1
        all_goals
          funext w
          simp only [Pi.mul_apply]
      change AEStronglyMeasurable (fun w : E3 × E3 => Φ w.1 w.2) (volume.prod volume)
      exact h5
    · filter_upwards with w
      simp only [Function.uncurry, hΦ, norm_mul, Work.SmallBoxBridge.Resolve.cnorm_ofReal,
        Work.SmallBoxBridge.Resolve.norm_exp_I_mul,
        Work.SmallBoxBridge.Resolve.norm_exp_neg_I_mul, mul_one]
      exact le_of_eq (by ring)
  -- the kernel is the constant `(2π)⁻³` times its `e^{i⟪p,z⟫}`-integral
  have hstep1 : (∫ z : E3, (κ z : ℂ) * (Submission.BoseGases.kinKernel F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ z : E3, ∫ p : E3, Φ z p := by
    have hper : ∀ z : E3, (κ z : ℂ) * (Submission.BoseGases.kinKernel F z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))
        = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : E3, Φ z p := by
      intro z
      rw [← Work.SmallBoxBridge.Kernel.kinKernelC_eq_ofReal F z,
        Submission.BoseGases.kinKernelC]
      simp only [hΦ]
      rw [integral_mul_const, integral_const_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hper), integral_const_mul]
  -- Fubini in `(z,p)`
  have hstep2 : (∫ z : E3, ∫ p : E3, Φ z p) = ∫ p : E3, ∫ z : E3, Φ z p :=
    MeasureTheory.integral_integral_swap hΦint
  -- the `z`-integral at fixed `p` is `s·G(q−p)` by hypothesis
  have hstep3 : ∀ p : E3, (∫ z : E3, Φ z p)
      = (F ‖p‖ : ℂ) * ((s : ℂ) * ((G (q - p) : ℝ) : ℂ)) := by
    intro p
    have hpt : (fun z : E3 => Φ z p) = fun z : E3 => (F ‖p‖ : ℂ) *
        ((κ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (q - p) z : ℂ)))) := by
      funext z
      simp only [hΦ]
      rw [show (κ z : ℂ) * ((F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))) *
            Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))
          = (F ‖p‖ : ℂ) * ((κ z : ℂ) * (Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
              Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))) from by ring]
      rw [cuc_exp_inner_mul_exp_inner_neg p q z]
    rw [hpt, integral_const_mul, hft (q - p)]
  -- back to the real `p`-integral
  have hstep4 : (∫ p : E3, ∫ z : E3, Φ z p)
      = (((s * ∫ p : E3, F ‖p‖ * G (q - p)) : ℝ) : ℂ) := by
    rw [show (fun p : E3 => ∫ z : E3, Φ z p) = fun p : E3 =>
        (F ‖p‖ : ℂ) * ((s : ℂ) * ((G (q - p) : ℝ) : ℂ)) from funext hstep3]
    rw [show (fun p : E3 => (F ‖p‖ : ℂ) * ((s : ℂ) * ((G (q - p) : ℝ) : ℂ)))
        = fun p : E3 => (((s * (F ‖p‖ * G (q - p))) : ℝ) : ℂ) from by
      funext p
      push_cast
      ring]
    rw [show (∫ p : E3, (((s * (F ‖p‖ * G (q - p))) : ℝ) : ℂ))
        = ((∫ p : E3, (s * (F ‖p‖ * G (q - p))) : ℝ) : ℂ) from integral_ofReal]
    rw [integral_const_mul]
  rw [hstep1, hstep2, hstep4]
  push_cast
  ring

/-! ## 5. The cube instance -/

/-- The Fourier transform of the kernel `convScaleCube M a · kinKernel F` of the unprojected cube
family form, in complex form: with `κ = convScaleCube M a` (`s = a³`, `G = profHatCube M (a•·)²`)
`cuc_ftKernel_eq_smul_integral_of_fourier` and `cuc_fourier_convScaleCube` give

  `∫_z k z·e^{-i⟪q,z⟫}dz = (2π)⁻³ a³ ∫_p F‖p‖ profHatCube(a•(q−p))² dp`. -/
theorem cuc_ftKernelConvScaleCube_eq_symACube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) (q : E3) :
    (∫ z : E3, (convScaleCube M a z : ℂ) * (Submission.BoseGases.kinKernel F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ((((2 * Real.pi) ^ 3)⁻¹ *
          (a ^ 3 * ∫ p : E3, F ‖p‖ * (profHatCube M (a • (q - p))) ^ 2) : ℝ) : ℂ) := by
  refine cuc_ftKernel_eq_smul_integral_of_fourier (κ := convScaleCube M a)
    (cuc_integrable_convScaleCube M hM (ne_of_gt ha)) (s := a ^ 3)
    (G := fun r : E3 => (profHatCube M (a • r)) ^ 2) ?_ hFi q
  intro r
  rw [cuc_fourier_convScaleCube M hM ha r]
  push_cast
  ring

/-- **The Fourier transform of the kernel of the unprojected cube family form.**  The real part of
`∫_z convScaleCube M a z · kinKernel F z · e^{-i⟪q,z⟫}dz` is the symbol `symACube M a F q`. -/
theorem cuc_kinKernel_mul_convScaleCube_fourier_re (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) (q : E3) :
    (∫ z : E3,
        ((convScaleCube M a z * Submission.BoseGases.kinKernel F z : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))).re = symACube M a F q := by
  have h1 : (∫ z : E3,
        ((convScaleCube M a z * Submission.BoseGases.kinKernel F z : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ∫ z : E3, (convScaleCube M a z : ℂ) * (Submission.BoseGases.kinKernel F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Complex.ofReal_mul]
  rw [h1, cuc_ftKernelConvScaleCube_eq_symACube M hM ha hFi q, Complex.ofReal_re,
    cuc_symACube_eq_shiftedIntegral M hM ha F q]

/-! ## 6. The main theorem -/

theorem cuc_cubeFamFormEqSymbol (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hFnn : ∀ r : ℝ, 0 ≤ F r)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Work.BoseFixB1S.bsFamilyFormUnprojCube M a F ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixB1S.symACube M a F q *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  rw [familyFormUnprojCube_eq_kernelForm M hM ha ψ hψ hcs hF hFnn]
  rw [Work.OneBodyKin.quadForm_conv_eq_fourier
    (k := fun z : E3 => convScaleCube M a z * Submission.BoseGases.kinKernel F z)
    (cuc_integrable_convScaleCube_mul_kinKernel M hM (ne_of_gt ha) hF) hψ hcs]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  rw [cuc_kinKernel_mul_convScaleCube_fourier_re M hM ha hF q]


/-! ## The RHS converges along the truncations -/

/-- Continuity of the cube profile in the momentum variable. -/
private lemma profHatCube_continuous (M : ℕ) (hM : 1 ≤ M) :
    Continuous (fun p : E3 => profHatCube M p) := by
  have hcont : Continuous (fun p : E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p) :=
    Work.OneBodyKin.continuous_kinFT
      ((Complex.continuous_ofReal.comp (Submission.BoseGases.chiSmall_continuous hM)
        ).integrable_of_hasCompactSupport
        ((Submission.BoseGases.chiSmall_hasCompactSupport hM).comp_left
          (g := fun r : ℝ => (r : ℂ)) (by simp)))
  have hfun : (fun p : E3 => profHatCube M p) = fun p : E3 =>
      (Submission.BoseGases.kinFT (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p).re := by
    funext p
    rw [cuc_kinFT_chiSmall M hM p]
    rfl
  rw [hfun]
  exact Complex.continuous_re.comp hcont

/-- The one-dimensional `p`-bound `‖q + a⁻¹•p‖² ≤ 2‖q‖² + 2a⁻²‖p‖²`. -/
private lemma norm_add_inv_smul_sq_le {a : ℝ} (ha : 0 < a) (q p : E3) :
    ‖q + a⁻¹ • p‖ ^ 2 ≤ 2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 := by
  have hsplit : ‖q + a⁻¹ • p‖ ≤ ‖q‖ + a⁻¹ * ‖p‖ := by
    calc ‖q + a⁻¹ • p‖ ≤ ‖q‖ + ‖a⁻¹ • p‖ := norm_add_le _ _
      _ = ‖q‖ + a⁻¹ * ‖p‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ a⁻¹)]
  calc ‖q + a⁻¹ • p‖ ^ 2 ≤ (‖q‖ + a⁻¹ * ‖p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsplit 2
    _ ≤ 2 * ‖q‖ ^ 2 + 2 * (a⁻¹ * ‖p‖) ^ 2 := by
        nlinarith [sq_nonneg (‖q‖ - a⁻¹ * ‖p‖)]
    _ = 2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 := by
        rw [mul_pow, inv_pow]
        ring

/-- `fsKinCoeff c r ≤ r² + c²` for `r ≥ 0`. -/
private lemma fsKinCoeff_le_sq_add (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ r ^ 2 + c ^ 2 := by
  rw [show Submission.BoseGases.fsKinCoeff c r = (max (r - c) 0) ^ 2 from rfl]
  have h2 : max (r - c) 0 ≤ |r - c| :=
    max_le (le_abs_self (r - c)) (abs_nonneg (r - c))
  have h3 : (max (r - c) 0) ^ 2 ≤ (r - c) ^ 2 := by
    rw [← sq_abs (r - c)]
    exact pow_le_pow_left₀ (le_max_right _ _) h2 2
  nlinarith [mul_nonneg hr hc]

/-- `Ftrunc c n r ≤ r² + c²` for `r ≥ 0`. -/
private lemma Ftrunc_le_sq_add (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Work.OneBodyKin.Ftrunc c n r ≤ r ^ 2 + c ^ 2 :=
  le_trans (Work.OneBodyKin.Ftrunc_le_fsKinCoeff c n r) (fsKinCoeff_le_sq_add c r hc hr)

/-- Pointwise domination of a symbol integrand by the quadratic `p`-weight. -/
private lemma symAIntegrand_le {a c : ℝ} (ha : 0 < a) {M : ℕ} {G : ℝ → ℝ}
    (hGb : ∀ r, 0 ≤ r → G r ≤ r ^ 2 + c ^ 2) (q p : E3) :
    G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2
      ≤ (2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2 := by
  have h1 := hGb ‖q + a⁻¹ • p‖ (norm_nonneg (q + a⁻¹ • p))
  have h2 := norm_add_inv_smul_sq_le ha q p
  have h3 : G ‖q + a⁻¹ • p‖ ≤ 2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + c ^ 2 := by linarith
  exact mul_le_mul_of_nonneg_right h3 (sq_nonneg (profHatCube M p))

/-- Integrability of the quadratic `p`-weight against `profHatCube²`. -/
private lemma integrable_symAdom {M : ℕ} {a c : ℝ} (q : E3)
    (hI0 : MeasureTheory.Integrable (fun p : E3 => (profHatCube M p) ^ 2))
    (hI1 : MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * (profHatCube M p) ^ 2)) :
    MeasureTheory.Integrable (fun p : E3 =>
      (2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2) := by
  have h1 : MeasureTheory.Integrable
      (fun p : E3 => (2 * ‖q‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2) :=
    hI0.const_mul (2 * ‖q‖ ^ 2 + c ^ 2)
  have h2 : MeasureTheory.Integrable
      (fun p : E3 => (2 * (a ^ 2)⁻¹) * (‖p‖ ^ 2 * (profHatCube M p) ^ 2)) :=
    hI1.const_mul (2 * (a ^ 2)⁻¹)
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Pi.add_apply]
  ring

/-- The value of the quadratic `p`-weight integral. -/
private lemma integral_symAdom {M : ℕ} {a c : ℝ} (q : E3)
    (hI0 : MeasureTheory.Integrable (fun p : E3 => (profHatCube M p) ^ 2))
    (hI1 : MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * (profHatCube M p) ^ 2)) :
    (∫ p : E3, (2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2)
      = 2 * ‖q‖ ^ 2 * (∫ p : E3, (profHatCube M p) ^ 2)
        + 2 * (a ^ 2)⁻¹ * (∫ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2)
        + c ^ 2 * (∫ p : E3, (profHatCube M p) ^ 2) := by
  have h1 : MeasureTheory.Integrable
      (fun p : E3 => (2 * ‖q‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2) :=
    hI0.const_mul (2 * ‖q‖ ^ 2 + c ^ 2)
  have h2 : MeasureTheory.Integrable
      (fun p : E3 => (2 * (a ^ 2)⁻¹) * (‖p‖ ^ 2 * (profHatCube M p) ^ 2)) :=
    hI1.const_mul (2 * (a ^ 2)⁻¹)
  rw [show (fun p : E3 =>
        (2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2)
      = fun p : E3 => (2 * ‖q‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2
          + (2 * (a ^ 2)⁻¹) * (‖p‖ ^ 2 * (profHatCube M p) ^ 2) from by funext p; ring]
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul]
  ring

/-- A.e. strong measurability of a symbol integrand. -/
private lemma aestronglyMeasurable_symAIntegrand {M : ℕ}
    (hpc : Continuous (fun p : E3 => profHatCube M p)) {G : ℝ → ℝ} (hGm : Measurable G)
    (a : ℝ) (q : E3) :
    AEStronglyMeasurable (fun p : E3 => G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2) volume :=
  (hGm.comp (continuous_norm.comp (by fun_prop)).measurable).aestronglyMeasurable.mul
    ((hpc.pow 2).aestronglyMeasurable)

/-- **The `q`-uniform quadratic bound for the cube symbol at a nonnegative symbol dominated by
`r² + c²`**, with constants built from the two moment integrals. -/
theorem cubeSymA_quad_bound {M : ℕ} (hM : 1 ≤ M) {a c : ℝ} (ha : 0 < a)
    (hI0 : MeasureTheory.Integrable (fun p : E3 => (profHatCube M p) ^ 2))
    (hI1 : MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * (profHatCube M p) ^ 2)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ (G : ℝ → ℝ) (hGm : Measurable G) (hGnn : ∀ r, 0 ≤ G r)
        (hGb : ∀ r, 0 ≤ r → G r ≤ r ^ 2 + c ^ 2) (q : E3),
          |symACube M a G q| ≤ A * ‖q‖ ^ 2 + B) := by
  have hpc : Continuous (fun p : E3 => profHatCube M p) := profHatCube_continuous M hM
  set I0 : ℝ := ∫ p : E3, (profHatCube M p) ^ 2 with hI0def
  set I1 : ℝ := ∫ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2 with hI1def
  have hI0nn : 0 ≤ I0 := by rw [hI0def]; exact integral_nonneg (fun p => sq_nonneg _)
  have hI1nn : 0 ≤ I1 := by
    rw [hI1def]; exact integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hcπ : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (2 * I0),
    ((2 * Real.pi) ^ 3)⁻¹ * (2 * (a ^ 2)⁻¹ * I1 + c ^ 2 * I0), ?_, ?_, ?_⟩
  · exact mul_nonneg hcπ.le (by linarith)
  · exact mul_nonneg hcπ.le (add_nonneg (mul_nonneg (by positivity) hI1nn)
      (mul_nonneg (sq_nonneg c) hI0nn))
  · intro G hGm hGnn hGb q
    have hg := integrable_symAdom (M := M) (a := a) (c := c) q hI0 hI1
    have hfint : MeasureTheory.Integrable
        (fun p : E3 => G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2) := by
      refine Integrable.mono' hg (aestronglyMeasurable_symAIntegrand hpc hGm a q) ?_
      filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (hGnn ‖q + a⁻¹ • p‖) (sq_nonneg (profHatCube M p)))]
      exact symAIntegrand_le ha hGb q p
    have hmain : symACube M a G q ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, (2 * ‖q‖ ^ 2 + 2 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + c ^ 2) * (profHatCube M p) ^ 2 := by
      rw [symACube]
      refine mul_le_mul_of_nonneg_left ?_ hcπ.le
      exact MeasureTheory.integral_mono hfint hg (fun p => symAIntegrand_le ha hGb q p)
    have hnonneg : 0 ≤ symACube M a G q := by
      rw [symACube]
      exact mul_nonneg hcπ.le (MeasureTheory.integral_nonneg (fun p =>
        mul_nonneg (hGnn ‖q + a⁻¹ • p‖) (sq_nonneg (profHatCube M p))))
    rw [abs_of_nonneg hnonneg]
    calc symACube M a G q
        ≤ ((2 * Real.pi) ^ 3)⁻¹
            * (2 * ‖q‖ ^ 2 * I0 + 2 * (a ^ 2)⁻¹ * I1 + c ^ 2 * I0) := by
          rw [integral_symAdom q hI0 hI1] at hmain
          rw [← hI0def, ← hI1def] at hmain
          exact hmain
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (2 * I0) * ‖q‖ ^ 2
            + ((2 * Real.pi) ^ 3)⁻¹ * (2 * (a ^ 2)⁻¹ * I1 + c ^ 2 * I0) := by ring

/-- **Pointwise convergence along the radial truncations of the cube symbol.** -/
theorem cubeSymA_Ftrunc_pt {M : ℕ} (hM : 1 ≤ M) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hI0 : MeasureTheory.Integrable (fun p : E3 => (profHatCube M p) ^ 2))
    (hI1 : MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * (profHatCube M p) ^ 2))
    (q : E3) :
    Filter.Tendsto (fun n : ℕ => symACube M a (Work.OneBodyKin.Ftrunc c n) q) Filter.atTop
      (nhds (symACube M a (Submission.BoseGases.fsKinCoeff c) q)) := by
  have hpc : Continuous (fun p : E3 => profHatCube M p) := profHatCube_continuous M hM
  have hg := integrable_symAdom (M := M) (a := a) (c := c) q hI0 hI1
  have hmain : Filter.Tendsto (fun n : ℕ =>
      ∫ p : E3, Work.OneBodyKin.Ftrunc c n ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2)
      Filter.atTop
      (nhds (∫ p : E3,
        Submission.BoseGases.fsKinCoeff c ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2)) := by
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (f := fun n p => Work.OneBodyKin.Ftrunc c n ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2)
      (F := fun p => Submission.BoseGases.fsKinCoeff c ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2)
      (fun n => ?_) ?_ ?_ ?_
    · refine Integrable.mono' hg
        (aestronglyMeasurable_symAIntegrand hpc (Work.OneBodyKin.measurable_Ftrunc c n) a q) ?_
      filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n _) (sq_nonneg (profHatCube M p)))]
      exact symAIntegrand_le ha (fun r hr => Ftrunc_le_sq_add c hc n r hr) q p
    · refine Integrable.mono' hg
        (aestronglyMeasurable_symAIntegrand hpc (by
          have hcont : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
            rw [show Submission.BoseGases.fsKinCoeff c
                = fun r : ℝ => (max (r - c) 0) ^ 2 from rfl]
            exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
          exact hcont.measurable) a q) ?_
      filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c _) (sq_nonneg (profHatCube M p)))]
      exact symAIntegrand_le ha (fun r hr => fsKinCoeff_le_sq_add c r hc hr) q p
    · filter_upwards with p
      intro n m hnm
      exact mul_le_mul_of_nonneg_right
        (Work.OneBodyKin.Ftrunc_mono_le c hnm ‖q + a⁻¹ • p‖) (sq_nonneg _)
    · filter_upwards with p
      exact (Work.OneBodyKin.Ftrunc_tendsto c ‖q + a⁻¹ • p‖).mul_const _
  have hthis := hmain.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  simpa only [symACube] using hthis

/-- **The `q`-integral of the cube symbol converges along the radial truncations**, with the two
moment integrabilities as inputs. -/
theorem cubeSymbolIntegralTendsto_of_moments (M : ℕ) (hM : 1 ≤ M) {a c : ℝ} (ha : 0 < a)
    (hc : 0 ≤ c)
    (hI0 : MeasureTheory.Integrable (fun p : E3 => (profHatCube M p) ^ 2))
    (hI1 : MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * (profHatCube M p) ^ 2))
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ => ∫ q : E3,
        symACube M a (Work.OneBodyKin.Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (∫ q : E3,
        symACube M a (Submission.BoseGases.fsKinCoeff c) q *
          ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2)) := by
  have hpc : Continuous (fun p : E3 => profHatCube M p) := profHatCube_continuous M hM
  obtain ⟨A, B, hAnn, hBnn, hquad⟩ := cubeSymA_quad_bound (c := c) hM ha hI0 hI1
  obtain ⟨D, hD0, hdec⟩ := Work.OneBodyKin.kinFT_decay_le 6
    (Complex.ofRealCLM.contDiff.comp hψ) (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0))
  have hone : MeasureTheory.Integrable (fun q : E3 => (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) := by
    refine integrable_one_add_norm (E := E3) (μ := volume) (r := ((10 : ℕ) : ℝ)) ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hGint : MeasureTheory.Integrable
      (fun q : E3 => (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) :=
    hone.const_mul ((A + B) * D ^ 2)
  have hK : Continuous (fun q : E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q) :=
    Work.OneBodyKin.continuous_kinFT
      ((Complex.continuous_ofReal.comp hψ.continuous).integrable_of_hasCompactSupport
        (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)))
  have hbound : ∀ n : ℕ, ∀ᵐ q ∂(volume : Measure E3),
      ‖symACube M a (Work.OneBodyKin.Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2‖
        ≤ (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ)) := by
    intro n
    refine Filter.Eventually.of_forall (fun q => ?_)
    have h0 : (0 : ℝ) < 1 + ‖q‖ := by positivity
    have hq := hquad (Work.OneBodyKin.Ftrunc c n) (Work.OneBodyKin.measurable_Ftrunc c n)
      (Work.OneBodyKin.Ftrunc_nonneg c n) (fun r hr => Ftrunc_le_sq_add c hc n r hr) q
    have hdec6 : ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2
        ≤ D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
      calc ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2
          ≤ (D / (1 + ‖q‖) ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdec q) 2
        _ = D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
            rw [div_pow, div_eq_mul_inv, show ((1 + ‖q‖) ^ 6) ^ 2 = (1 + ‖q‖) ^ 12 by ring,
              Real.rpow_neg h0.le, Real.rpow_natCast]
    have hAB : A * ‖q‖ ^ 2 + B ≤ (A + B) * (1 + ‖q‖) ^ 2 := by
      have h1 : ‖q‖ ^ 2 ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have h2 : (1 : ℝ) ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have h3 : A * ‖q‖ ^ 2 ≤ A * (1 + ‖q‖) ^ 2 := mul_le_mul_of_nonneg_left h1 hAnn
      have h4 : B * 1 ≤ B * (1 + ‖q‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hBnn
      linarith
    have hrw : (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))
        = (1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
      rw [show (-((10 : ℕ) : ℝ)) = (2 : ℝ) + (-((12 : ℕ) : ℝ)) by norm_num, Real.rpow_add h0]
      norm_num
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖), hrw]
    calc |symACube M a (Work.OneBodyKin.Ftrunc c n) q|
          * ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2
        ≤ ((A + B) * (1 + ‖q‖) ^ 2) * (D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) :=
          mul_le_mul (le_trans hq hAB) hdec6 (sq_nonneg _) (by positivity)
      _ = (A + B) * D ^ 2 * ((1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) := by ring
  have hlim : ∀ᵐ q ∂(volume : Measure E3),
      Filter.Tendsto
        (fun n : ℕ => symACube M a (Work.OneBodyKin.Ftrunc c n) q
          * ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2)
        Filter.atTop
        (nhds (symACube M a (Submission.BoseGases.fsKinCoeff c) q
          * ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2)) :=
    Filter.Eventually.of_forall (fun q =>
      (cubeSymA_Ftrunc_pt hM ha hc hI0 hI1 q).mul_const _)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun q : E3 => symACube M a (Work.OneBodyKin.Ftrunc c n) q
        * ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2) := by
    intro n
    have hjoint : StronglyMeasurable (fun w : E3 × E3 =>
        Work.OneBodyKin.Ftrunc c n ‖w.1 + a⁻¹ • w.2‖ * (profHatCube M w.2) ^ 2) :=
      (((Work.OneBodyKin.measurable_Ftrunc c n).comp
        ((continuous_fst.add (continuous_snd.const_smul a⁻¹)).norm.measurable)).stronglyMeasurable).mul
        ((hpc.comp continuous_snd).pow 2).stronglyMeasurable
    have hint : StronglyMeasurable (fun q : E3 =>
        ∫ p : E3, Work.OneBodyKin.Ftrunc c n ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2) :=
      hjoint.integral_prod_right' (ν := (volume : Measure E3))
    have hsym : StronglyMeasurable (fun q : E3 => symACube M a (Work.OneBodyKin.Ftrunc c n) q) := by
      simpa only [symACube] using hint.const_mul (((2 * Real.pi) ^ 3)⁻¹)
    exact hsym.aestronglyMeasurable.mul ((hK.norm.pow 2).aestronglyMeasurable)
  exact MeasureTheory.tendsto_integral_of_dominated_convergence _
    hmeas hGint hbound hlim


end Helpers

theorem cruxUnprojCube (M : ℕ) (hM : 1 ≤ M) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Work.BoseFixB1S.bsFamilyFormUnprojCube M a (Submission.BoseGases.fsKinCoeff c) ψ
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixB1S.symACube M a (Submission.BoseGases.fsKinCoeff c) q *
              ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  -- the left-hand side converges along the radial truncations of the kinetic symbol
  have hL := Work.BoseFixB1S.cubeFamFormFtruncTendsto2 M hM (a := a) (c := c) ha hψ hcs
  -- and so does the right-hand side (dominated convergence in the momentum)
  have hR := Work.BoseFixB1S.cubeSymbolIntegralTendsto_of_moments M hM ha hc
    (Work.BoseFixB1S.cubeProfHatMass M hM) (Work.BoseFixB1S.cubeProfHatSecondMoment M hM) hψ hcs
  -- at every truncation the two sides agree, by the `L¹` symbol identity
  have hkey : ∀ n : ℕ,
      Work.BoseFixB1S.bsFamilyFormUnprojCube M a (Work.OneBodyKin.Ftrunc c n) ψ
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixB1S.symACube M a (Work.OneBodyKin.Ftrunc c n) q *
              ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 :=
    fun n => cuc_cubeFamFormEqSymbol M hM ha
      (Work.OneBodyKin.integrable_Ftrunc c n) (Work.OneBodyKin.Ftrunc_nonneg c n) hψ hcs
  have hL' := hL.congr' (Filter.Eventually.of_forall hkey)
  have hR' := hR.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  exact le_of_eq (tendsto_nhds_unique hL' hR')

end Work.BoseFixB1S

