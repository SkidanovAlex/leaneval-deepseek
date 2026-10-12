import Mathlib
import Submission.Work.BoseFixB1S.cubeProfHatMass
import Submission.Work.BoseFixB1S.cubeProfHatSecondMoment
import Submission.Work.BoseFixB1S.familyFormUnprojCube_eq_kernelForm
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
import Submission.Work.OneBodyKin.Phi_far_nonneg
import Submission.Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le
import Submission.Work.OneBodyKin.SecondOrder.symA_zero_small
import Submission.Work.OneBodyKin.SecondOrder.symD_diff_bound_uniform
import Submission.Work.OneBodyKin.SecondOrder.symD_fsKinCoeff_small
import Submission.Work.OneBodyKin.SymBound_iff_SymBoundOne
import Submission.Work.OneBodyKin.SymbolIntegral_fsKinCoeff
import Submission.Work.OneBodyKin.dSpace_eq_fourier
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.symA_fsKinCoeff_far_le
import Submission.Work.OneBodyKin.symD_second_order
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.cubeFamFormFtruncTendsto2` — the cube family form converges along the
radial truncations of the FS cut-off

Along the radial truncations `Ftrunc c n ↑ fsKinCoeff c` of the FS cut-off symbol
(`Work.OneBodyKin.TruncDefs`), the `u`-integral of the *unprojected cube* family form converges:

    `bsFamilyFormUnprojCube M a (Ftrunc c n) ψ ⟶ bsFamilyFormUnprojCube M a (fsKinCoeff c) ψ`.

This is the cube-cutoff analogue of the proved
`Work.BoseFixB1S.Unproj.bsFamilyFormUnproj_Ftrunc_tendsto` (the ball-window version).  The
window `χ_M` of FS's cube cutoff is only `C^{M−1}`, so the ball argument — which bounds the
`u`-integrand *uniformly in* `u` by `bsW_le_L2_Dir` + `bsL2`/`bsDir` bounds, both requiring a
`C^∞` state — is not available here.  Instead the argument runs entirely at the level of
*integrals over the box centre*:

* **pointwise (in `n`) monotone convergence in the momentum `p`**: for the truncated symbols the
  `p`-integrand is dominated by `Ftrunc c n ‖p‖ ≤ [n−c]₊²` times the `L²` mass of the `p`-transform,
  so `ofReal (bsOneBodyUnprojCube M a (Ftrunc c n) u ψ) = (2π)⁻³ ∫⁻_p ofReal (Ftrunc c n ‖p‖·‖…)`;
* **the bound `sup_n ∫_u bsOneBodyUnprojCube M a (Ftrunc c n) u ψ < ∞`**: the `L¹`-symbol identity
  (`ccf_cubeFamFormEqSymbol`, reproduced below verbatim from
  `Submission/Work/BoseFixB1S/cruxUnprojCube.lean`, where it is proved) converts each member of the
  sequence into a `q`-integral of the cube symbol `symACube M a (Ftrunc c n)`, and the
  `q`-uniform quadratic bound on that symbol (`symACube_quad_bound_cube` below, whose constants are
  the two PROVED moment integrals `cubeProfHatMass` / `cubeProfHatSecondMoment`) together with the
  Schwartz decay of `kinFT ψ` bounds *all* of them by one finite number;
* the two facts together give, by monotone convergence in the box centre `u`, that the limit
  function `u ↦ bsOneBodyUnprojCube M a (fsKinCoeff c) u ψ` is finite a.e., integrable, and is the
  limit of the sequence; a final monotone convergence in `u` gives the statement.

The declarations between the two `##` markers below are the verbatim (renamed) content of
`Submission/Work/BoseFixB1S/cubeFamFormEqSymbol.lean` — the `L¹`-symbol identity and its ingredients
— reproduced here because that module imports `cruxUnprojCube.lean`, which cannot be built (it
references the lemma proved here).  They are used *only* through `ccf_cubeFamFormEqSymbol`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal Convolution

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## The `p`-convention Fourier transform of the cube cutoff is the cosine profile -/

/-- **The Fourier transform of the cube bump equals its real cosine profile** (cube analogue of
the proved `Work.OneBodyKin.kinFT_chi_eq`): since `chiSmall M` is even, the sine part of
`kinFT (chiSmall M : E3 → ℂ)` vanishes, leaving `profHatCube M`. -/
theorem cubeKinFT_chiSmall (M : ℕ) (hM : 1 ≤ M) (p : E3) :
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
(proved there), inlined here because that module imports this one for `cubeKinFT_chiSmall`.
-/



set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## 1. The cube overlap kernel: continuity, compact support, integrability -/

/-- `convScaleCube M a` is `(fun z ↦ conv3Small M (a⁻¹ • z))`, definitionally. -/
private lemma ccf_convScaleCube_eq_conv3Small_fun (M : ℕ) (a : ℝ) :
    convScaleCube M a = fun z : E3 => Submission.BoseGases.conv3Small M (a⁻¹ • z) := by
  funext z
  rfl

/-- `convScaleCube M a` is continuous (`1 ≤ M`). -/
theorem ccf_continuous_convScaleCube (M : ℕ) (hM : 1 ≤ M) (a : ℝ) :
    Continuous (convScaleCube M a) := by
  rw [ccf_convScaleCube_eq_conv3Small_fun M a]
  exact (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)

/-- `conv3Small M` has compact support (`1 ≤ M`), being the convolution `χ_M ⋆ χ_M`. -/
private lemma ccf_hasCompactSupport_conv3Small (M : ℕ) (hM : 1 ≤ M) :
    HasCompactSupport (fun x : E3 => Submission.BoseGases.conv3Small M x) := by
  rw [Submission.BoseGases.conv3Small_eq_convolution M]
  exact (Submission.BoseGases.chiSmall_hasCompactSupport hM).convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) (Submission.BoseGases.chiSmall_hasCompactSupport hM)

/-- `convScaleCube M a` has compact support for `a ≠ 0`: it is the dilation of `conv3Small M`. -/
theorem ccf_hasCompactSupport_convScaleCube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : a ≠ 0) :
    HasCompactSupport (convScaleCube M a) := by
  rw [ccf_convScaleCube_eq_conv3Small_fun M a]
  have h := (ccf_hasCompactSupport_conv3Small M hM).comp_homeomorph
    (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha))
  simpa [Homeomorph.smulOfNeZero, Function.comp_def] using h

/-- **The cube overlap kernel is `L¹`**: continuous with compact support. -/
theorem ccf_integrable_convScaleCube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : a ≠ 0) :
    MeasureTheory.Integrable (convScaleCube M a) :=
  (ccf_continuous_convScaleCube M hM a).integrable_of_hasCompactSupport
    (ccf_hasCompactSupport_convScaleCube M hM ha)

/-- The convolution kernel `convScaleCube M a · kinKernel F` of the unprojected family form is
integrable: `convScaleCube M a ∈ L¹` and `kinKernel F` is bounded (`kinKernel_bdd`). -/
theorem ccf_integrable_convScaleCube_mul_kinKernel (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : a ≠ 0)
    {F : ℝ → ℝ} (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) :
    MeasureTheory.Integrable
      (fun z : E3 => convScaleCube M a z * Submission.BoseGases.kinKernel F z) := by
  refine (ccf_integrable_convScaleCube M hM ha).mul_bdd
    (c := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖)
    ((Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable hFi).aestronglyMeasurable) ?_
  filter_upwards with z
  exact Work.SmallBoxBridge.Resolve.kinKernel_bdd F hFi z

/-! ## 2. Evenness of the cube profile, and the change of variables in `symACube` -/

/-- `profHatCube M` is even (it is the cosine transform of `chiSmall M`). -/
private lemma ccf_profHatCube_even (M : ℕ) (p : E3) : profHatCube M (-p) = profHatCube M p := by
  unfold profHatCube
  apply integral_congr_ae
  filter_upwards with z
  rw [inner_neg_left, Real.cos_neg]

/-- The symbol `symACube M a F q = (2π)⁻³∫_p F‖q + a⁻¹•p‖ profHatCube(p)²` with the `F`-factor
carrying the momentum: the dilation `v = a • x` (`v`-volume factor `a³`), the translation
`x = p − q` and the evenness of `profHatCube` give

  `symACube M a F q = (2π)⁻³ · a³ ∫_p F‖p‖ · profHatCube(a • (q − p))²`. -/
theorem ccf_symACube_eq_shiftedIntegral (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ)
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
    rw [h1, ccf_profHatCube_even]
  unfold symACube
  rw [hdil, htr, heven]

/-! ## 3. The Fourier transform of the cube overlap kernel -/

/-- The two-phase product formula around a shift:
`e^{i⟪p,z⟫}·e^{-i⟪q,z⟫} = e^{-i⟪q−p,z⟫}`. -/
private lemma ccf_exp_inner_mul_exp_inner_neg (p q z : E3) :
    Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ (q - p) z : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_sub_left]
  push_cast
  ring

/-- **The convolution theorem at the cube bump**: `kinFT (χ_M ⋆ χ_M) = profHatCube M²`.  Cube
analogue of the proved `Work.OneBodyKin.kinFT_conv3_chi`; the sine part of `kinFT χ_M` vanishes by
evenness (`cubeKinFT_chiSmall`). -/
theorem ccf_kinFT_conv3Small_eq_profHatCube_sq (M : ℕ) (hM : 1 ≤ M) (p : E3) :
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
  rw [← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, cubeKinFT_chiSmall M hM]
  ring

/-- **The Fourier transform of the scaled cube autocorrelation.**  With
`convScaleCube M a z = (χ_M ⋆ χ_M)(z/a)` and the `p`-convention Fourier transform `kinFT`, the
substitution `z = a•w` gives

    `∫_z (χ_M⋆χ_M)(z/a)·e^{−i⟪q,z⟫} dz = a³ · kinFT (χ_M⋆χ_M) (a q)`.

Cube analogue of the proved `Work.OneBodyKin.fourier_convScale_scaling`. -/
private lemma ccf_fourier_convScaleCube_scaling (M : ℕ) {a : ℝ} (ha : 0 < a) (q : E3) :
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
theorem ccf_fourier_convScaleCube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (q : E3) :
    (∫ z : E3, (convScaleCube M a z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = (a : ℂ) ^ 3 * ((profHatCube M (a • q) : ℝ) : ℂ) ^ 2 := by
  rw [ccf_fourier_convScaleCube_scaling M ha q, ccf_kinFT_conv3Small_eq_profHatCube_sq M hM (a • q)]

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
theorem ccf_ftKernel_eq_smul_integral_of_fourier
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
      rw [ccf_exp_inner_mul_exp_inner_neg p q z]
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
`ccf_ftKernel_eq_smul_integral_of_fourier` and `ccf_fourier_convScaleCube` give

  `∫_z k z·e^{-i⟪q,z⟫}dz = (2π)⁻³ a³ ∫_p F‖p‖ profHatCube(a•(q−p))² dp`. -/
theorem ccf_ftKernelConvScaleCube_eq_symACube (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) (q : E3) :
    (∫ z : E3, (convScaleCube M a z : ℂ) * (Submission.BoseGases.kinKernel F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ((((2 * Real.pi) ^ 3)⁻¹ *
          (a ^ 3 * ∫ p : E3, F ‖p‖ * (profHatCube M (a • (q - p))) ^ 2) : ℝ) : ℂ) := by
  refine ccf_ftKernel_eq_smul_integral_of_fourier (κ := convScaleCube M a)
    (ccf_integrable_convScaleCube M hM (ne_of_gt ha)) (s := a ^ 3)
    (G := fun r : E3 => (profHatCube M (a • r)) ^ 2) ?_ hFi q
  intro r
  rw [ccf_fourier_convScaleCube M hM ha r]
  push_cast
  ring

/-- **The Fourier transform of the kernel of the unprojected cube family form.**  The real part of
`∫_z convScaleCube M a z · kinKernel F z · e^{-i⟪q,z⟫}dz` is the symbol `symACube M a F q`. -/
theorem ccf_kinKernel_mul_convScaleCube_fourier_re (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a)
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
  rw [h1, ccf_ftKernelConvScaleCube_eq_symACube M hM ha hFi q, Complex.ofReal_re,
    ccf_symACube_eq_shiftedIntegral M hM ha F q]

/-! ## 6. The main theorem -/

theorem ccf_cubeFamFormEqSymbol (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
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
    (ccf_integrable_convScaleCube_mul_kinKernel M hM (ne_of_gt ha) hF) hψ hcs]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  rw [ccf_kinKernel_mul_convScaleCube_fourier_re M hM ha hF q]

/-! ## The `q`-uniform quadratic bound for the cube symbol

The whole sequence `(symACube M a (Ftrunc c n))_n` is dominated by the single quadratic
`A‖q‖² + B`, with `A, B` built from the two PROVED moment integrals of `profHatCube M`
(`cubeProfHatMass`, `cubeProfHatSecondMoment`) — the point being that the *unbounded* factor
`Ftrunc c n‖p‖ ≤ 2‖p‖² + 2c²` is uniform in `n`. -/

/-- The one-dimensional `p`-bound `‖q + a⁻¹•p‖² ≤ 2‖q‖² + 2a⁻²‖p‖²`. -/
private lemma cubeNorm_add_inv_smul_sq_le {a : ℝ} (ha : 0 < a) (q p : E3) :
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

/-- **The `q`-uniform quadratic bound for the cube symbol at the FS cut-off.**  For every `a > 0`
there are `A, B ≥ 0` such that *every* nonnegative symbol `G` with `G r ≤ 2r² + 2c²` (`r ≥ 0`)
satisfies `symACube M a G q ≤ A‖q‖² + B` for all `q`.  In particular this covers
`G = Ftrunc c n` for every `n` (`Ftrunc_le_fsKinCoeff` + `fsKinCoeff_le_two_mul`) and
`G = fsKinCoeff c`. -/
theorem symACube_quad_bound_cube (M : ℕ) (hM : 1 ≤ M) {a c : ℝ} (ha : 0 < a) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (G : ℝ → ℝ), (∀ r : ℝ, 0 ≤ r → 0 ≤ G r) →
        (∀ r : ℝ, 0 ≤ r → G r ≤ 2 * r ^ 2 + 2 * c ^ 2) → ∀ q : E3,
        symACube M a G q ≤ A * ‖q‖ ^ 2 + B := by
  have hI0 := cubeProfHatMass M hM
  have hI1 := cubeProfHatSecondMoment M hM
  have hI0nn : 0 ≤ ∫ p : E3, (profHatCube M p) ^ 2 :=
    integral_nonneg (fun p => sq_nonneg _)
  have hI1nn : 0 ≤ ∫ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2 :=
    integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hcπ : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  set I0 : ℝ := ∫ p : E3, (profHatCube M p) ^ 2 with hI0def
  set I1 : ℝ := ∫ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2 with hI1def
  have hI0nn' : 0 ≤ I0 := by rw [hI0def]; exact hI0nn
  have hI1nn' : 0 ≤ I1 := by rw [hI1def]; exact hI1nn
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (4 * I0),
    ((2 * Real.pi) ^ 3)⁻¹ * (4 * (a ^ 2)⁻¹ * I1 + 2 * c ^ 2 * I0), ?_, ?_, ?_⟩
  · exact mul_nonneg hcπ.le (by positivity)
  · exact mul_nonneg hcπ.le (by positivity)
  · intro G hGnn hG q
    have hdom1 : Integrable (fun p : E3 =>
        (4 * ‖q‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2) :=
      hI0.const_mul _
    have hdom2 : Integrable (fun p : E3 =>
        (4 * (a ^ 2)⁻¹) * (‖p‖ ^ 2 * (profHatCube M p) ^ 2)) :=
      hI1.const_mul _
    have hdom : Integrable (fun p : E3 =>
        (4 * ‖q‖ ^ 2 + 4 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2) := by
      refine (hdom1.add hdom2).congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Pi.add_apply]
      ring
    have hpoint : ∀ p : E3, G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2
        ≤ (4 * ‖q‖ ^ 2 + 4 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2 := by
      intro p
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := hG ‖q + a⁻¹ • p‖ (norm_nonneg _)
      have h2 := cubeNorm_add_inv_smul_sq_le ha q p
      linarith
    have hnn : ∀ p : E3, 0 ≤ G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2 :=
      fun p => mul_nonneg (hGnn _ (norm_nonneg _)) (sq_nonneg _)
    have hmono : (∫ p : E3, G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2)
        ≤ ∫ p : E3,
            (4 * ‖q‖ ^ 2 + 4 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2 :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hdom
        (Filter.Eventually.of_forall hpoint)
    have hval : (∫ p : E3,
          (4 * ‖q‖ ^ 2 + 4 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2)
        = 4 * ‖q‖ ^ 2 * I0 + 4 * (a ^ 2)⁻¹ * I1 + 2 * c ^ 2 * I0 := by
      rw [show (fun p : E3 =>
            (4 * ‖q‖ ^ 2 + 4 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2)
          = fun p : E3 => (4 * ‖q‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2
            + (4 * (a ^ 2)⁻¹) * (‖p‖ ^ 2 * (profHatCube M p) ^ 2) from by
        funext p; ring]
      rw [integral_add hdom1 hdom2, integral_const_mul, integral_const_mul, ← hI0def, ← hI1def]
      ring
    have hsym : symACube M a G q = ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2 := rfl
    rw [hsym]
    calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, G ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
            (4 * ‖q‖ ^ 2 + 4 * (a ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2) * (profHatCube M p) ^ 2 :=
          mul_le_mul_of_nonneg_left hmono (le_of_lt hcπ)
      _ = ((2 * Real.pi) ^ 3)⁻¹
            * (4 * ‖q‖ ^ 2 * I0 + 4 * (a ^ 2)⁻¹ * I1 + 2 * c ^ 2 * I0) := by rw [hval]
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (4 * I0) * ‖q‖ ^ 2
          + ((2 * Real.pi) ^ 3)⁻¹ * (4 * (a ^ 2)⁻¹ * I1 + 2 * c ^ 2 * I0) := by ring

/-! ## The windowed state and the box-centre machinery -/

private lemma continuous_cubeWin (M : ℕ) (hM : 1 ≤ M) (a : ℝ) (u : E3) :
    Continuous (cubeWin M a u) :=
  (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)

private lemma cubeWin_ne_zero_le_norm {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {u x : E3}
    (h : cubeWin M a u x ≠ 0) : ‖x - a • u‖ ≤ a := by
  have h' : Submission.BoseGases.chiSmall M (a⁻¹ • x - u) ≠ 0 := h
  have h1 : ‖a⁻¹ • x - u‖ ≤ 1 := Work.BoseFixB1S.win.chiSmall_support_norm_le hM h'
  have hsm : x - a • u = a • (a⁻¹ • x - u) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
  rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  calc a * ‖a⁻¹ • x - u‖ ≤ a * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
    _ = a := by ring

private lemma cubeWin_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (u : E3) :
    HasCompactSupport (cubeWin M a u) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (a • u) a) ?_
  rw [Function.support_subset_iff]
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact cubeWin_ne_zero_le_norm hM ha hx

private lemma integrable_cubeWin_mul {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (u : E3)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun x : E3 => cubeWin M a u x * ψ x) :=
  ((continuous_cubeWin M hM a u).mul hψ.continuous).integrable_of_hasCompactSupport
    ((cubeWin_hasCompactSupport hM ha u).mul_right)

/-- `∫_z cubeWin M a u z ^ 2 dz = a ^ 3` (the `z`-integral of the square of the moving window). -/
private lemma integral_cubeWin_sq (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (u : E3) :
    ∫ z : E3, cubeWin M a u z ^ 2 = a ^ 3 := by
  have h1 : (∫ z : E3, cubeWin M a u z ^ 2)
      = a ^ 3 * ∫ s : E3, Submission.BoseGases.chiSmall M (s - u) ^ 2 := by
    rw [integral_comp_smul_right (g := fun z : E3 => cubeWin M a u z ^ 2) ha]
    congr 1
    apply integral_congr_ae
    filter_upwards with s
    show Submission.BoseGases.chiSmall M (a⁻¹ • (a • s) - u) ^ 2
      = Submission.BoseGases.chiSmall M (s - u) ^ 2
    rw [show a⁻¹ • (a • s) = s by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]]
  have h2 : (∫ s : E3, Submission.BoseGases.chiSmall M (s - u) ^ 2)
      = ∫ w : E3, Submission.BoseGases.chiSmall M w ^ 2 := by
    have h := integral_comp_sub_left
      (g := fun s : E3 => Submission.BoseGases.chiSmall M (s - u) ^ 2) u
    rw [← h]
    apply integral_congr_ae
    filter_upwards with w
    rw [show u - w - u = -w by abel, Submission.BoseGases.chiSmall_even hM]
  rw [h1, h2, Submission.BoseGases.chiSmall_L2 hM, mul_one]

/-- The windowed state vanishes once the box centre is far out. -/
private lemma cubeWin_far {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a)
    {ψ : E3 → ℝ} (hcs : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u : E3, R ≤ ‖u‖ →
      (fun z : E3 => cubeWin M a u z * ψ z) = 0 := by
  obtain ⟨Rψ, hRψ0, hψzero⟩ :=
    Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs
  refine ⟨(Rψ + a) / a, div_nonneg (by linarith) (le_of_lt ha), ?_⟩
  intro u hu
  funext z
  change cubeWin M a u z * ψ z = 0
  by_contra hne
  have hwin : cubeWin M a u z ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hpsi : ψ z ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hz : ‖z‖ < Rψ := not_le.mp fun h => hpsi (hψzero z h)
  have h1 : ‖z - a • u‖ ≤ a := cubeWin_ne_zero_le_norm hM ha hwin
  have h2 : ‖a • u‖ ≤ ‖z‖ + ‖z - a • u‖ := by
    have h := norm_sub_le z (z - a • u)
    rwa [sub_sub_cancel] at h
  have h4 : ‖a • u‖ = a * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have h3 : a * ‖u‖ < Rψ + a := by
    rw [← h4]
    linarith
  have h5 : ‖u‖ < (Rψ + a) / a := by
    rw [lt_div_iff₀ ha]
    linarith [h3, mul_comm a ‖u‖]
  exact absurd hu (not_le.mpr h5)

private lemma bsW_zero' (F : ℝ → ℝ) : Work.BSKinetic.Decomp.bsW F (0 : E3 → ℝ) = 0 := by
  simp [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]

/-- **Strong measurability in the box centre `u` of the cube-windowed `bsW`.** -/
theorem strongMeasurable_bsW_cubeWin {M : ℕ} (hM : 1 ≤ M) (a : ℝ) {G : ℝ → ℝ}
    (hG : Measurable G) {ψ : E3 → ℝ} (hψ : Continuous ψ) :
    StronglyMeasurable (fun u : E3 => Work.BSKinetic.Decomp.bsW G
      (fun z : E3 => cubeWin M a u z * ψ z)) := by
  have hexp : StronglyMeasurable (fun q : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ)))) :=
    (by fun_prop : Continuous (fun q : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ))))).stronglyMeasurable
  have hwin : StronglyMeasurable (fun q : (E3 × E3) × E3 =>
      (Submission.BoseGases.chiSmall M (a⁻¹ • q.2 - q.1.1) : ℂ)) := by
    refine (Complex.continuous_ofReal.comp ?_).stronglyMeasurable
    exact (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
  have hpsi : StronglyMeasurable (fun q : (E3 × E3) × E3 => (ψ q.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp hψ).stronglyMeasurable.comp_measurable (by fun_prop)
  have hf : StronglyMeasurable (fun q : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiSmall M (a⁻¹ • q.2 - q.1.1) : ℂ) * (ψ q.2 : ℂ))) :=
    hexp.mul (hwin.mul hpsi)
  have hK : StronglyMeasurable (fun q : E3 × E3 =>
      ∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ q.2 y : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiSmall M (a⁻¹ • y - q.1) : ℂ) * (ψ y : ℂ))) :=
    hf.integral_prod_right' (ν := (volume : Measure E3))
  have hGp : StronglyMeasurable (fun q : E3 × E3 => G ‖q.2‖ *
      ‖(∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ q.2 y : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiSmall M (a⁻¹ • y - q.1) : ℂ) * (ψ y : ℂ)))‖ ^ 2) := by
    have hGm : StronglyMeasurable (fun q : E3 × E3 => G ‖q.2‖) :=
      (hG.comp continuous_norm.measurable).stronglyMeasurable.comp_measurable (by fun_prop)
    exact hGm.mul (hK.norm.pow 2)
  have hF : StronglyMeasurable (fun u : E3 =>
      ∫ p : E3, G ‖p‖ *
        ‖(∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) *
          ((Submission.BoseGases.chiSmall M (a⁻¹ • y - u) : ℂ) * (ψ y : ℂ)))‖ ^ 2) :=
    hGp.integral_prod_right' (ν := (volume : Measure E3))
  have hfun : (fun u : E3 => ∫ p : E3, G ‖p‖ *
        ‖(∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) *
          ((Submission.BoseGases.chiSmall M (a⁻¹ • y - u) : ℂ) * (ψ y : ℂ)))‖ ^ 2)
      = fun u : E3 => Work.BSKinetic.Decomp.bsW G
          (fun z : E3 => cubeWin M a u z * ψ z) := by
    funext u
    unfold Work.BSKinetic.Decomp.bsW Work.BSKinetic.Decomp.bsPsi Submission.BoseGases.kinFT
    congr 1
    funext p
    congr 1
    congr 1
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [Complex.ofReal_mul]
    rfl
  rw [hfun] at hF
  exact hF

private lemma memLp_one_of_continuous_cspt {f : E3 → ℂ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : MeasureTheory.MemLp f 1 volume :=
  MeasureTheory.memLp_one_iff_integrable.mpr (hf.integrable_of_hasCompactSupport hcs)

private lemma memLp_two_of_continuous_cspt {f : E3 → ℂ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : MeasureTheory.MemLp f 2 volume := by
  have hsup : HasCompactSupport (fun z : E3 => ‖f z‖ ^ 2) :=
    hcs.mono (by
      intro z hz
      simp only [Function.mem_support] at hz ⊢
      exact fun h => hz (by rw [h, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]))
  have hint : MeasureTheory.Integrable (fun z : E3 => ‖f z‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hsup
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hint

/-- Plancherel for the windowed state: `(2π)⁻³ ∫_p ‖bsPsi (χ_u ψ) p‖² = bsL2 (χ_u ψ)`. -/
private lemma plancherel_cubeWin_mul (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (u : E3)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun p : E3 => ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)
      ∧ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)
        = Work.BSKinetic.Decomp.bsL2 (fun z : E3 => cubeWin M a u z * ψ z) := by
  have hg : Continuous (fun z : E3 => cubeWin M a u z * ψ z) :=
    (continuous_cubeWin M hM a u).mul hψ.continuous
  have hgc : HasCompactSupport (fun z : E3 => cubeWin M a u z * ψ z) :=
    (cubeWin_hasCompactSupport hM ha u).mul_right
  have hF : Continuous (fun z : E3 => ((cubeWin M a u z * ψ z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hg
  have hFc : HasCompactSupport (fun z : E3 => ((cubeWin M a u z * ψ z : ℝ) : ℂ)) := by
    have h := hgc.comp_left (g := (Complex.ofRealCLM : ℝ → ℂ)) (by simp)
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  have hpl := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
    (memLp_one_of_continuous_cspt hF hFc) (memLp_two_of_continuous_cspt hF hFc)
  have hR : (∫ z : E3, ‖((cubeWin M a u z * ψ z : ℝ) : ℂ)‖ ^ 2)
      = ∫ z : E3, (cubeWin M a u z * ψ z) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  refine ⟨hpl.1, ?_⟩
  rw [Work.BSKinetic.Decomp.bsL2, ← hR]
  exact hpl.2

/-- The family form as a `bsW`-integral in the box centre. -/
private lemma cubeFamFormUnprojCube_eq_bsW_integral (M : ℕ) (a : ℝ) (F : ℝ → ℝ)
    {ψ : E3 → ℝ} :
    bsFamilyFormUnprojCube M a F ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ u : E3, Work.BSKinetic.Decomp.bsW F
          (fun z : E3 => cubeWin M a u z * ψ z) := by
  rw [bsFamilyFormUnprojCube]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext u
  exact (twoPi_inv_bsW_cubeWin_eq_bsOneBodyUnprojCube M a F u ψ).symm

/-- **The symbol identity for the `bsW`-integral in the box centre** (from
`ccf_cubeFamFormEqSymbol`). -/
private lemma cubeWin_bsW_integral_eq_symbol (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : MeasureTheory.Integrable (fun p : E3 => F ‖p‖))
    (hFnn : ∀ r : ℝ, 0 ≤ F r)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ u : E3, Work.BSKinetic.Decomp.bsW F (fun z : E3 => cubeWin M a u z * ψ z))
      = ∫ q : E3, symACube M a F q *
          ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2 := by
  have hpos : ((2 * Real.pi) ^ 3)⁻¹ ≠ 0 := by positivity
  have h1 := cubeFamFormUnprojCube_eq_bsW_integral M a F (ψ := ψ)
  have h2 := ccf_cubeFamFormEqSymbol M hM ha hF hFnn hψ hcs
  exact mul_left_cancel₀ hpos (h1.symm.trans h2)

/-- **The target.** -/
theorem cubeFamFormFtruncTendsto2 (M : ℕ) (hM : 1 ≤ M) {a c : ℝ} (ha : 0 < a)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ =>
        Work.BoseFixB1S.bsFamilyFormUnprojCube M a (Work.OneBodyKin.Ftrunc c n) ψ)
      Filter.atTop
      (nhds (Work.BoseFixB1S.bsFamilyFormUnprojCube M a
        (Submission.BoseGases.fsKinCoeff c) ψ)) := by
  classical
  obtain ⟨A, B, hA0, hB0, hAB⟩ := symACube_quad_bound_cube M hM (a := a) (c := c) ha
  -- the q-side dominating function is integrable
  obtain ⟨D, hD0, hDdec⟩ := Work.OneBodyKin.kinFT_decay_le 6
    (Complex.ofRealCLM.contDiff.comp hψ) (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0))
  have hKint : MeasureTheory.Integrable (fun q : E3 => (A * ‖q‖ ^ 2 + B) *
      ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2) := by
    have hone : MeasureTheory.Integrable (fun q : E3 => (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) := by
      refine integrable_one_add_norm (E := E3) (μ := volume) (r := ((10 : ℕ) : ℝ)) ?_
      rw [finrank_euclideanSpace_fin]
      norm_num
    have hGint : MeasureTheory.Integrable (fun q : E3 => (A + B) * D ^ 2 *
        (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) := hone.const_mul _
    have hcontK : Continuous (fun q : E3 =>
        ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2) :=
      ((Work.OneBodyKin.continuous_kinFT
        ((Complex.continuous_ofReal.comp hψ.continuous).integrable_of_hasCompactSupport
          (hcs.comp_left (g := (Complex.ofRealCLM : ℝ → ℂ)) (by simp)))).norm).pow 2
    have hmeas : AEStronglyMeasurable (fun q : E3 => (A * ‖q‖ ^ 2 + B) *
        ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2) :=
      (((continuous_const.mul (continuous_norm.pow 2)).add continuous_const).mul hcontK
        |>.aestronglyMeasurable)
    refine MeasureTheory.Integrable.mono' hGint hmeas (Filter.Eventually.of_forall fun q => ?_)
    have hq : (0 : ℝ) < 1 + ‖q‖ := by positivity
    have h1 : A * ‖q‖ ^ 2 + B ≤ (A + B) * (1 + ‖q‖) ^ 2 := by
      have hsq : ‖q‖ ^ 2 ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hone2 : (1 : ℝ) ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hA' : A * ‖q‖ ^ 2 ≤ A * (1 + ‖q‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hA0
      have hB' : B ≤ B * (1 + ‖q‖) ^ 2 :=
        le_trans (le_mul_of_one_le_right hB0 hone2) (le_of_eq rfl)
      have hsum : A * (1 + ‖q‖) ^ 2 + B * (1 + ‖q‖) ^ 2 = (A + B) * (1 + ‖q‖) ^ 2 := by ring
      linarith
    have h2 : ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2
        ≤ D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
      calc ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2
          ≤ (D / (1 + ‖q‖) ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hDdec q) 2
        _ = D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
            rw [div_pow, div_eq_mul_inv, show ((1 + ‖q‖) ^ 6) ^ 2 = (1 + ‖q‖) ^ 12 by ring,
              Real.rpow_neg hq.le, Real.rpow_natCast]
    have hrw : (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))
        = (1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
      rw [show (-((10 : ℕ) : ℝ)) = (2 : ℝ) + (-((12 : ℕ) : ℝ)) by norm_num,
        Real.rpow_add hq]
      norm_num
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _)), hrw]
    calc (A * ‖q‖ ^ 2 + B) * ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2
        ≤ ((A + B) * (1 + ‖q‖) ^ 2) * (D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = (A + B) * D ^ 2 * ((1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) := by ring
  -- the boundary radius in the box centre, and the crude uniform bound
  obtain ⟨R, hR0, hRfar⟩ := cubeWin_far (M := M) hM ha hcs
  obtain ⟨Cψ, hCψ⟩ := hcs.exists_bound_of_continuous hψ.continuous
  have hCψ0 : 0 ≤ Cψ := le_trans (norm_nonneg (ψ 0)) (hCψ 0)
  have hCψ' : ∀ z : E3, |ψ z| ≤ Cψ := fun z => by simpa [Real.norm_eq_abs] using hCψ z
  have hBsL2 : ∀ u : E3, Work.BSKinetic.Decomp.bsL2 (fun z : E3 => cubeWin M a u z * ψ z)
      ≤ Cψ ^ 2 * a ^ 3 := by
    intro u
    rw [Work.BSKinetic.Decomp.bsL2]
    have hpt : ∀ z : E3, (cubeWin M a u z * ψ z) ^ 2 ≤ Cψ ^ 2 * cubeWin M a u z ^ 2 := by
      intro z
      have h2 : (ψ z) ^ 2 ≤ Cψ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hCψ' z) 2
      calc (cubeWin M a u z * ψ z) ^ 2 = ψ z ^ 2 * cubeWin M a u z ^ 2 := by ring
        _ ≤ Cψ ^ 2 * cubeWin M a u z ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have hcs2 : HasCompactSupport (fun z : E3 => cubeWin M a u z ^ 2) :=
      (cubeWin_hasCompactSupport hM ha u).mono (by
        intro z hz
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]))
    have hint : MeasureTheory.Integrable (fun z : E3 => Cψ ^ 2 * cubeWin M a u z ^ 2) :=
      (((continuous_cubeWin M hM a u).pow 2).integrable_of_hasCompactSupport hcs2).const_mul _
    calc (∫ z : E3, (cubeWin M a u z * ψ z) ^ 2)
        ≤ ∫ z : E3, Cψ ^ 2 * cubeWin M a u z ^ 2 :=
          MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
            hint (Filter.Eventually.of_forall hpt)
      _ = Cψ ^ 2 * ∫ z : E3, cubeWin M a u z ^ 2 := MeasureTheory.integral_const_mul _ _
      _ = Cψ ^ 2 * a ^ 3 := by rw [integral_cubeWin_sq M hM ha u]
  have key_pint : ∀ (n : ℕ) (u : E3), MeasureTheory.Integrable (fun p : E3 =>
      Work.OneBodyKin.Ftrunc c n ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2) := by
    intro n u
    have hpl := plancherel_cubeWin_mul M hM ha u hψ hcs
    have hcontK : Continuous (fun p : E3 =>
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2) :=
      ((Work.OneBodyKin.continuous_kinFT
        (Complex.ofRealCLM.integrable_comp (integrable_cubeWin_mul hM ha u hψ hcs))).norm).pow 2
    refine MeasureTheory.Integrable.mono'
      (hpl.1.const_mul (Submission.BoseGases.fsKinCoeff c (n : ℝ))) ?_ ?_
    · exact (((Work.OneBodyKin.measurable_Ftrunc c n).comp continuous_norm.measurable).mul
        hcontK.measurable).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_of_nonneg
        (mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (Work.OneBodyKin.Ftrunc_le_max c n ‖p‖) (sq_nonneg _)
  have key_bsW_nonneg : ∀ (n : ℕ) (u : E3), 0 ≤ Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z) := by
    intro n u
    rw [Work.BSKinetic.Decomp.bsW]
    exact MeasureTheory.integral_nonneg fun p =>
      mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n _) (sq_nonneg _)
  have key_bsW_le : ∀ (n : ℕ) (u : E3), Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z)
      ≤ Submission.BoseGases.fsKinCoeff c (n : ℝ) * ((2 * Real.pi) ^ 3 * (Cψ ^ 2 * a ^ 3)) := by
    intro n u
    have hpl := plancherel_cubeWin_mul M hM ha u hψ hcs
    have hpos : ((2 * Real.pi) ^ 3) ≠ 0 := by positivity
    have h2 : (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
          (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)
        = ((2 * Real.pi) ^ 3) * Work.BSKinetic.Decomp.bsL2
            (fun z : E3 => cubeWin M a u z * ψ z) := by
      calc (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)
          = ((2 * Real.pi) ^ 3) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
              ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2) := by
            rw [← mul_assoc, mul_inv_cancel₀ hpos, one_mul]
        _ = ((2 * Real.pi) ^ 3) * Work.BSKinetic.Decomp.bsL2
              (fun z : E3 => cubeWin M a u z * ψ z) := by rw [hpl.2]
    rw [Work.BSKinetic.Decomp.bsW]
    calc (∫ p : E3, Work.OneBodyKin.Ftrunc c n ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)
        ≤ Submission.BoseGases.fsKinCoeff c (n : ℝ) * ∫ p : E3,
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2 := by
          rw [← MeasureTheory.integral_const_mul]
          exact MeasureTheory.integral_mono (key_pint n u) (hpl.1.const_mul _) fun p =>
            mul_le_mul_of_nonneg_right (Work.OneBodyKin.Ftrunc_le_max c n ‖p‖) (sq_nonneg _)
      _ = Submission.BoseGases.fsKinCoeff c (n : ℝ)
            * (((2 * Real.pi) ^ 3) * Work.BSKinetic.Decomp.bsL2
                (fun z : E3 => cubeWin M a u z * ψ z)) := by rw [h2]
      _ ≤ Submission.BoseGases.fsKinCoeff c (n : ℝ) * ((2 * Real.pi) ^ 3 * (Cψ ^ 2 * a ^ 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Submission.BoseGases.fsKinCoeff_nonneg c _)
          exact mul_le_mul_of_nonneg_left (hBsL2 u) (by positivity)
  have key_int : ∀ n : ℕ, MeasureTheory.Integrable (fun u : E3 => Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z)) := by
    intro n
    refine Work.BSKinetic.integrable_of_compact_support ?_
      ((strongMeasurable_bsW_cubeWin hM a (Work.OneBodyKin.measurable_Ftrunc c n)
        hψ.continuous).aestronglyMeasurable)
      ⟨_, fun u => by rw [Real.norm_of_nonneg (key_bsW_nonneg n u)]; exact key_bsW_le n u⟩
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, ?_⟩
    intro u hu
    by_contra hmem
    have hle : R ≤ ‖u‖ := by
      have h : ¬ (‖u‖ ≤ R) := by simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
      exact le_of_lt (not_le.mp h)
    rw [hRfar u hle, bsW_zero'] at hu
    exact hu rfl
  have bsW_mono_le : ∀ {n m : ℕ}, n ≤ m → ∀ u : E3, Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z)
      ≤ Work.BSKinetic.Decomp.bsW (Work.OneBodyKin.Ftrunc c m)
          (fun z : E3 => cubeWin M a u z * ψ z) := by
    intro n m hnm u
    rw [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsW]
    exact MeasureTheory.integral_mono (key_pint n u) (key_pint m u)
      (fun p => mul_le_mul_of_nonneg_right (Work.OneBodyKin.Ftrunc_mono_le c hnm ‖p‖)
        (sq_nonneg _))
  -- the lintegral identity per truncation
  have key_ofReal : ∀ (n : ℕ) (u : E3), ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z))
      = ∫⁻ p : E3, ENNReal.ofReal (Work.OneBodyKin.Ftrunc c n ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2) := by
    intro n u
    rw [Work.BSKinetic.Decomp.bsW]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (key_pint n u)
      (Filter.Eventually.of_forall fun p =>
        mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n _) (sq_nonneg _))
  -- the pointwise-upward-limit identity in the momentum, for each box centre
  have key_sup : ∀ u : E3, (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))
      = ⨆ n : ℕ, ENNReal.ofReal (Work.BSKinetic.Decomp.bsW (Work.OneBodyKin.Ftrunc c n)
          (fun z : E3 => cubeWin M a u z * ψ z)) := by
    intro u
    have hpt : (fun p : E3 => ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))
        = fun p : E3 => ⨆ n : ℕ, ENNReal.ofReal (Work.OneBodyKin.Ftrunc c n ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2) := by
      funext p
      have hmono : Monotone (fun n : ℕ => ENNReal.ofReal (Work.OneBodyKin.Ftrunc c n ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)) :=
        fun n m hnm => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (Work.OneBodyKin.Ftrunc_mono_le c hnm ‖p‖) (sq_nonneg _))
      have hlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Work.OneBodyKin.Ftrunc c n ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))
          Filter.atTop (𝓝 (ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          ((Work.OneBodyKin.Ftrunc_tendsto c ‖p‖).mul_const _)
      exact (tendsto_nhds_unique (tendsto_atTop_iSup hmono) hlim).symm
    rw [hpt]
    rw [MeasureTheory.lintegral_iSup]
    · congr 1
      funext n
      exact (key_ofReal n u).symm
    · intro n
      have hcontK : Continuous (fun p : E3 =>
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2) :=
        ((Work.OneBodyKin.continuous_kinFT
          (Complex.ofRealCLM.integrable_comp (integrable_cubeWin_mul hM ha u hψ hcs))).norm).pow 2
      exact ENNReal.measurable_ofReal.comp
        (((Work.OneBodyKin.measurable_Ftrunc c n).comp continuous_norm.measurable).mul
          hcontK.measurable)
    · intro n m hnm p
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (Work.OneBodyKin.Ftrunc_mono_le c hnm ‖p‖) (sq_nonneg _))
  -- the box-centre supremum is finite
  have key_u : (∫⁻ u : E3, ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))
      = ⨆ n : ℕ, ∫⁻ u : E3, ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
          (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z)) := by
    have hΛeq : (fun u : E3 => ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))
        = fun u : E3 => ⨆ n : ℕ, ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
            (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z)) :=
      funext key_sup
    rw [hΛeq]
    refine MeasureTheory.lintegral_iSup (fun n => ?_) (fun n m hnm u => ?_)
    · exact ENNReal.measurable_ofReal.comp ((strongMeasurable_bsW_cubeWin hM a
        (Work.OneBodyKin.measurable_Ftrunc c n) hψ.continuous).measurable)
    · exact ENNReal.ofReal_le_ofReal (bsW_mono_le hnm u)
  have hbound_u : ∀ n : ℕ, ∫⁻ u : E3, ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z))
      ≤ ENNReal.ofReal (∫ q : E3, (A * ‖q‖ ^ 2 + B) *
          ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2) := by
    intro n
    have hsym : (∫ u : E3, Work.BSKinetic.Decomp.bsW (Work.OneBodyKin.Ftrunc c n)
        (fun z : E3 => cubeWin M a u z * ψ z))
        = ∫ q : E3, symACube M a (Work.OneBodyKin.Ftrunc c n) q *
            ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2 :=
      cubeWin_bsW_integral_eq_symbol M hM ha (Work.OneBodyKin.integrable_Ftrunc c n)
        (fun r => Work.OneBodyKin.Ftrunc_nonneg c n r) hψ hcs
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (key_int n)
      (Filter.Eventually.of_forall fun u => key_bsW_nonneg n u), hsym]
    refine ENNReal.ofReal_le_ofReal ?_
    refine MeasureTheory.integral_mono_of_nonneg ?_ hKint ?_
    · refine Filter.Eventually.of_forall fun q => ?_
      have hnn : 0 ≤ symACube M a (Work.OneBodyKin.Ftrunc c n) q := by
        rw [symACube]
        exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun p =>
          mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n _) (sq_nonneg _))
      exact mul_nonneg hnn (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun q => mul_le_mul_of_nonneg_right
        (hAB (Work.OneBodyKin.Ftrunc c n) (fun r _ => Work.OneBodyKin.Ftrunc_nonneg c n r)
          (fun r hr => le_trans (Work.OneBodyKin.Ftrunc_le_fsKinCoeff c n r)
            (Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul c r)) q) (sq_nonneg _)
  have hΛfin : (∫⁻ u : E3, ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)) < ⊤ := by
    rw [key_u]
    refine lt_of_le_of_lt (iSup_le hbound_u) ?_
    exact ENNReal.ofReal_lt_top
  -- the limit function
  let F : E3 → ℝ := fun u => ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2
  have hFu : ∀ u : E3, F u = (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)).toReal := by
    intro u
    have hcont1 : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) :=
      ((continuous_norm.sub continuous_const).max continuous_const).pow 2
    have hcont2 : Continuous (fun p : E3 => ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2) :=
      ((Work.OneBodyKin.continuous_kinFT
        (Complex.ofRealCLM.integrable_comp (integrable_cubeWin_mul hM ha u hψ hcs))).norm).pow 2
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c _) (sq_nonneg _))
      (hcont1.mul hcont2).aestronglyMeasurable
  have hΛmeas : Measurable (fun u : E3 => ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)) := by
    have hΛeq : (fun u : E3 => ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))
        = fun u : E3 => ⨆ n : ℕ, ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
            (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z)) :=
      funext key_sup
    rw [hΛeq]
    exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
      ((strongMeasurable_bsW_cubeWin hM a (Work.OneBodyKin.measurable_Ftrunc c n)
        hψ.continuous).measurable)
  have hΛlt : ∀ᵐ u : E3 ∂volume, (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)) < ⊤ :=
    MeasureTheory.ae_lt_top' hΛmeas.aemeasurable (ne_of_lt hΛfin)
  have hFint : MeasureTheory.Integrable F := by
    refine ⟨?_, ?_⟩
    · exact (strongMeasurable_bsW_cubeWin hM a (by
        have hcont : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
          rw [show Submission.BoseGases.fsKinCoeff c
              = fun r : ℝ => (max (r - c) 0) ^ 2 from rfl]
          exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
        exact hcont.measurable) hψ.continuous).aestronglyMeasurable
    · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun u => MeasureTheory.integral_nonneg fun p =>
          mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c _) (sq_nonneg _))]
      refine lt_of_le_of_lt ?_ hΛfin
      refine MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall fun u => ?_)
      change ENNReal.ofReal (F u) ≤ ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)
      rw [hFu u]
      exact ENNReal.ofReal_toReal_le
  have hmono_ae : ∀ᵐ u : E3 ∂volume, Monotone (fun n : ℕ => Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z)) :=
    Filter.Eventually.of_forall fun u => fun n m hnm => bsW_mono_le hnm u
  have hconv : ∀ᵐ u : E3 ∂volume, Filter.Tendsto (fun n : ℕ => Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z))
      Filter.atTop (𝓝 (F u)) := by
    filter_upwards [hΛlt] with u hu
    have hmct : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
        (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z))) Filter.atTop
        (𝓝 (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2))) := by
      rw [key_sup u]
      exact tendsto_atTop_iSup (fun n m hnm =>
        ENNReal.ofReal_le_ofReal (bsW_mono_le hnm u))
    have h2 : Filter.Tendsto (fun n : ℕ => (ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
        (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z))).toReal) Filter.atTop
        (𝓝 ((∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => cubeWin M a u z * ψ z) p‖ ^ 2)).toReal)) :=
      Tendsto.congr (fun n => rfl)
        ((ENNReal.tendsto_toReal (ne_of_lt hu)).comp hmct)
    have h3 : (fun n : ℕ => (ENNReal.ofReal (Work.BSKinetic.Decomp.bsW
        (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z))).toReal)
        = fun n : ℕ => Work.BSKinetic.Decomp.bsW (Work.OneBodyKin.Ftrunc c n)
            (fun z : E3 => cubeWin M a u z * ψ z) :=
      funext fun n => ENNReal.toReal_ofReal (key_bsW_nonneg n u)
    rw [h3, ← hFu u] at h2
    exact h2
  have hmain : Filter.Tendsto (fun n : ℕ => ∫ u : E3, Work.BSKinetic.Decomp.bsW
      (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z))
      Filter.atTop (𝓝 (∫ u : E3, F u)) :=
    MeasureTheory.integral_tendsto_of_tendsto_of_monotone (fun n => key_int n) hFint
      hmono_ae hconv
  have hL : (fun n : ℕ => Work.BoseFixB1S.bsFamilyFormUnprojCube M a
        (Work.OneBodyKin.Ftrunc c n) ψ)
      = fun n : ℕ => ((2 * Real.pi) ^ 3)⁻¹ * ∫ u : E3, Work.BSKinetic.Decomp.bsW
          (Work.OneBodyKin.Ftrunc c n) (fun z : E3 => cubeWin M a u z * ψ z) :=
    funext fun n => cubeFamFormUnprojCube_eq_bsW_integral M a (Work.OneBodyKin.Ftrunc c n)
  have hR : Work.BoseFixB1S.bsFamilyFormUnprojCube M a (Submission.BoseGases.fsKinCoeff c) ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ u : E3, F u :=
    cubeFamFormUnprojCube_eq_bsW_integral M a (Submission.BoseGases.fsKinCoeff c)
  rw [hL, hR]
  exact hmain.const_mul _

end Work.BoseFixB1S
