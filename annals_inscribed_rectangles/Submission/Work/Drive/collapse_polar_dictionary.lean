import Mathlib
import Submission.Work.Drive.hdensePolarDefs
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.squareDisk
import Submission.Work.Drive.sideGermDefs

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-! ## 1. The radial normalisation of `ℂ` -/

lemma contDiff_normSq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.normSq := by
  have h : Complex.normSq = fun z : ℂ => z.re ^ 2 + z.im ^ 2 := by
    funext z; rw [Complex.normSq_apply]; ring
  rw [h]
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.reCLM z ^ 2) :=
    (Complex.reCLM.contDiff).pow 2
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.imCLM z ^ 2) :=
    (Complex.imCLM.contDiff).pow 2
  simpa [Complex.reCLM_apply, Complex.imCLM_apply] using h1.add h2

/-- **The radial normalisation** `z ↦ ‖z‖⁻¹ • z` of `ℂ` (the radial projection onto the unit
circle). -/
noncomputable def polarNorm (z : ℂ) : ℂ := (‖z‖)⁻¹ • z

@[simp] lemma polarNorm_eq (z : ℂ) : polarNorm z = (‖z‖)⁻¹ • z := rfl

lemma norm_polarNorm {z : ℂ} (hz : z ≠ 0) : ‖polarNorm z‖ = 1 := by
  rw [polarNorm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

lemma polarNorm_ne_zero {z : ℂ} (hz : z ≠ 0) : polarNorm z ≠ 0 := by
  intro h
  have := norm_polarNorm hz
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

lemma polarNorm_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : polarNorm z = z := by
  rw [polarNorm, hz, inv_one, one_smul]

lemma polarNorm_smul_pos {z : ℂ} {c : ℝ} (hc : 0 < c) : polarNorm (c • z) = polarNorm z := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [polarNorm, polarNorm, norm_smul, Real.norm_eq_abs, abs_of_pos hc, Complex.real_smul,
    Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp

lemma polarNorm_mul_unit {z : ℂ} {w : ℂ} (hw : ‖w‖ = 1) : polarNorm (w * z) = w * polarNorm z := by
  rw [polarNorm, polarNorm, norm_mul, hw, one_mul, Complex.real_smul, Complex.real_smul]
  ring

lemma contDiffAt_polarNorm {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) polarNorm z := by
  have hns : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => Complex.normSq w) z :=
    contDiff_normSq.contDiffAt
  have hpos : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  have hsqrt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => Real.sqrt (Complex.normSq w)) z := hns.sqrt hpos
  have hval : Real.sqrt (Complex.normSq z) = ‖z‖ := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  have hinv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => (Real.sqrt (Complex.normSq w))⁻¹) z :=
    hsqrt.inv (by rw [hval]; exact norm_ne_zero_iff.mpr hz)
  have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => (Real.sqrt (Complex.normSq w))⁻¹ • w) z := hinv.smul contDiffAt_id
  have hfun : (fun w : ℂ => (Real.sqrt (Complex.normSq w))⁻¹ • w) = polarNorm := by
    funext w
    rw [polarNorm, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  rw [hfun] at hsm
  exact hsm

lemma mdifferentiableAt_polarNorm {z : ℂ} (hz : z ≠ 0) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) polarNorm z :=
  (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_polarNorm hz)).mdifferentiableAt (by simp)

lemma hasFDerivAt_polarNorm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt polarNorm (fderiv ℝ polarNorm z) z :=
  ((contDiffAt_polarNorm hz).differentiableAt (by simp)).hasFDerivAt

/-- **The radial direction is killed** by the derivative of the radial normalisation. -/
theorem fderiv_polarNorm_self {z : ℂ} (hz : z ≠ 0) : fderiv ℝ polarNorm z z = 0 := by
  have hA := hasFDerivAt_polarNorm hz
  have hg : HasDerivAt (fun r : ℝ => (1 + r) • z) z 0 := by
    have h1 : HasDerivAt (fun r : ℝ => r • z) ((1 : ℝ) • z) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const z
    have h2 := h1.const_add z
    have hfun : (fun r : ℝ => z + r • z) = fun r : ℝ => (1 + r) • z := by
      funext r; rw [add_smul, one_smul]
    rw [hfun] at h2
    simpa using h2
  have hA' : HasFDerivAt polarNorm (fderiv ℝ polarNorm z) ((1 + (0 : ℝ)) • z) := by
    simpa using hA
  have h1 : HasDerivAt (fun r : ℝ => polarNorm ((1 + r) • z)) (fderiv ℝ polarNorm z z) 0 := by
    have := hA'.comp_hasDerivAt 0 hg
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun r : ℝ => polarNorm ((1 + r) • z)) 0 0 := by
    refine (Filter.EventuallyEq.hasDerivAt_iff ?_).mpr (hasDerivAt_const (0 : ℝ) (polarNorm z))
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with r hr
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hr
    exact polarNorm_smul_pos (z := z) (by linarith : 0 < 1 + r)
  exact h1.unique h2

/-- **The tangential direction is rotated** by the derivative of the radial normalisation. -/
theorem fderiv_polarNorm_I_mul {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ polarNorm z (Complex.I * z) = Complex.I * polarNorm z := by
  have hA' : HasFDerivAt polarNorm (fderiv ℝ polarNorm z) (Complex.exp (0 * Complex.I) * z) := by
    simpa using hasFDerivAt_polarNorm hz
  have hinner : HasDerivAt (fun r : ℝ => (r : ℂ) * Complex.I) (1 * Complex.I) 0 :=
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) Complex.ofRealCLM).hasDerivAt.mul_const Complex.I
  have hexp : HasDerivAt (fun r : ℝ => Complex.exp (r * Complex.I)) Complex.I 0 := by
    have h := hinner.cexp
    simpa using h
  have hg : HasDerivAt (fun r : ℝ => Complex.exp (r * Complex.I) * z) (Complex.I * z) 0 := by
    simpa using hexp.mul_const z
  have h1 : HasDerivAt (fun r : ℝ => polarNorm (Complex.exp (r * Complex.I) * z))
      (fderiv ℝ polarNorm z (Complex.I * z)) 0 := by
    have := hA'.comp_hasDerivAt 0 hg
    simpa [Function.comp_def] using this
  have hexp2 : HasDerivAt (fun r : ℝ => Complex.exp (r * Complex.I) * polarNorm z)
      (Complex.I * polarNorm z) 0 := by
    simpa using hexp.mul_const (polarNorm z)
  have hn : ∀ r : ℝ, ‖Complex.exp (r * Complex.I)‖ = 1 := by
    intro r; rw [Complex.norm_exp]; simp
  have hev : (fun r : ℝ => polarNorm (Complex.exp (r * Complex.I) * z))
      =ᶠ[nhds (0 : ℝ)] (fun r : ℝ => Complex.exp (r * Complex.I) * polarNorm z) := by
    filter_upwards with r
    exact polarNorm_mul_unit (hn r)
  have h2 := hexp2.congr_of_eventuallyEq hev
  exact h1.unique h2

/-- **The decomposition of `ℂ` along the basis `z`, `I z`.** -/
theorem exists_eq_smul_add_smul_I (z v : ℂ) (hz : z ≠ 0) :
    ∃ a b : ℝ, a • z + b • (Complex.I * z) = v := by
  set q := v * starRingEnd ℂ z with hq
  set N := Complex.normSq z with hNm
  refine ⟨q.re / N, q.im / N, ?_⟩
  have hNpos : 0 < N := Complex.normSq_pos.mpr hz
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hqsum : q = (N : ℂ) * (↑(q.re / N) + ↑(q.im / N) * Complex.I) := by
    nth_rewrite 1 [← Complex.re_add_im q]
    push_cast
    field_simp
  have hqz : q * z = v * (N : ℂ) := by
    rw [hq, hNm, mul_assoc, Complex.conj_mul' z, ← Complex.ofReal_pow,
      ← Complex.normSq_eq_norm_sq]
  have h4 : (N : ℂ) * ((↑(q.re / N) + ↑(q.im / N) * Complex.I) * z) = (N : ℂ) * v := by
    rw [← mul_assoc, ← hqsum, hqz]
    ring
  have hsz : (↑(q.re / N) + ↑(q.im / N) * Complex.I) * z = v := mul_left_cancel₀ hNne h4
  rw [Complex.real_smul, Complex.real_smul, ← hsz]
  ring

/-- The image of the derivative of the radial normalisation is the tangent line at `polarNorm z`. -/
theorem fderiv_polarNorm_mem_span {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ polarNorm z v ∈ Submodule.span ℝ {Complex.I * polarNorm z} := by
  obtain ⟨a, b, hab⟩ := exists_eq_smul_add_smul_I z v hz
  rw [← hab, map_add, map_smul, map_smul, fderiv_polarNorm_self hz, fderiv_polarNorm_I_mul hz,
    smul_zero, zero_add]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The kernel of the derivative of the radial normalisation is the radial line. -/
theorem fderiv_polarNorm_eq_zero_iff {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ polarNorm z v = 0 ↔ v ∈ Submodule.span ℝ {z} := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := exists_eq_smul_add_smul_I z v hz
    have hI : Complex.I * polarNorm z ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (polarNorm_ne_zero hz)
    have hb : b = 0 := by
      have h2 : b • (Complex.I * polarNorm z) = 0 := by
        have h3 := h
        rw [← hab, map_add, map_smul, map_smul, fderiv_polarNorm_self hz,
          fderiv_polarNorm_I_mul hz, smul_zero, zero_add] at h3
        exact h3
      rcases (smul_eq_zero.mp h2) with h4 | h4
      · exact h4
      · exact absurd h4 hI
    rw [hb, zero_smul, add_zero] at hab
    rw [← hab]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨c, rfl⟩ := h
    rw [map_smul, fderiv_polarNorm_self hz, smul_zero]

/-! ## 2. The folded square-to-disk parametrisation -/

/-- The square-to-disk parametrisation of the folded square, as a map into `ℂ`. -/
noncomputable def cdFoldDisk (y : EuclideanSpace ℝ (Fin 2)) : ℂ := sqDisk (foldBox y)

lemma diskPlane_eq_cdFoldDisk (Q : ℂ → CappingSpace) :
    diskPlane Q = Q ∘ cdFoldDisk := rfl

lemma colPlane_eq_cdFoldDisk (β : ℝ → ℝ) (Q : ℂ → CappingSpace) (s : ℝ) :
    colPlane β Q s = Q ∘ (fun y => colMap β s (cdFoldDisk y)) := rfl

lemma contDiff_foldBox : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) foldBox :=
  contDiff_iff_contDiffAt.mpr fun y => contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff y)

lemma contDiff_cdFoldDisk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cdFoldDisk :=
  sqDisk_contDiff.comp contDiff_foldBox

lemma mdiff_cdFoldDisk (y : EuclideanSpace ℝ (Fin 2)) :
    MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk y :=
  (contMDiffAt_iff_contDiffAt.mpr (contDiff_cdFoldDisk.contDiffAt)).mdifferentiableAt (by simp)

/-- The chart of a smooth disk presentation is manifold-differentiable everywhere. -/
lemma mdiff_chart {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (z : ℂ) :
    MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 4) Q z :=
  hQsm.mdifferentiableAt (by simp)

/-! ## 3. The parameter of the circle and the two loops -/

/-- The affine parameter of the diameter loop has the derivative `-2`. -/
lemma hasDerivAt_diamParam (t : ℝ) (σ : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - 2 * s) * colCirclePt t) ((-2 : ℝ) • colCirclePt t) σ := by
  have h2 : HasDerivAt (fun s : ℝ => (2 : ℝ) * s) 2 σ := by
    simpa [mul_comm] using (hasDerivAt_id σ).const_mul (2 : ℝ)
  have hlin : HasDerivAt (fun s : ℝ => (1 - 2 * s : ℝ)) (-2) σ := by
    simpa using h2.const_sub (1 : ℝ)
  have h1 : HasDerivAt (fun s : ℝ => ((1 - 2 * s : ℝ) : ℂ)) ((-2 : ℝ) : ℂ) σ := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) Complex.ofRealCLM).comp_hasDerivAt σ hlin
  have h3 := h1.mul_const (colCirclePt t)
  have hv : (((-2 : ℝ) : ℂ) * colCirclePt t) = (-2 : ℝ) • colCirclePt t := by
    rw [Complex.real_smul]
  rw [hv] at h3
  simpa using h3

lemma mdiff_add_one (t : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ : ℝ => τ + 1) t :=
  ((hasDerivAt_id t).add_const 1).differentiableAt.mdifferentiableAt

/-- The parametrisation `t ↦ e^{iπt}` of the unit circle. -/
lemma hasDerivAt_colCirclePt (t : ℝ) :
    HasDerivAt colCirclePt (Real.pi * Complex.I * colCirclePt t) t := by
  have h0 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 t :=
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) Complex.ofRealCLM).hasDerivAt
  have h1 : HasDerivAt (fun r : ℝ => (Real.pi : ℂ) * (r : ℂ)) ((Real.pi : ℂ) * 1) t :=
    h0.const_mul (Real.pi : ℂ)
  have h2 : HasDerivAt (fun r : ℝ => (Real.pi : ℂ) * (r : ℂ) * Complex.I)
      (((Real.pi : ℂ) * 1) * Complex.I) t := h1.mul_const Complex.I
  have h3 : HasDerivAt (fun r : ℝ => Complex.exp ((Real.pi : ℂ) * (r : ℂ) * Complex.I))
      (Complex.exp ((Real.pi : ℂ) * (t : ℂ) * Complex.I) * (((Real.pi : ℂ) * 1) * Complex.I)) t :=
    h2.cexp
  have hfun : (fun r : ℝ => Complex.exp ((Real.pi : ℂ) * (r : ℂ) * Complex.I)) = colCirclePt := by
    funext r; rw [colCirclePt]
  rw [hfun] at h3
  have hder : Complex.exp ((Real.pi : ℂ) * (t : ℂ) * Complex.I)
      * (((Real.pi : ℂ) * 1) * Complex.I) = Real.pi * Complex.I * colCirclePt t := by
    rw [colCirclePt]; ring
  rwa [hder] at h3

lemma mdiff_colCirclePt (t : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) colCirclePt t :=
  (hasDerivAt_colCirclePt t).differentiableAt.mdifferentiableAt

/-- The derivative of the circle parametrisation, applied to the unit parameter. -/
lemma mfderiv_colCirclePt_apply (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) colCirclePt t (1 : ℝ)
      = Real.pi • (Complex.I * colCirclePt t) := by
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) colCirclePt t (1 : ℝ) = deriv colCirclePt t := by
    rw [mfderiv_eq_fderiv]; rfl
  have h2 : deriv colCirclePt t = Real.pi • (Complex.I * colCirclePt t) := by
    rw [(hasDerivAt_colCirclePt t).deriv, Complex.real_smul]
    ring
  rw [h1, h2]

lemma coreLoop_eq_col (Q : ℂ → CappingSpace) (t : ℝ) : coreLoop Q t = Q (colCirclePt t) := rfl

lemma coreLoop_fun_eq (Q : ℂ → CappingSpace) : coreLoop Q = fun t : ℝ => Q (colCirclePt t) := rfl

lemma diamLoop_eq' (Q : ℂ → CappingSpace) (t σ : ℝ) :
    diamLoop Q t σ = Q ((1 - 2 * σ) * colCirclePt t) := rfl

lemma diamLoop_fun_eq (Q : ℂ → CappingSpace) (t : ℝ) :
    diamLoop Q t = fun σ : ℝ => Q ((1 - 2 * σ) * colCirclePt t) := rfl

lemma coreLoop_fun_eq' (Q : ℂ → CappingSpace) :
    coreLoop Q = fun t : ℝ => Q (colCirclePt t) := rfl

/-- Rewriting the loop along an equality of its parameter functions. -/
lemma mfderiv_congr_fun_apply {f g : ℝ → CappingSpace} (h : f = g) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 4) f t (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) (𝓡 4) g t (1 : ℝ) := by
  rw [h]

/-- The core loop is manifold-differentiable. -/
lemma mdiff_coreLoop {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (t : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) t := by
  rw [coreLoop_fun_eq]
  simpa [Function.comp_def] using
    (mdiff_chart hQsm (colCirclePt t)).comp t (mdiff_colCirclePt t)

/-- The diameter loop is manifold-differentiable. -/
lemma mdiff_diamLoop {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (t σ : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ := by
  rw [diamLoop_fun_eq]
  simpa [Function.comp_def] using
    (mdiff_chart hQsm ((1 - 2 * σ) * colCirclePt t)).comp σ
      (hasDerivAt_diamParam t σ).differentiableAt.mdifferentiableAt

/-- **The core loop is `1`-periodic** whenever the chart fixes antipodal pairs of the unit circle. -/
lemma coreLoop_add_one {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (t : ℝ) :
    coreLoop Q (t + 1) = coreLoop Q t := by
  rw [coreLoop_eq_col, coreLoop_eq_col, colCirclePt_add_one]
  exact hQseam _ (by simp)

/-- **The derivative of the core loop transfers between the two branches** of the circle
parametrisation. -/
lemma mfderiv_coreLoop_add_one {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) (t + 1) (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) t (1 : ℝ) := by
  have hfun : (fun τ : ℝ => coreLoop Q (τ + 1)) = coreLoop Q :=
    funext (coreLoop_add_one hQseam)
  have hA : mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (fun τ : ℝ => coreLoop Q (τ + 1)) t (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) t (1 : ℝ) :=
    mfderiv_congr_fun_apply hfun t
  have h := mfderiv_comp_apply t (g := coreLoop Q) (f := fun τ : ℝ => τ + 1)
    (mdiff_coreLoop hQsm (t + 1)) (mdiff_add_one t) (1 : ℝ)
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ : ℝ => τ + 1) t (1 : ℝ) = 1 := by
    rw [mfderiv_eq_fderiv]
    show (fderiv ℝ (fun τ : ℝ => τ + 1) t) (1 : ℝ) = (1 : ℝ)
    have h1 : HasDerivAt (fun τ : ℝ => τ + 1) 1 t := (hasDerivAt_id t).add_const 1
    rw [h1.hasFDerivAt.fderiv]
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hd] at h
  have hB : mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (fun τ : ℝ => coreLoop Q (τ + 1)) t (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) (t + 1) (1 : ℝ) := by
    simpa [Function.comp_def] using h
  exact hB.symm.trans hA

/-- **The derivative of the core loop, applied to the unit parameter.** -/
lemma mfderiv_coreLoop_apply {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (τ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) τ (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℂ) (𝓡 4) Q (colCirclePt τ)
          (Real.pi • (Complex.I * colCirclePt τ)) := by
  have h := mfderiv_comp_apply τ (g := Q) (f := colCirclePt)
    (mdiff_chart hQsm (colCirclePt τ)) (mdiff_colCirclePt τ) (1 : ℝ)
  rw [mfderiv_colCirclePt_apply] at h
  have hA : mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) τ (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (fun x : ℝ => Q (colCirclePt x)) τ (1 : ℝ) :=
    mfderiv_congr_fun_apply (coreLoop_fun_eq Q).symm τ
  exact hA.trans (by simpa [Function.comp_def] using h)

lemma mfderiv_diamParam_apply (t σ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun s : ℝ => (1 - 2 * s) * colCirclePt t) σ (1 : ℝ)
      = (-2 : ℝ) • colCirclePt t := by
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun s : ℝ => (1 - 2 * s) * colCirclePt t) σ (1 : ℝ)
      = deriv (fun s : ℝ => (1 - 2 * s) * colCirclePt t) σ := by
    rw [mfderiv_eq_fderiv]; rfl
  rw [h1, (hasDerivAt_diamParam t σ).deriv]

/-- **The derivative of the diameter loop, applied to the unit parameter.** -/
lemma mfderiv_diamLoop_apply {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (t σ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℂ) (𝓡 4) Q ((1 - 2 * σ) * colCirclePt t)
          ((-2 : ℝ) • colCirclePt t) := by
  have h := mfderiv_comp_apply σ (g := Q) (f := fun σ : ℝ => (1 - 2 * σ) * colCirclePt t)
    (mdiff_chart hQsm ((1 - 2 * σ) * colCirclePt t))
    (hasDerivAt_diamParam t σ).differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [mfderiv_diamParam_apply] at h
  have hA : mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 4)
          (fun x : ℝ => Q ((1 - 2 * x) * colCirclePt t)) σ (1 : ℝ) :=
    mfderiv_congr_fun_apply (diamLoop_fun_eq Q t).symm σ
  exact hA.trans (by simpa [Function.comp_def] using h)

/-- **The derivative of the honest disk plane**, applied to a direction. -/
lemma mfderiv_diskPlane_apply {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (y : EuclideanSpace ℝ (Fin 2)) (a : EuclideanSpace ℝ (Fin 2)) :
    mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) y a
      = mfderiv 𝓘(ℝ, ℂ) (𝓡 4) Q (cdFoldDisk y)
          (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk y a) := by
  have h := mfderiv_comp_apply y (g := Q) (f := cdFoldDisk)
    (mdiff_chart hQsm (cdFoldDisk y)) (mdiff_cdFoldDisk y) a
  rw [diskPlane_eq_cdFoldDisk]
  simpa [Function.comp_def] using h

/-- **The derivative of the collapsed plane at `s = 1` on the collar**, applied to a direction: the
chain rule through `Q ∘ (polarNorm ∘ cdFoldDisk)`. -/
theorem mfderiv_colPlane_one_apply {β : ℝ → ℝ} {δc : ℝ} (hδc : 0 ≤ δc)
    (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t) {Q : ℂ → CappingSpace}
    (hQsm : IsSmoothChart Q) (u : EuclideanSpace ℝ (Fin 2))
    (hcol : δc < ‖cdFoldDisk u‖) (a : EuclideanSpace ℝ (Fin 2)) :
    mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) u a
      = mfderiv 𝓘(ℝ, ℂ) (𝓡 4) Q (polarNorm (cdFoldDisk u))
          (fderiv ℝ polarNorm (cdFoldDisk u)
            (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk u a)) := by
  have hne : cdFoldDisk u ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hδc hcol)
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 2) => ‖cdFoldDisk y‖ :=
    continuous_norm.comp contDiff_cdFoldDisk.continuous
  have hmem : ∀ᶠ y in 𝓝 u, δc < ‖cdFoldDisk y‖ :=
    (isOpen_lt continuous_const hcont).mem_nhds hcol
  have hev : colPlane β Q 1 =ᶠ[𝓝 u]
      fun y : EuclideanSpace ℝ (Fin 2) => Q (polarNorm (cdFoldDisk y)) := by
    filter_upwards [hmem] with y hy
    rw [colPlane_eq_cdFoldDisk, Function.comp_apply,
      colMap_one_of_collar hδc hβδ _ (le_of_lt hy)]
    rfl
  have hkey := mfderiv_comp_apply u (g := Q) (f := polarNorm ∘ cdFoldDisk)
    (mdiff_chart hQsm (polarNorm (cdFoldDisk u)))
    ((mdifferentiableAt_polarNorm hne).comp u (mdiff_cdFoldDisk u)) a
  have hkey2 := mfderiv_comp_apply u (g := polarNorm) (f := cdFoldDisk)
    (mdifferentiableAt_polarNorm hne) (mdiff_cdFoldDisk u) a
  rw [hkey2] at hkey
  have hN : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) polarNorm (cdFoldDisk u)
      = fderiv ℝ polarNorm (cdFoldDisk u) := mfderiv_eq_fderiv
  rw [hN] at hkey
  have hpu : colPlane β Q 1 u = Q (polarNorm (cdFoldDisk u)) := by
    rw [colPlane_eq_cdFoldDisk, Function.comp_apply,
      colMap_one_of_collar hδc hβδ _ (le_of_lt hcol)]
    rfl
  have heq : mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) u
      = mfderiv (𝓡 2) (𝓡 4) (Q ∘ (polarNorm ∘ cdFoldDisk)) u :=
    (Filter.EventuallyEq.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 4) (x := u) (f₁ := colPlane β Q 1)
      (f := Q ∘ (polarNorm ∘ cdFoldDisk))
      (by simpa only [Function.comp_def] using hev)).trans (by ext v; rfl)
  rw [heq, hpu]
  exact hkey

/-! ## 3bis. The chart derivative as a plain linear map

`Work.Drive.chartDerivC Q z` is `mfderiv Q z` with its source and target written in the *model*
spaces `ℂ` and `EuclideanSpace ℝ (Fin 4)`, so that applying it to a complex vector and taking scalar
multiples needs no coercion into the tangent spaces. -/

noncomputable def chartDerivC (Q : ℂ → CappingSpace) (z : ℂ) :
    ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv 𝓘(ℝ, ℂ) (𝓡 4) Q z

lemma chartDerivC_apply {Q : ℂ → CappingSpace} (z w : ℂ) :
    chartDerivC Q z w = (mfderiv 𝓘(ℝ, ℂ) (𝓡 4) Q z) w := rfl

lemma chartDerivC_smul {Q : ℂ → CappingSpace} (z : ℂ) (c : ℝ) (w : ℂ) :
    chartDerivC Q z (c • w) = c • chartDerivC Q z w :=
  map_smul _ _ _

lemma chartDerivC_congr {Q : ℂ → CappingSpace} {z z' : ℂ} (h : z = z') :
    chartDerivC Q z = chartDerivC Q z' := by rw [h]

/-- The collapsed plane's derivative, in the model-space form. -/
theorem mfderiv_colPlane_one_chartDeriv {β : ℝ → ℝ} {δc : ℝ} (hδc : 0 ≤ δc)
    (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t) {Q : ℂ → CappingSpace}
    (hQsm : IsSmoothChart Q) (u : EuclideanSpace ℝ (Fin 2))
    (hcol : δc < ‖cdFoldDisk u‖) (a : EuclideanSpace ℝ (Fin 2)) :
    (mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) u) a
      = chartDerivC Q (polarNorm (cdFoldDisk u))
          (fderiv ℝ polarNorm (cdFoldDisk u)
            (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk u a)) :=
  mfderiv_colPlane_one_apply hδc hβδ hQsm u hcol a

/-- The honest disk plane's derivative, in the model-space form. -/
theorem mfderiv_diskPlane_chartDeriv {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (u : EuclideanSpace ℝ (Fin 2)) (a : EuclideanSpace ℝ (Fin 2)) :
    (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) u) a
      = chartDerivC Q (cdFoldDisk u) (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk u a) :=
  mfderiv_diskPlane_apply hQsm u a

/-- The core loop's derivative, in the model-space form. -/
theorem mfderiv_coreLoop_chartDeriv {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (τ : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) τ) (1 : ℝ)
      = chartDerivC Q (colCirclePt τ) (Real.pi • (Complex.I * colCirclePt τ)) :=
  mfderiv_coreLoop_apply hQsm τ

/-- The diameter loop's derivative, in the model-space form. -/
theorem mfderiv_diamLoop_chartDeriv {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (t σ : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ) (1 : ℝ)
      = chartDerivC Q ((1 - 2 * σ) * colCirclePt t) ((-2 : ℝ) • colCirclePt t) :=
  mfderiv_diamLoop_apply hQsm t σ

/-- The same with the base point of the chart derivative written as a real multiple. -/
theorem mfderiv_diamLoop_chartDeriv' {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (t σ : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ) (1 : ℝ)
      = chartDerivC Q ((1 - 2 * σ) • colCirclePt t) ((-2 : ℝ) • colCirclePt t) := by
  rw [mfderiv_diamLoop_chartDeriv hQsm t σ]
  congr 1
  simp only [Complex.real_smul]
  push_cast
  ring

/-! ## 4. The parameter of the polar dictionary -/

/-- A linear map out of the one-dimensional space `ℝ` is determined by its value at `1`. -/
lemma clm_eq_zero_of_one {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (f : ℝ →L[ℝ] E) (h : f 1 = 0) : f = 0 := by
  ext
  simpa using h

/-- The polar exponent of `z` is the radial normalisation of `z`. -/
lemma exp_arg_eq_polarNorm (z : ℂ) (hz : z ≠ 0) :
    Complex.exp ((z.arg : ℂ) * Complex.I) = polarNorm z := by
  have hz0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using (norm_ne_zero_iff.mpr hz)
  refine mul_left_cancel₀ hz0 ?_
  rw [Complex.norm_mul_exp_arg_mul_I z, polarNorm, Complex.real_smul, Complex.ofReal_inv,
    ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]

/-- **The argument of `z` is the circle parameter of its radial normalisation.** -/
lemma colCirclePt_arg_div_pi (z : ℂ) (hz : z ≠ 0) :
    colCirclePt (z.arg / Real.pi) = polarNorm z := by
  have harg : (Real.pi : ℂ) * ((z.arg / Real.pi : ℝ) : ℂ) = (z.arg : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [colCirclePt, harg, exp_arg_eq_polarNorm z hz]

/-- **The polar parametrisation of a point of the disk.**  For `0 < ‖z‖ ≤ 1` there is a core
parameter `τ` with `colCirclePt τ = polarNorm z`, a diameter parameter `σ ∈ [0,1]` and a time
`t ∈ [0,1]` equal to `τ` or to `τ + 1` and representing the same core point, with
`(1 - 2σ) · colCirclePt t = z`. -/
theorem exists_colParam {z : ℂ} (hz : z ≠ 0) (hzle : ‖z‖ ≤ 1) :
    ∃ τ : ℝ, colCirclePt τ = polarNorm z ∧
      ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) 1 ∧
        (t = τ ∨ t = τ + 1) ∧ (1 - 2 * σ) * colCirclePt t = z := by
  refine ⟨z.arg / Real.pi, colCirclePt_arg_div_pi z hz, ?_⟩
  have hdiv : z.arg / Real.pi ≤ 1 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Complex.arg_le_pi z]
  have hdiv' : -1 < z.arg / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    linarith [Complex.neg_pi_lt_arg z]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hzpos.ne'
  by_cases h : 0 ≤ z.arg / Real.pi
  · refine ⟨z.arg / Real.pi, ⟨h, hdiv⟩, (1 - ‖z‖) / 2, ⟨by linarith, by linarith⟩, Or.inl rfl,
      ?_⟩
    have hcoef : (1 : ℂ) - 2 * (((1 - ‖z‖) / 2 : ℝ) : ℂ) = ((‖z‖ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcoef, colCirclePt_arg_div_pi z hz, polarNorm, Complex.real_smul, Complex.ofReal_inv,
      ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  · refine ⟨z.arg / Real.pi + 1, ⟨by linarith, by linarith⟩, (1 + ‖z‖) / 2,
      ⟨by linarith, by linarith⟩, Or.inr rfl, ?_⟩
    have hcoef : (1 : ℂ) - 2 * (((1 + ‖z‖) / 2 : ℝ) : ℂ) = -((‖z‖ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcoef, colCirclePt_add_one, colCirclePt_arg_div_pi z hz, polarNorm, Complex.real_smul,
      Complex.ofReal_inv, neg_mul_neg, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]

/-- **The derivative part of the polar dictionary**, from the parametrisation data: `τ` is the core
parameter of the polar normalisation of `cdFoldDisk u`, `t` its lift into `[0,1]`, and `σ` the
diameter parameter. -/
theorem polarDict_of_data {β : ℝ → ℝ} {δc : ℝ} (hδc : 0 ≤ δc)
    (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {u : EuclideanSpace ℝ (Fin 2)} (hcol : δc < ‖cdFoldDisk u‖)
    {τ t σ : ℝ} (hτ : colCirclePt τ = polarNorm (cdFoldDisk u))
    (hcore : CoreImmersiveAt Q τ) (ht : t = τ ∨ t = τ + 1)
    (hσt : (1 - 2 * σ) * colCirclePt t = cdFoldDisk u) :
    PolarDict β Q u t σ := by
  have hz : cdFoldDisk u ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hδc hcol)
  have hσbase : cdFoldDisk u = (1 - 2 * σ) • colCirclePt t := by
    rw [Complex.real_smul]
    push_cast
    exact hσt.symm
  have hcoreeq : (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) τ) (1 : ℝ)
      = Real.pi • chartDerivC Q (polarNorm (cdFoldDisk u))
          (Complex.I * polarNorm (cdFoldDisk u)) := by
    rw [mfderiv_coreLoop_chartDeriv hQsm τ, hτ, chartDerivC_smul]
  have hXne : chartDerivC Q (polarNorm (cdFoldDisk u))
      (Complex.I * polarNorm (cdFoldDisk u)) ≠ 0 := by
    intro h0
    have h1 : (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) τ) (1 : ℝ) = 0 := by
      rw [hcoreeq, h0, smul_zero]
    exact hcore (clm_eq_zero_of_one _ h1)
  have htval : (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) t) (1 : ℝ)
      = (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) τ) (1 : ℝ) := by
    rcases ht with rfl | rfl
    · rfl
    · exact mfderiv_coreLoop_add_one hQsm hQseam τ
  constructor
  · intro a
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (fderiv_polarNorm_mem_span hz (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk u a))
    refine ⟨b / Real.pi, ?_⟩
    rw [mfderiv_colPlane_one_chartDeriv hδc hβδ hQsm u hcol a, ← hb, chartDerivC_smul,
      htval.trans hcoreeq, smul_smul, div_mul_cancel₀ _ Real.pi_ne_zero]
  · intro a ha
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (fderiv_polarNorm_mem_span hz (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk u a))
    have hb0 : b = 0 := by
      by_contra hbne
      have h1 : b • chartDerivC Q (polarNorm (cdFoldDisk u))
          (Complex.I * polarNorm (cdFoldDisk u)) = 0 := by
        have h2 := ha
        rw [mfderiv_colPlane_one_chartDeriv hδc hβδ hQsm u hcol a, ← hb, chartDerivC_smul] at h2
        exact h2
      refine hXne ?_
      have h3 := congrArg (fun y => b⁻¹ • y) h1
      simpa [smul_smul, inv_mul_cancel₀ hbne] using h3
    have hfv : fderiv ℝ polarNorm (cdFoldDisk u)
        (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk u a) = 0 := by
      rw [← hb, hb0, zero_smul]
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp
      ((fderiv_polarNorm_eq_zero_iff hz _).mp hfv)
    have hL : (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ) ((μ * (1 - 2 * σ)) / (-2))
        = ((μ * (1 - 2 * σ)) / (-2)) •
            ((mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ) (1 : ℝ)) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    have hR : (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) u) a
        = ((μ * (1 - 2 * σ)) / (-2)) •
            ((mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ) (1 : ℝ)) := by
      calc (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) u) a
          = chartDerivC Q (cdFoldDisk u) (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk u a) :=
            mfderiv_diskPlane_chartDeriv hQsm u a
        _ = chartDerivC Q (cdFoldDisk u) (μ • cdFoldDisk u) := by rw [← hμ]
        _ = μ • chartDerivC Q (cdFoldDisk u) (cdFoldDisk u) := chartDerivC_smul _ _ _
        _ = μ • chartDerivC Q ((1 - 2 * σ) • colCirclePt t)
              ((1 - 2 * σ) • colCirclePt t) := by rw [hσbase]
        _ = μ • ((1 - 2 * σ) • chartDerivC Q ((1 - 2 * σ) • colCirclePt t)
              (colCirclePt t)) := by rw [chartDerivC_smul]
        _ = (μ * (1 - 2 * σ)) • chartDerivC Q ((1 - 2 * σ) • colCirclePt t)
              (colCirclePt t) := by rw [← smul_smul]
        _ = (μ * (1 - 2 * σ)) • ((-2 : ℝ)⁻¹ • chartDerivC Q ((1 - 2 * σ) • colCirclePt t)
              ((-2 : ℝ) • colCirclePt t)) := by
            rw [chartDerivC_smul]
            congr 1
            rw [smul_smul, inv_mul_cancel₀ (by norm_num : (-2 : ℝ) ≠ 0), one_smul]
        _ = ((μ * (1 - 2 * σ)) / (-2)) • chartDerivC Q ((1 - 2 * σ) • colCirclePt t)
              ((-2 : ℝ) • colCirclePt t) := by
            rw [div_eq_mul_inv, smul_smul]
        _ = ((μ * (1 - 2 * σ)) / (-2)) •
              ((mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ) (1 : ℝ)) := by
            rw [mfderiv_diamLoop_chartDeriv' hQsm t σ]
    refine Set.mem_range.mpr ⟨(μ * (1 - 2 * σ)) / (-2), ?_⟩
    exact hL.trans hR.symm

end

end Work.Drive

namespace Work.Drive

/-- **The polar dictionary of the radial collapse at `s = 1`.**  Let `β` be a collar function
(`β t = √t` for `t ≥ δc²` with `δc ≥ 0`) and `Q` a smooth disk presentation fixing the antipodal pairs
of the unit circle.  For a point `u` of the *open* square with `δc < ‖sqDisk (foldBox u)‖` — so the
collapse at `s = 1` is the radial projection there (`colPlane_one_of_collar`) — there are a core-loop
parameter `t ∈ [0,1]` and a diameter parameter `σ ∈ [0,1]` with

* `colPlane β Q 1 u = coreLoop Q t` — the collapsed plane is a point of the core loop,
* `diskPlane Q u = diamLoop Q t σ` — the radial fibre over that core point is the diameter,
* `PolarDict β Q u t σ` — the derivative of the collapsed plane is a scalar multiple of the core loop's
  tangent at `t` (*this* is the conjunct that consumes `hcore`: `d(colPlane) = dQ (z₀) ∘ d(radial
  projection)` has image in the line `dQ (z₀) (i z₀) = d(coreLoop Q) t / π`, which is nonzero exactly
  under `hcore`), and every direction it kills (the *radial* direction) is sent by the honest plane
  `diskPlane Q` into the diameter loop's tangent at `σ`.

The hypothesis `hcore` is the *only* non-degeneracy input: it says the core loop `coreLoop Q` is
immersive at the polar parameter of `u`.  It cannot be dropped (a smooth `Q` with degenerate derivative
on the unit circle makes the first `PolarDict` conjunct false), and in the application
(`Work.Drive.pairOneData_of_T6GenAt`) it is supplied by the `GoodLoopChain` of `T6GenAt` at the core
meet, whose transversality `range dL ⊔ range dX = ⊤` forces `dL ≠ 0`.  The collar hypothesis is strict
because `hβδ` constrains `β` only on `[δc²,∞)`, and at `‖z‖ = δc` the derivative of `colMap β 1` at `z`
would see the arbitrary values of `β` below `δc²`.

Proof shape (both reviewers): with `z := sqDisk (foldBox u)` and `z₀ := ‖z‖⁻¹ • z`, `hcol` puts `u` in
the strict collar, so `colPlane β Q 1 u = Q z₀` and a `t ∈ [0,1]` with `e^{iπt} = ±z₀` (the sign is the
argument branch; the seam clause `hQseam` makes `coreLoop Q` `1`-periodic, and `2`-periodic as well, so
`d (coreLoop Q)` transfers between the branches); then `σ := (1 ∓ ‖z‖)/2 ∈ [0,1]` makes
`(1 - 2σ) e^{iπt} = z` *as points*, so `diskPlane Q u = diamLoop Q t σ`.  For `PolarDict`: near `u`,
`colPlane β Q 1 = Q ∘ (normalize ∘ sqDisk ∘ foldBox)`, the inner map lands on the unit circle, so its
derivative is a real multiple of `i e^{iπt}`; the kernel of `d(colPlane)` is therefore the kernel of the
inner map, whose elements are sent by `d (sqDisk ∘ foldBox)` into `span z`, and `dQ z` of those is in
`span (dQ z z) = range (mfderiv (diamLoop Q t) σ)` (because `d (diamLoop Q t) σ = -2 dQ z e^{iπt}` and
`z = (1-2σ) e^{iπt}`). -/
theorem collapse_polar_dictionary
    {β : ℝ → ℝ} {δc : ℝ} (hδc : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    {Q : ℂ → Work.Drive.CappingSpace} (hQsm : Work.Drive.IsSmoothChart Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {u : EuclideanSpace ℝ (Fin 2)} (hu0 : u 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hu1 : u 1 ∈ Set.Ioo (0 : ℝ) 1)
    (hcol : δc < ‖Work.Drive.sqDisk (Work.Drive.foldBox u)‖)
    (hcore : ∀ t : ℝ, Work.Drive.colCirclePt t
        = (‖Work.Drive.sqDisk (Work.Drive.foldBox u)‖⁻¹ : ℝ)
            • Work.Drive.sqDisk (Work.Drive.foldBox u) →
      Work.Drive.CoreImmersiveAt Q t) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) 1 ∧
      Work.Drive.colPlane β Q 1 u = Work.Drive.coreLoop Q t ∧
      Work.Drive.diskPlane Q u = Work.Drive.diamLoop Q t σ ∧
      Work.Drive.PolarDict β Q u t σ := by
  have hzle : ‖cdFoldDisk u‖ ≤ 1 := norm_sqDisk_le_one (foldBox u) (foldBox_mem_unitBox u)
  have hz : cdFoldDisk u ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hδc hcol)
  obtain ⟨τ, hτ, t, ht_mem, σ, hσ_mem, ht, hσt⟩ := exists_colParam hz hzle
  have hcoreτ : CoreImmersiveAt Q τ := hcore τ (by rw [hτ]; rfl)
  refine ⟨t, ht_mem, σ, hσ_mem, ?_, ?_, ?_⟩
  · have h1 : colPlane β Q 1 u = Q (polarNorm (cdFoldDisk u)) := by
      rw [colPlane_eq_cdFoldDisk, Function.comp_apply]
      exact colPlane_one_of_collar hδc hβδ Q u (le_of_lt hcol)
    rw [h1]
    rcases ht with rfl | rfl
    · rw [coreLoop_eq_col, hτ]
    · rw [coreLoop_add_one hQseam τ, coreLoop_eq_col, hτ]
  · rw [diskPlane_eq_cdFoldDisk, Function.comp_apply, diamLoop_eq', ← hσt]
  · exact polarDict_of_data hδc hβδ hQsm hQseam hcol hτ hcoreτ ht hσt

end Work.Drive
