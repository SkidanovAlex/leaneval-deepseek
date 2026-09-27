import Mathlib
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The model arc `w ↦ I √(η - I w)` of the saddle's anchor level: smoothness and immersion

The arc points of the saddle window (`Work.Drive.N2Lead.arcUpPt`, `arcDnPt`) are the two model arcs
of the anchor level `f = f p - lam0² η`.  The dichotomy of the saddle packet
(`Work.Drive.N2Lead.saddlePin_oneComp_or`) lifts those arcs to the components of the level through
`Work.Drive.N2C.arcLiftOfLevelCurves`, and that lift needs the arc *curve* `w ↦ arcZ η w` to be a
smooth immersion.  This file proves exactly that:

* `contDiff_arcZ` — `w ↦ arcZ η w = I √(η - I w)` is `C^∞` for `η > 0` (the argument of the square
  root stays in the open right half-plane, hence in the slit plane, where `Complex.sqrt` is
  complex-analytic);
* `deriv_arcZ_ne_zero` — its velocity never vanishes, because the identity
  `(arcZ η w)² = -η + I w` has non-zero derivative `I` (a vanishing velocity would give `0 = I`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

open Work.Drive.N2Lead (arcZ)

/-- `Complex.sqrt` is `C^∞` on the slit plane (it is complex-analytic there). -/
lemma contDiffOn_sqrt_slitPlane :
    ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.sqrt Complex.slitPlane :=
  Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane

/-- The argument `η - I w` of the model arc's square root lies in the slit plane when `η > 0`. -/
lemma mem_slitPlane_arcArg {η : ℝ} (hη : 0 < η) (w : ℝ) :
    ((η : ℂ) - (w : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simpa [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] using hη

/-- The affine map `w ↦ η - I w` is `C^∞`. -/
lemma contDiffAt_arcArg (η : ℝ) (w : ℝ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ((η : ℂ) - (u : ℂ) * Complex.I)) w := by
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ((u : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ((u : ℝ) : ℂ) * Complex.I) w :=
    h2.mul contDiffAt_const
  exact (contDiffAt_const (c := (η : ℂ))).sub h3

/-- **The model arc is smooth** (for `η > 0`). -/
lemma contDiff_arcZ {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => arcZ η w) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  have hsqrtC : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.sqrt
      ((η : ℂ) - (w : ℂ) * Complex.I) :=
    contDiffOn_sqrt_slitPlane.contDiffAt
      (Complex.isOpen_slitPlane.mem_nhds (mem_slitPlane_arcArg hη w))
  have hsqrtR : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.sqrt
      ((η : ℂ) - (w : ℂ) * Complex.I) := hsqrtC.restrict_scalars ℝ
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Complex.sqrt ((η : ℂ) - (u : ℂ) * Complex.I)) w := by
    simpa only [Function.comp_def] using hsqrtR.comp w (contDiffAt_arcArg η w)
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Complex.I * Complex.sqrt ((η : ℂ) - (u : ℂ) * Complex.I)) w :=
    contDiffAt_const.mul h1
  simpa [arcZ] using h2

/-- The velocity of the model arc. -/
lemma hasDerivAt_arcZ {η : ℝ} (hη : 0 < η) (w : ℝ) :
    HasDerivAt (fun u : ℝ => arcZ η u)
      (Complex.I * (((η : ℂ) - (w : ℂ) * Complex.I) ^ (-1 / 2 : ℂ) / 2 * (-Complex.I)))
      w := by
  have hmem : ((η : ℂ) - (w : ℂ) * Complex.I) ∈ Complex.slitPlane := mem_slitPlane_arcArg hη w
  have harg : HasDerivAt (fun u : ℝ => ((η : ℂ) - (u : ℂ) * Complex.I)) (-Complex.I) w := by
    have h2 : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ)) (1 : ℂ) w := by
      simpa using (hasDerivAt_id w).ofReal_comp
    have h3 : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ) * Complex.I) (Complex.I) w := by
      simpa using h2.mul_const Complex.I
    have h4 := h3.const_sub (η : ℂ)
    simpa using h4
  have hsqrt := (Complex.hasDerivAt_sqrt hmem).comp w harg
  have := hsqrt.const_mul Complex.I
  simpa [arcZ] using this

/-- **The model arc is an immersion**: its velocity never vanishes. -/
lemma deriv_arcZ_ne_zero {η : ℝ} (hη : 0 < η) (w : ℝ) :
    deriv (fun u : ℝ => arcZ η u) w ≠ 0 := by
  intro h0
  have hd : DifferentiableAt ℝ (fun u : ℝ => arcZ η u) w :=
    ((contDiff_arcZ hη).contDiffAt).differentiableAt (by simp)
  -- the derivative of the square
  have h1 : deriv (fun u : ℝ => (arcZ η u) ^ 2) w
      = 2 * arcZ η w * deriv (fun u : ℝ => arcZ η u) w := by
    rw [show (fun u : ℝ => (arcZ η u) ^ 2)
        = ((fun u : ℝ => arcZ η u) * fun u : ℝ => arcZ η u) from by
      funext u; rw [Pi.mul_apply]; ring]
    rw [deriv_mul hd hd]
    ring
  -- the square is the affine map `u ↦ -η + I u`, whose derivative is `I`
  have h2 : deriv (fun u : ℝ => (arcZ η u) ^ 2) w = Complex.I := by
    have hfun : (fun u : ℝ => (arcZ η u) ^ 2)
        = (fun u : ℝ => (-(η : ℂ)) + ((u : ℝ) : ℂ) * Complex.I) := by
      funext u
      rw [Work.Drive.N2Lead.arcZ_sq]
    rw [hfun]
    have h3 : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ)) (1 : ℂ) w := by
      simpa using (hasDerivAt_id w).ofReal_comp
    have h4 : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ) * Complex.I) (Complex.I) w := by
      simpa using h3.mul_const Complex.I
    have h5 := h4.const_add (-(η : ℂ))
    simpa using h5.deriv
  rw [h2] at h1
  rw [h0, mul_zero] at h1
  exact Complex.I_ne_zero h1

/-! ## The arc curves in `M` -/

/-- The planar inclusion `ℂ → ℝ²` as a continuous linear map. -/
noncomputable def cE2L : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      if i = 0 then Complex.reCLM else Complex.imCLM))

lemma cE2L_apply (z : ℂ) : cE2L z = Work.Drive.N2Lead.cE2 z := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> simp [cE2L, Work.Drive.N2Lead.cE2]

/-- The chart curve of an arc point is `C^∞`. -/
lemma contDiff_chartArc {η lam0 : ℝ} (hη : 0 < η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℝ => Work.Drive.N2Lead.cE2 ((lam0 : ℂ) * arcZ η w)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => (lam0 : ℂ) * arcZ η w) :=
    contDiff_const.mul (contDiff_arcZ hη)
  have h2 := cE2L.contDiff.comp h1
  simpa [Function.comp_def, cE2L_apply] using h2

/-- The model arc point stays in the chart's ball as long as `|w| ≤ 3` (and `|η| ≤ 1`). -/
lemma norm_arcZ_lt_eight {η w : ℝ} (hη : |η| ≤ 1) (hw : |w| ≤ 3) : ‖arcZ η w‖ < 8 := by
  have h1 : ‖arcZ η w‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq, Work.Drive.N2Lead.normSq_arcZ]
  have h2 : η ^ 2 + w ^ 2 ≤ 10 := by
    nlinarith [abs_le.mp hη, abs_le.mp hw]
  have h3 : Real.sqrt (η ^ 2 + w ^ 2) ≤ 4 := by
    have h4 : Real.sqrt (η ^ 2 + w ^ 2) ≤ Real.sqrt ((4 : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [h2])
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (4 : ℝ))] at h4
  nlinarith [norm_nonneg (arcZ η w), h1]

/-- **The upper arc of the anchor level is a `C^∞` curve in `M`** on `Ioo (-3) 3`. -/
lemma contMDiffOn_arcUpPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {lam0 η : ℝ} (hη : 0 < η) (hη1 : |η| ≤ 1) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8) :
    ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℝ => Work.Drive.N2Lead.arcUpPt D lam0 η w) (Ioo (-3) 3) := by
  have hmap : ∀ w ∈ Ioo (-3) 3,
      Work.Drive.N2Lead.cE2 ((lam0 : ℂ) * arcZ η w) ∈ (D.φ D.j).target := by
    intro w hw
    exact Work.Drive.N2Lead.cE2_mul_mem_target D
      (norm_arcZ_lt_eight hη1 (le_of_lt (abs_lt.mpr ⟨by linarith [hw.1],
        by linarith [hw.2]⟩))) hlam0
  have hcomp := (show ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (D.φ D.j).symm z) (D.φ D.j).target from D.hφ' D.j).comp
    (contDiff_chartArc (η := η) (lam0 := lam0) hη).contDiffOn.contMDiffOn hmap
  simpa [Work.Drive.N2Lead.arcUpPt, Function.comp_def] using hcomp

/-- The same for the lower arc. -/
lemma contMDiffOn_arcDnPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {lam0 η : ℝ} (hη : 0 < η) (hη1 : |η| ≤ 1) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8) :
    ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℝ => Work.Drive.N2Lead.arcDnPt D lam0 η w) (Ioo (-3) 3) := by
  have hcur : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℝ => Work.Drive.N2Lead.cE2 (-((lam0 : ℂ) * arcZ η w))) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : ℝ => -((lam0 : ℂ) * arcZ η w)) :=
      (contDiff_const.mul (contDiff_arcZ hη)).neg
    have h2 := cE2L.contDiff.comp h1
    simpa [Function.comp_def, cE2L_apply] using h2
  have hmap : ∀ w ∈ Ioo (-3) 3,
      Work.Drive.N2Lead.cE2 (-((lam0 : ℂ) * arcZ η w)) ∈ (D.φ D.j).target := by
    intro w hw
    have hball : ‖arcZ η w‖ < 8 :=
      norm_arcZ_lt_eight hη1 (le_of_lt (abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩))
    refine Work.Drive.N2.windowBall_subset_target D D.j ?_
    rw [show -((lam0 : ℂ) * arcZ η w) = (lam0 : ℂ) * (-(arcZ η w)) by ring,
      Work.Drive.N2Lead.cE2_norm, norm_mul, Complex.norm_of_nonneg hlam0pos.le, hlam0, norm_neg]
    nlinarith [hball, D.hρ D.j]
  have hcomp := (show ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (D.φ D.j).symm z) (D.φ D.j).target from D.hφ' D.j).comp
    hcur.contDiffOn.contMDiffOn hmap
  simpa [Work.Drive.N2Lead.arcDnPt, Function.comp_def] using hcomp


/-- **The upper arc curve in `M` is an immersion.**  The chain rule with the chart coordinate `Z`
reduces it to the immersion of the model arc `w ↦ arcZ η w`: on the arc, `Z` is `arcZ η w`, whose
velocity is non-zero. -/
lemma mfderiv_arcUpPt_ne_zero {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 η : ℝ} (hη : 0 < η) (hη1 : |η| ≤ 1) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, Work.Drive.N2Lead.chartCplx D x = (lam0 : ℂ) * Z x)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ,ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    {w : ℝ} (hw : w ∈ Ioo (-3) 3) :
    mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun u : ℝ => Work.Drive.N2Lead.arcUpPt D lam0 η u) w 1 ≠ 0 := by
  have hb : ∀ u ∈ Ioo (-3) 3, ‖arcZ η u‖ < 8 := fun u hu =>
    norm_arcZ_lt_eight hη1 (le_of_lt (abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩))
  have hZev : (Z ∘ fun u : ℝ => Work.Drive.N2Lead.arcUpPt D lam0 η u)
      =ᶠ[𝓝 w] (fun u : ℝ => arcZ η u) := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with u hu
    exact Work.Drive.N2Lead.Z_arcUpPt D (hb u hu) hlam0pos hlam0 hZrel
  have hαd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2)
      (fun u : ℝ => Work.Drive.N2Lead.arcUpPt D lam0 η u) w :=
    ((contMDiffOn_arcUpPt D hη hη1 hlam0pos hlam0).contMDiffAt
      (Ioo_mem_nhds hw.1 hw.2)).mdifferentiableAt (by simp)
  have hZd : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) Z (Work.Drive.N2Lead.arcUpPt D lam0 η w) :=
    (hZsm _ (Work.Drive.N2Lead.arcUpPt_mem_source D (hb w hw) hlam0)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℂ)) w
    (f := fun u : ℝ => Work.Drive.N2Lead.arcUpPt D lam0 η u) (g := Z) hZd hαd (1 : ℝ)
  intro h0
  have hchain0 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ)
      (Z ∘ fun u : ℝ => Work.Drive.N2Lead.arcUpPt D lam0 η u) w (1 : ℝ) = 0 := by
    rw [hchain]
    exact (congrArg (fun z => (mfderiv (𝓡 2) 𝓘(ℝ,ℂ) Z
      (Work.Drive.N2Lead.arcUpPt D lam0 η w)) z) h0).trans (map_zero _)
  have h2 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) (fun u : ℝ => arcZ η u) w 1 = 0 := by
    rw [← hZev.mfderiv_eq_v433]
    exact hchain0
  rw [mfderiv_eq_fderiv] at h2
  exact deriv_arcZ_ne_zero hη w h2

/-- The lower arc point's chart coordinate. -/
lemma Z_arcDnPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 η w : ℝ} (hball : ‖arcZ η w‖ < 8) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, Work.Drive.N2Lead.chartCplx D x = (lam0 : ℂ) * Z x) :
    Z (Work.Drive.N2Lead.arcDnPt D lam0 η w) = -arcZ η w := by
  have hmem : Work.Drive.N2Lead.cE2 (-((lam0 : ℂ) * arcZ η w)) ∈ (D.φ D.j).target := by
    refine Work.Drive.N2.windowBall_subset_target D D.j ?_
    rw [show -((lam0 : ℂ) * arcZ η w) = (lam0 : ℂ) * (-(arcZ η w)) by ring,
      Work.Drive.N2Lead.cE2_norm, norm_mul, Complex.norm_of_nonneg hlam0pos.le, hlam0, norm_neg]
    nlinarith [hball, D.hρ D.j]
  have h : Work.Drive.N2Lead.chartCplx D
      ((D.φ D.j).symm (Work.Drive.N2Lead.cE2 (-((lam0 : ℂ) * arcZ η w))))
      = (lam0 : ℂ) * Z (Work.Drive.N2Lead.arcDnPt D lam0 η w) :=
    hZrel (Work.Drive.N2Lead.arcDnPt D lam0 η w)
  rw [Work.Drive.N2Lead.chartCplx, (D.φ D.j).right_inv hmem,
    Work.Drive.N2Lead.cplxE2_cE2] at h
  rw [show -((lam0 : ℂ) * arcZ η w) = (lam0 : ℂ) * (-arcZ η w) by ring] at h
  have hne : (lam0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0pos)
  exact (mul_left_cancel₀ hne h).symm

/-- **The lower arc curve in `M` is an immersion.** -/
lemma mfderiv_arcDnPt_ne_zero {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 η : ℝ} (hη : 0 < η) (hη1 : |η| ≤ 1) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, Work.Drive.N2Lead.chartCplx D x = (lam0 : ℂ) * Z x)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ,ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    {w : ℝ} (hw : w ∈ Ioo (-3) 3) :
    mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun u : ℝ => Work.Drive.N2Lead.arcDnPt D lam0 η u) w 1 ≠ 0 := by
  have hb : ∀ u ∈ Ioo (-3) 3, ‖arcZ η u‖ < 8 := fun u hu =>
    norm_arcZ_lt_eight hη1 (le_of_lt (abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩))
  have hZev : (Z ∘ fun u : ℝ => Work.Drive.N2Lead.arcDnPt D lam0 η u)
      =ᶠ[𝓝 w] (fun u : ℝ => -arcZ η u) := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with u hu
    exact Z_arcDnPt D (hb u hu) hlam0pos hlam0 hZrel
  have hsrc : Work.Drive.N2Lead.arcDnPt D lam0 η w ∈ (D.φ D.j).source :=
    (D.φ D.j).map_target (by
      refine Work.Drive.N2.windowBall_subset_target D D.j ?_
      rw [show -((lam0 : ℂ) * arcZ η w) = (lam0 : ℂ) * (-(arcZ η w)) by ring,
        Work.Drive.N2Lead.cE2_norm, norm_mul, Complex.norm_of_nonneg hlam0pos.le, hlam0,
        norm_neg]
      nlinarith [hb w hw, D.hρ D.j])
  have hαd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2)
      (fun u : ℝ => Work.Drive.N2Lead.arcDnPt D lam0 η u) w :=
    ((contMDiffOn_arcDnPt D hη hη1 hlam0pos hlam0).contMDiffAt
      (Ioo_mem_nhds hw.1 hw.2)).mdifferentiableAt (by simp)
  have hZd : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) Z (Work.Drive.N2Lead.arcDnPt D lam0 η w) :=
    (hZsm _ hsrc).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℂ)) w
    (f := fun u : ℝ => Work.Drive.N2Lead.arcDnPt D lam0 η u) (g := Z) hZd hαd (1 : ℝ)
  intro h0
  have hchain0 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ)
      (Z ∘ fun u : ℝ => Work.Drive.N2Lead.arcDnPt D lam0 η u) w (1 : ℝ) = 0 := by
    rw [hchain]
    exact (congrArg (fun z => (mfderiv (𝓡 2) 𝓘(ℝ,ℂ) Z
      (Work.Drive.N2Lead.arcDnPt D lam0 η w)) z) h0).trans (map_zero _)
  have h2 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) (fun u : ℝ => -arcZ η u) w 1 = 0 := by
    rw [← hZev.mfderiv_eq_v433]
    exact hchain0
  rw [mfderiv_eq_fderiv] at h2
  have h2' : deriv (fun u : ℝ => -arcZ η u) w = 0 := h2
  have hd : HasDerivAt (fun u : ℝ => -arcZ η u) (-(deriv (fun u : ℝ => arcZ η u) w)) w :=
    ((((contDiff_arcZ hη).contDiffAt).differentiableAt (by simp)).hasDerivAt).neg
  rw [hd.deriv] at h2'
  exact deriv_arcZ_ne_zero hη w (neg_eq_zero.mp h2')

end Work.Drive.N2C
