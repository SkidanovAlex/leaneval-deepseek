import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.signedArea_scale_shift
import Submission.Work.RPB.B5.ktarg_signedArea

/-!
# B5: elementary facts about the `κ`-parametrised collar

This module collects the *elementary* (purely algebraic / cutoff) facts about the objects of
`Submission/Work/RPB/B5/kappaDefs.lean` that are needed both by the assembly file
`Submission/Work/RPB/B5/collar_exists_kappa.lean` and by the sibling lemmas about it:

* the values of the cutoffs `kblf`, `krpf`, `kphc`, `kbbmp` at the thresholds;
* `krpf δ σ ∈ [0,1]` (so the far family is a genuine rescaled curve of the isotopy);
* the real-linear map `kdiagM`: `kdiagM 1 = id`, injectivity for `g ≠ 0`, and the chain rule
  `deriv (kdiagM g ∘ c) = kdiagM g ∘ deriv c` at differentiability points;
* the radius `krd σ = √(2+2σ)`: square and positivity;
* the glued shape `kshape`: it is `kfsh` for `σ ≥ δ`, it is exactly the target circle `ktarg` for
  `σ ≥ 2δ` and on the `τ = 0` slice;
* the signed area `karS` and the normalisation constants `kg`, `kgam` on the far region
  `σ ≥ δ`: `karS = 2π(1+σ)`, `kg = 1`, `kgam = kshape`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## The cutoffs at their thresholds -/

theorem ksb_kblf_one {δ σ : ℝ} (hδ : 0 < δ) (h : δ ≤ σ) : kblf δ σ = 1 := by
  unfold kblf
  apply kstp_one
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < δ / 2)]
  linarith

theorem ksb_kblf_zero {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ δ / 2) : kblf δ σ = 0 := by
  unfold kblf
  apply kstp_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

theorem ksb_krpf_one {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ δ) : krpf δ σ = 1 := by
  unfold krpf
  rw [kstp_zero (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith)]
  ring

theorem ksb_krpf_zero {δ σ : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ σ) : krpf δ σ = 0 := by
  unfold krpf
  rw [kstp_one (by rw [le_div_iff₀ hδ]; linarith)]
  ring

theorem ksb_kphc_zero {δ : ℝ} (k : ℤ) {σ : ℝ} (hδ : 0 < δ) (h : σ ≤ δ) : kphc δ k σ = 0 := by
  unfold kphc
  rw [kstp_zero (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith)]
  ring

theorem ksb_kphc_far {δ : ℝ} (k : ℤ) {σ : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ σ) :
    kphc δ k σ = -(Real.pi / 2 + 2 * Real.pi * k) := by
  unfold kphc
  rw [kstp_one (by rw [le_div_iff₀ hδ]; linarith)]
  ring

theorem ksb_kbbmp_zero (δ : ℝ) : kbbmp δ 0 = 1 := by
  unfold kbbmp
  rw [zero_div, kstp_zero (le_refl 0), sub_zero]

theorem ksb_krpf_nonneg (δ σ : ℝ) : 0 ≤ krpf δ σ := by
  unfold krpf
  linarith [kstp_le_one ((σ - δ) / δ)]

theorem ksb_krpf_le_one (δ σ : ℝ) : krpf δ σ ≤ 1 := by
  unfold krpf
  linarith [kstp_nonneg ((σ - δ) / δ)]

theorem ksb_krpf_mem_Icc (δ σ : ℝ) : krpf δ σ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ksb_krpf_nonneg δ σ, ksb_krpf_le_one δ σ⟩

theorem ksb_krpf_mul_mem_Icc {δ σ τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    krpf δ σ * τ ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := ksb_krpf_mem_Icc δ σ
  exact ⟨mul_nonneg h0 hτ.1, mul_le_one₀ h1 hτ.1 hτ.2⟩

/-! ## The radius `krd` -/

theorem ksb_krd_sq (σ : ℝ) (hσ : 0 ≤ 2 + 2 * σ) : krd σ ^ 2 = 2 + 2 * σ := by
  unfold krd
  rw [Real.sq_sqrt hσ]

theorem ksb_krd_pos (σ : ℝ) (hσ : 0 < 2 + 2 * σ) : 0 < krd σ := by
  unfold krd
  exact Real.sqrt_pos.mpr hσ

theorem ksb_krd_ne_zero (σ : ℝ) (hσ : 0 < 2 + 2 * σ) : krd σ ≠ 0 := ne_of_gt (ksb_krd_pos σ hσ)

/-! ## The real-linear normalisation `kdiagM` -/

theorem ksb_kdiagM_one (z : ℂ) : kdiagM 1 z = z := by
  unfold kdiagM
  rw [one_mul, Complex.re_add_im]

theorem ksb_kdiagM_re (g : ℝ) (z : ℂ) : (kdiagM g z).re = z.re := by
  simp [kdiagM]

theorem ksb_kdiagM_im (g : ℝ) (z : ℂ) : (kdiagM g z).im = g * z.im := by
  simp [kdiagM]

theorem ksb_kdiagM_inj {g : ℝ} (hg : g ≠ 0) {z w : ℂ} (h : kdiagM g z = kdiagM g w) : z = w := by
  apply Complex.ext
  · have := congrArg Complex.re h
    simpa [ksb_kdiagM_re] using this
  · have := congrArg Complex.im h
    simp only [ksb_kdiagM_im] at this
    exact mul_left_cancel₀ hg this

/-- `kdiagM g` as a continuous `ℝ`-linear map. -/
def ksb_kdiagM_clm (g : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (1 : ℂ) + g • Complex.imCLM.smulRight Complex.I

theorem ksb_kdiagM_clm_apply (g : ℝ) (z : ℂ) : ksb_kdiagM_clm g z = kdiagM g z := by
  rw [kdiagM]
  simp only [ksb_kdiagM_clm, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul]
  rw [Complex.ofReal_mul]
  ring

/-- **Chain rule for `kdiagM g`.**  At a differentiability point, `kdiagM g` may be pulled out of
`deriv` — for *every* `g`, including `g = 0`. -/
theorem ksb_deriv_kdiagM_comp (g : ℝ) (c : ℝ → ℂ) {t : ℝ} (hc : DifferentiableAt ℝ c t) :
    deriv (fun u => kdiagM g (c u)) t = kdiagM g (deriv c t) := by
  have hfun : (fun u => kdiagM g (c u)) = fun u => ksb_kdiagM_clm g (c u) := by
    funext u
    rw [ksb_kdiagM_clm_apply]
  rw [hfun]
  have h3 : HasFDerivAt (fun u => ksb_kdiagM_clm g (c u)) ((ksb_kdiagM_clm g).comp (fderiv ℝ c t)) t :=
    (ksb_kdiagM_clm g).hasFDerivAt.comp t hc.hasFDerivAt
  rw [h3.hasDerivAt.deriv, ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv,
    ksb_kdiagM_clm_apply]

/-! ## The glued shape at the corners -/

/-- At `τ = 0` the glued shape is exactly the target circle. -/
theorem ksb_kshape_zero_slice (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) {σ t : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) :
    kshape CI W ρh δ k 0 σ t = ktarg δ k σ t := by
  have h1 : knear CI W ρh δ k 0 σ t = ktarg δ k σ t := by
    have hb : kbbmp δ 0 = 1 := ksb_kbbmp_zero δ
    have hx : xfade δ σ = 1 := xfade_one hδ hσ
    unfold knear
    rw [hb, hx]
    push_cast
    ring
  have h2 : kfsh CI δ k 0 σ t = ktarg δ k σ t := by
    unfold kfsh ktarg
    rw [mul_zero, CI.start]
    congr 1
    congr 1
    push_cast
    ring
  unfold kshape
  rw [h1, h2]
  ring

/-- For `σ ≥ δ` the glued shape is exactly the far family. -/
theorem ksb_kshape_eq_kfsh (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ σ : ℝ} (hδ : 0 < δ) (h : δ ≤ σ) (k : ℤ) (τ t : ℝ) :
    kshape CI W ρh δ k τ σ t = kfsh CI δ k τ σ t := by
  have hb : kblf δ σ = 1 := ksb_kblf_one hδ h
  unfold kshape
  rw [hb]
  simp

/-- For `σ ≥ 2δ` the glued shape is exactly the collar's far circle. -/
theorem ksb_kshape_far (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) {τ σ t : ℝ} (hδ : 0 < δ) (hσ : 2 * δ ≤ σ) :
    kshape CI W ρh δ k τ σ t
      = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I) := by
  have hb : kblf δ σ = 1 := ksb_kblf_one hδ (by linarith)
  have hf : kfsh CI δ k τ σ t = (krd σ : ℂ) * CI.c 0 (t + kphc δ k σ) := by
    unfold kfsh
    rw [ksb_krpf_zero hδ hσ, zero_mul]
  have hexp : Complex.exp ((t + kphc δ k σ : ℝ) * Complex.I)
      = Complex.exp ((t - Real.pi / 2 : ℝ) * Complex.I) := by
    rw [ksb_kphc_far k hδ hσ]
    have h2 : ((t + (-(Real.pi / 2 + 2 * Real.pi * k)) : ℝ) : ℂ) * Complex.I
        = ((t - Real.pi / 2 : ℝ) : ℂ) * Complex.I
          + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  unfold kshape
  rw [hb, hf, CI.start, hexp]
  simp only [krd]
  push_cast
  ring

/-! ## The signed area and the normalisation on the far region -/

/-- The far family is a rescaled, phase-shifted curve of the isotopy. -/
theorem ksb_kfsh_apply (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (τ σ t : ℝ) :
    kfsh CI δ k τ σ t = (krd σ : ℂ) * CI.c (krpf δ σ * τ) (t + kphc δ k σ) := rfl

/-- The signed area of the far family is `2π(1+σ)`. -/
theorem ksb_kfsh_signedArea (CI : Work.RPV.CurveIsotopy) {δ σ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : δ ≤ σ) :
    Work.RPB.signedArea (fun t => kfsh CI δ k τ σ t) = 2 * Real.pi * (1 + σ) := by
  have hfun : (fun t => kfsh CI δ k τ σ t)
      = fun t => (krd σ : ℂ) * CI.c (krpf δ σ * τ) (t + kphc δ k σ) :=
    funext (fun t => ksb_kfsh_apply CI δ k τ σ t)
  rw [hfun, signedArea_scale_shift CI (krpf δ σ * τ) (krd σ) (kphc δ k σ)
    (ksb_krpf_mul_mem_Icc hτ)]
  rw [ksb_krd_sq σ (by linarith)]
  ring

/-- On the far region `σ ≥ δ` the signed area of the glued shape is `2π(1+σ)`. -/
theorem ksb_karS_far (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ σ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : δ ≤ σ) :
    karS CI W ρh δ k τ σ = 2 * Real.pi * (1 + σ) := by
  have hshape : (fun t => kshape CI W ρh δ k τ σ t) = fun t => kfsh CI δ k τ σ t :=
    funext (fun t => ksb_kshape_eq_kfsh CI W ρh hδ hσ k τ t)
  rw [karS, hshape, ksb_kfsh_signedArea CI hδ k hτ hσ]

/-- On the far region `σ ≥ δ` the normalisation factor is `1`. -/
theorem ksb_kg_far (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ σ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : δ ≤ σ) :
    kg CI W ρh δ k τ σ = 1 := by
  have hne : 2 * Real.pi * (1 + σ) ≠ 0 := by
    have h1 : (0 : ℝ) < 1 + σ := by linarith
    positivity
  rw [kg, ksb_karS_far CI W ρh hδ k hτ hσ, div_self hne]

/-- On the far region `σ ≥ δ` the collar is the glued shape itself. -/
theorem ksb_kgam_far (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ σ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : δ ≤ σ) (t : ℝ) :
    kgam CI W ρh δ k τ σ t = kshape CI W ρh δ k τ σ t := by
  rw [kgam, ksb_kg_far CI W ρh hδ k hτ hσ, ksb_kdiagM_one]

theorem ksb_kgam_apply (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (τ σ t : ℝ) :
    kgam CI W ρh δ k τ σ t = kdiagM (kg CI W ρh δ k τ σ) (kshape CI W ρh δ k τ σ t) := rfl

theorem ksb_kac_apply (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (τ σ t : ℝ) :
    kac CI W ρh δ k τ σ t = kA0 W ρh δ k τ σ +
      ∫ u in (0 : ℝ)..t,
        Work.RPV.ωC (deriv (fun s => kgam CI W ρh δ k τ s u) σ)
          (deriv (fun s => kgam CI W ρh δ k τ σ s) u) := rfl

end Work.RPB.B5
