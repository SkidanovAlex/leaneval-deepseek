/-
# Auxiliary lemmas for the left-detour residue computation

The target lemma `Work.Asymptotics.detourLeftC_eq_interval_sub_residue` evaluates the left detour
of the CKMRV contour against the axis interval by Cauchy's theorem for the rectangle
`[-ξ,0] × [c-A,c+A]`, whose only singular point is the simple pole `z = τ-1` of
`z ↦ K^{(d)}(τ,z)e^{iπr²z}/i`.

This module collects the pieces:

* the conversion between the real parametrisations `edgeH`, `edgeV` of
  `Work.Asymptotics.contourLeftDefs` and the complex-variable integrand
  `Work.Asymptotics.kerForm` (the `edgeH` direction is `Work.Asymptotics.kerForm_edgeH`);
* the identification of the (set) integrals of the detour with the (oriented interval) integrals
  of the residue theorem;
* the derivation of the `j`-cleanness of the closed rectangle from the hypothesis that the only
  point of the orbit of `τ` there is `τ - 1`;
* continuity and holomorphy of `kerForm` on the rectangle off the pole, and the residue limit
  `(z - (τ-1))·kerForm → e^{iπr²(τ-1)}/(2πi)` at the pole.
-/
import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.kerFormDefs
import Submission.Work.Asymptotics.kerForm_edgeH
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Residues.ResidueSecondVariable

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.Asymptotics

/-! ## The edge integrands as complex-variable integrals -/

/-- `edgeV` is `i` times the complex-variable integrand `kerForm`. -/
theorem dlc_edgeV_eq_kerForm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    (τ : UpperHalfPlane) (u v : ℝ) (hv : 0 < v) :
    edgeV ℓ d r τ u v
      = Complex.I * kerForm ℓ d r τ ((u : ℂ) + (v : ℂ) * Complex.I) := by
  rw [edgeV, kerForm, ofReImT_eq_ofComplex u v hv, kerExp_eq_phaseWeight_mul_gaussWeight]
  field_simp

/-- **The horizontal edges of the left detour as oriented interval integrals.** -/
theorem dlc_integral_edgeH_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    (τ : UpperHalfPlane) (ξ v : ℝ) (hξ : 0 < ξ) (hv : 0 < v) :
    (∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) v)
      = ∫ x : ℝ in (-ξ)..0, kerForm ℓ d r τ ((x : ℂ) + (v : ℂ) * Complex.I) := by
  have hL : (∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) v)
      = ∫ u : ℝ in (0 : ℝ)..ξ, edgeH ℓ d r τ (-u) v := by
    rw [intervalIntegral.integral_of_le hξ.le]
    exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  rw [hL]
  have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := ξ)
      (f := fun x : ℝ => kerForm ℓ d r τ ((x : ℂ) + (v : ℂ) * Complex.I))
  rw [neg_zero] at hneg
  rw [← hneg]
  exact intervalIntegral.integral_congr fun u _ => kerForm_edgeH ℓ d r τ (-u) v hv

/-- **The vertical edge of the left detour as an oriented interval integral.** -/
theorem dlc_integral_edgeV (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    (τ : UpperHalfPlane) (x y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy : y₁ < y₂) :
    (∫ v in Set.Ioo y₁ y₂, edgeV ℓ d r τ x v)
      = Complex.I * ∫ v : ℝ in y₁..y₂,
          kerForm ℓ d r τ ((x : ℂ) + (v : ℂ) * Complex.I) := by
  have hL : (∫ v in Set.Ioo y₁ y₂, edgeV ℓ d r τ x v)
      = ∫ v : ℝ in y₁..y₂, edgeV ℓ d r τ x v := by
    rw [intervalIntegral.integral_of_le hy.le,
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
  rw [hL, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v hv' => ?_
  have hv0 : 0 < v := by
    have h : v ∈ Set.Icc y₁ y₂ := by rwa [Set.uIcc_of_le hy.le] at hv'
    linarith [h.1, hy₁]
  exact dlc_edgeV_eq_kerForm ℓ d r τ x v hv0

/-! ## Cleanness of the closed rectangle -/

/-- **The closed left rectangle is `j`-clean except at the pole.**  If the only point of the
`SL(2,ℤ)`-orbit of `τ` in the closed rectangle `[-ξ,0] × [c-A,c+A]` is `τ - 1`, then no other
point `z` of the rectangle has `j (ofComplex z) = j τ`. -/
theorem dlc_clean (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hcl : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect c A ξ z → (z ≠ γ • τ ∨ z = tauSubOne τ)) :
    ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ poleℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := by
  intro z hz hzp hjeq
  have hzim : 0 < z.im := leftRectℂ_subset_im_pos hcA hz
  have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzim, UpperHalfPlane.coe_mk]
  have hre : (UpperHalfPlane.ofComplex z).re = z.re := by
    rw [← UpperHalfPlane.coe_re, hcoe]
  have him : (UpperHalfPlane.ofComplex z).im = z.im := by
    rw [← UpperHalfPlane.coe_im, hcoe]
  have hleft : leftRect c A ξ (UpperHalfPlane.ofComplex z) := by
    simp only [leftRect, leftRectℂ, Set.mem_ofPred_eq] at hz ⊢
    rw [hre, him]
    exact hz
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq
    (τ := UpperHalfPlane.ofComplex z) (w := τ) hjeq.symm
  rcases hcl γ (UpperHalfPlane.ofComplex z) hleft with h' | h'
  · exact h' hγ.symm
  · exact hzp (by rw [poleℂ, ← h', hcoe])

/-! ## Openness of the open rectangle -/

lemma isOpen_openLeftRectℂ (c A ξ : ℝ) : IsOpen (openLeftRectℂ c A ξ) := by
  have h : openLeftRectℂ c A ξ = Set.Ioo (-ξ) 0 ×ℂ Set.Ioo (c - A) (c + A) := by
    ext z
    simp only [openLeftRectℂ, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_ofPred_eq]
    tauto
  rw [h]
  exact isOpen_Ioo.reProdIm isOpen_Ioo

/-! ## Continuity of the integrand on the punctured closed rectangle -/

/-- **`kerForm` is continuous on the closed rectangle minus the pole.** -/
theorem dlc_continuousOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ poleℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ \ {poleℂ τ}) := by
  have hsub : (leftRectℂ c A ξ \ {poleℂ τ}) ⊆ {z : ℂ | 0 < z.im} :=
    fun z hz => leftRectℂ_subset_im_pos hcA hz.1
  have hof : ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z)
      (leftRectℂ c A ξ \ {poleℂ τ}) :=
    continuousOn_ofComplex_of_im_pos.mono hsub
  have hgc : ContinuousOn (fun z : ℂ => (τ, UpperHalfPlane.ofComplex z))
      (leftRectℂ c A ξ \ {poleℂ τ}) :=
    ContinuousOn.prodMk (f := fun _ : ℂ => τ) (g := fun z : ℂ => UpperHalfPlane.ofComplex z)
      continuousOn_const hof
  have hK := (continuousOn_Kfun_clean ℓ d hd).comp hgc (fun z hz => by
    have h := hclean z hz.1 (by simpa using hz.2)
    simpa using h)
  have hexp : ContinuousOn (fun z : ℂ => kerExp r z) (leftRectℂ c A ξ \ {poleℂ τ}) := by
    have hcont : Continuous fun z : ℂ => kerExp r z := by
      unfold kerExp; fun_prop
    exact hcont.continuousOn
  have hmain := (hK.mul hexp).div_const Complex.I
  refine hmain.congr (fun z hz => ?_)
  simp [kerForm, Function.comp]

/-! ## Holomorphy of the integrand on the punctured open rectangle -/

/-- **`kerForm` is holomorphic on the open rectangle off the pole.** -/
theorem dlc_differentiableAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ poleℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    ∀ z : ℂ, z ∈ openLeftRectℂ c A ξ → z ≠ poleℂ τ →
      DifferentiableAt ℂ (kerForm ℓ d r τ) z := by
  intro z hz hzp
  have hleft : z ∈ leftRectℂ c A ξ := openLeftRectℂ_subset_leftRectℂ c A ξ hz
  have hzim : 0 < z.im := leftRectℂ_subset_im_pos hcA hleft
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim
  have hne : Work.Kernels.jInvariantFun τ
      ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := hclean z hleft hzp
  have hA : DifferentiableAt ℂ
      (fun w : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) z := by
    have hhol : DifferentiableOn ℂ
        (fun w : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) {w : ℂ | 0 < w.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff
        (f := fun w : UpperHalfPlane => AfunFun ℓ d τ w)).mp
        (mdifferentiable_AfunFun_snd ℓ d hd τ)
      simpa [Function.comp_def] using h
    exact hhol.differentiableAt hU
  have hJ : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) z := by
    have hhol : DifferentiableOn ℂ
        (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
        {w : ℂ | 0 < w.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff
        (f := Work.Kernels.jInvariantFun)).mp mdifferentiable_jInvariantFun
      simpa [Function.comp_def] using h
    exact hhol.differentiableAt hU
  have hexp : DifferentiableAt ℂ (fun w : ℂ => kerExp r w) z := by
    simp only [kerExp]
    fun_prop
  have hΦ : DifferentiableAt ℂ (fun w : ℂ =>
      AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)
        / (Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
        * kerExp r w / Complex.I) z :=
    (((hA.div ((differentiableAt_const (c := Work.Kernels.jInvariantFun τ)).sub hJ)
      (sub_ne_zero.mpr hne)).mul hexp)).div_const Complex.I
  refine (Filter.EventuallyEq.differentiableAt_iff ?_).mpr hΦ
  have hmem : openLeftRectℂ c A ξ \ {poleℂ τ} ∈ 𝓝 z :=
    ((isOpen_openLeftRectℂ c A ξ).inter isOpen_compl_singleton).mem_nhds ⟨hz, hzp⟩
  filter_upwards [hmem] with w hw
  have hwl : w ∈ leftRectℂ c A ξ := openLeftRectℂ_subset_leftRectℂ c A ξ hw.1
  have hwne : Work.Kernels.jInvariantFun τ
      ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w) := hclean w hwl hw.2
  simp only [kerForm]
  rw [show Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w)
      = AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)
        / (Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) by
    rw [eq_div_iff (sub_ne_zero.mpr hwne)]
    exact Kfun_mul_slope_eq_AfunFun ℓ d hd τ (UpperHalfPlane.ofComplex w) hwne]

/-! ## The residue limit of the integrand -/

/-- **The residue limit of the contour integrand at the pole `z = τ - 1`.** -/
theorem dlc_tendsto_residue (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (hdeg : Work.Residues.jprime (tauSubOne τ) ≠ 0) :
    Filter.Tendsto (fun z : ℂ => (z - poleℂ τ) * kerForm ℓ d r τ z)
      (nhdsWithin (poleℂ τ) {poleℂ τ}ᶜ)
      (nhds (kerExp r (poleℂ τ) / (2 * (Real.pi : ℂ) * Complex.I))) := by
  have hne : Work.Residues.jprime τ ≠ 0 := by
    rw [← Work.Residues.jprime_vadd_neg_one τ]
    exact hdeg
  have hres := Work.Residues.hasResidue_Kfun_second' ℓ d hd τ hne
  have hz0im : 0 < (poleℂ τ).im := by
    have h : (poleℂ τ).im = τ.im := by
      rw [poleℂ, UpperHalfPlane.coe_im]
      exact UpperHalfPlane.vadd_im (-1) τ
    rw [h]
    exact τ.im_pos
  have hUmem : {z : ℂ | 0 < z.im} ∈ nhdsWithin (poleℂ τ) {poleℂ τ}ᶜ :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz0im)
  have hcont : ContinuousAt (fun z : ℂ => UpperHalfPlane.ofComplex z) (poleℂ τ) :=
    continuousOn_ofComplex_of_im_pos.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz0im)
  have hofc : Tendsto (fun z : ℂ => UpperHalfPlane.ofComplex z)
      (nhdsWithin (poleℂ τ) {poleℂ τ}ᶜ)
      (nhdsWithin (tauSubOne τ) {(tauSubOne τ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun z : ℂ => UpperHalfPlane.ofComplex z)
          (nhds (poleℂ τ)) (nhds (tauSubOne τ)) := by
        have h' := hcont.tendsto
        rwa [show UpperHalfPlane.ofComplex (poleℂ τ) = tauSubOne τ by
          rw [poleℂ, UpperHalfPlane.ofComplex_apply]] at h'
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, hUmem] with z hz hzim
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      intro hcon
      refine hz ?_
      have h1 : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = poleℂ τ := by
        rw [hcon, poleℂ]
      rwa [UpperHalfPlane.ofComplex_apply_of_im_pos hzim, UpperHalfPlane.coe_mk] at h1
  have hcomp := hres.comp hofc
  have hcomp' : Tendsto (fun z : ℂ =>
      (z - poleℂ τ) * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z))
      (nhdsWithin (poleℂ τ) {poleℂ τ}ᶜ) (nhds (1 / (2 * Real.pi))) := by
    refine hcomp.congr' ?_
    filter_upwards [hUmem] with z hzim
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzim, UpperHalfPlane.coe_mk]
    rfl
  have hexp : Tendsto (fun z : ℂ => kerExp r z / Complex.I)
      (nhdsWithin (poleℂ τ) {poleℂ τ}ᶜ) (nhds (kerExp r (poleℂ τ) / Complex.I)) := by
    have hc : ContinuousAt (fun z : ℂ => kerExp r z / Complex.I) (poleℂ τ) := by
      simp only [kerExp]
      fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hcomp'.mul hexp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hval : (1 / (2 * Real.pi) : ℂ) * (kerExp r (poleℂ τ) / Complex.I)
      = kerExp r (poleℂ τ) / (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    field_simp
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards with z
  simp only [kerForm]
  ring_nf

end Work.Asymptotics
