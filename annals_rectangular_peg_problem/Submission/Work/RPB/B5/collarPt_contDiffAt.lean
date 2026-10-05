import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.contDiffAt_signedArea_of_contDiffOn
import Submission.Work.RPB.B5.contDiffAt_param_intervalIntegral
import Submission.Work.RPB.B5.uproj_chart_contDiffAt_kappa
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff

/-!
# B5: `collarPt` is `C⁸` at `σ = 0`

This file proves `Work.RPB.B5.collarPt_contDiffAt`.  Recall the κ-collar of the chord annulus

* `kgam CI W ρh δ k τ σ t = kdiagM (kg CI W ρh δ k τ σ) (kshape CI W ρh δ k τ σ t)`
  is the real-linear normalisation of the glued shape, with `kg = 2π(1+σ)/karS`;
* `kac CI W ρh δ k τ σ t = kA0 … + ∫_0^t ω_ℂ(∂_σ kgam, ∂_t kgam)` is its phase;
* `collarPt Γc Ac τ σ t = levelPt (Γc τ σ t) σ (Ac τ σ t)`.

The claim is that `σ ↦ collarPt (kgam σ t) (kac σ t)` is `C⁸` at `σ = 0` (for fixed `τ, t`).

The proof has three layers, none of which is deep.

* `σ ↦ kshape σ t` and `σ ↦ karS σ` are `C⁸` near `0`: the first is the slice of the jointly
  `C¹²` glued shape `hkshape`; the second is `Work.RPB.B5.contDiffAt_signedArea_of_contDiffOn`
  applied to it (a signed area of a jointly `C¹²` family is `C¹¹`).  Since `karS 0 ≠ 0`, the
  quotient `kg = 2π(1+σ)/karS` is `C¹¹` at `0`, and hence `σ ↦ kgam σ t` is `C⁸`.
* For the phase, `kA0` is plainly `C^∞` in `σ` (a clamped smooth bump plus a finite sum), while
  the flux integral is a parametric interval integral of
  `(σ,u) ↦ ω_ℂ(∂_σ kgam (σ,u), ∂_t kgam (σ,u))`.  The joint family `(σ,u) ↦ kgam … σ u` is `C⁹`
  at each `(0,u)` (product of the `C¹¹` factor `kg σ` with the jointly `C¹²` shape, through the
  smooth `kdiagM`), so both partial derivatives are `C⁸` there and the integrand is `C⁸`; the
  integral is then `C⁸` by `contDiffAt_param_intervalIntegral`.
* Finally `levelPt` is `C⁸` (`chartJets_levelPt_contDiff`), so composing it with the `C⁸` map
  `σ ↦ (kgam σ t, σ, kac σ t)` gives the result.
-/

open MeasureTheory intervalIntegral
open scoped ContDiff Topology Interval

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.RPB.B5

/-! ## Smoothness of the elementary building blocks -/

/-- The real-linear map `kdiagM g z = (z.re) + i (g z.im)` is smooth as a function of the pair
`(g, z) : ℝ × ℂ`. -/
lemma kdiagM_contDiff_pair : ContDiff ℝ ∞ (fun p : ℝ × ℂ => kdiagM p.1 p.2) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((Complex.reCLM p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
  have h2 : ContDiff ℝ ∞
      (fun p : ℝ × ℂ => (((p.1 * Complex.imCLM p.2 : ℝ)) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_fst.mul (Complex.imCLM.contDiff.comp contDiff_snd))).mul contDiff_const
  have h := h1.add h2
  simpa only [kdiagM, Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply] using h

/-- `kphc δ k` is smooth. -/
lemma kphc_contDiff (δ : ℝ) (k : ℤ) : ContDiff ℝ ∞ (kphc δ k) := by
  have h : ContDiff ℝ ∞ (fun σ : ℝ => kstp ((σ - δ) / δ)) :=
    kstp_contDiff.comp (by fun_prop)
  unfold kphc
  exact (contDiff_const.mul h)

/-- `kjbump δ` is smooth. -/
lemma kjbump_contDiff (δ : ℝ) : ContDiff ℝ ∞ (kjbump δ) := by
  have h : ContDiff ℝ ∞ (fun σ : ℝ => kstp (σ / δ)) := kstp_contDiff.comp (by fun_prop)
  unfold kjbump
  exact contDiff_const.sub h

/-- `kA0 W ρh δ k τ` is smooth in `σ`. -/
lemma kA0_contDiff (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ : ℝ) : ContDiff ℝ ∞ (fun σ => kA0 W ρh δ k τ σ) := by
  unfold kA0
  refine (((kphc_contDiff δ k).add contDiff_const).add contDiff_const).add ?_
  apply ContDiff.sum
  intro j hj
  have h1 : ContDiff ℝ ∞ (fun σ : ℝ =>
      (kcj W ρh τ j - kcj W ρh 0 j) * (σ ^ j / (Nat.factorial j : ℝ))) :=
    (contDiff_const.mul (by fun_prop))
  exact h1.mul (kjbump_contDiff δ)

/-! ## Two generic calculus lemmas -/

/-- `ω_ℂ(f, g)` is `C^n` at `x` whenever `f` and `g` are. -/
private lemma contDiffAt_omegaC_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => Work.RPV.ωC (f y) (g y)) x := by
  have hconj : ContDiffAt ℝ n (fun y => (starRingEnd ℂ) (f y)) x := by
    have h := Complex.conjCLE.contDiff.contDiffAt.comp x hf
    simpa only [Function.comp_def, Complex.conjCLE_apply] using h
  have hmul : ContDiffAt ℝ n (fun y => (starRingEnd ℂ) (f y) * g y) x := hconj.mul hg
  have h := Complex.imCLM.contDiff.contDiffAt.comp x hmul
  simpa only [Function.comp_def, Complex.imCLM_apply, Work.RPV.ωC] using h

/-- The `σ`-slice derivative of a jointly `C^{n+1}` family is jointly `C^n`. -/
private lemma contDiffAt_sliceDeriv_fst {F : ℝ × ℝ → ℂ} {n : ℕ} {a b : ℝ}
    (hF : ContDiffAt ℝ (n + 1) F (a, b)) :
    ContDiffAt ℝ n (fun z : ℝ × ℝ => deriv (fun s => F (s, z.2)) z.1) (a, b) := by
  have hfd : ContDiffAt ℝ n (fderiv ℝ F) (a, b) :=
    hF.fderiv_right (m := (n : WithTop ℕ∞)) (by norm_num)
  have hval : ContDiffAt ℝ n (fun z : ℝ × ℝ => (fderiv ℝ F z) (1, 0)) (a, b) :=
    hfd.clm_apply contDiffAt_const
  refine hval.congr_of_eventuallyEq ?_
  filter_upwards [hF.eventually (by simp)] with z hz
  exact Work.RPA3.deriv_prodMk_left ((hz.differentiableAt (by simp)).hasFDerivAt)

/-- The `u`-slice derivative of a jointly `C^{n+1}` family is jointly `C^n`. -/
private lemma contDiffAt_sliceDeriv_snd {F : ℝ × ℝ → ℂ} {n : ℕ} {a b : ℝ}
    (hF : ContDiffAt ℝ (n + 1) F (a, b)) :
    ContDiffAt ℝ n (fun z : ℝ × ℝ => deriv (fun s => F (z.1, s)) z.2) (a, b) := by
  have hfd : ContDiffAt ℝ n (fderiv ℝ F) (a, b) :=
    hF.fderiv_right (m := (n : WithTop ℕ∞)) (by norm_num)
  have hval : ContDiffAt ℝ n (fun z : ℝ × ℝ => (fderiv ℝ F z) (0, 1)) (a, b) :=
    hfd.clm_apply contDiffAt_const
  refine hval.congr_of_eventuallyEq ?_
  filter_upwards [hF.eventually (by simp)] with z hz
  exact Work.RPA3.deriv_prodMk_right ((hz.differentiableAt (by simp)).hasFDerivAt)

/-! ## The main theorem -/

theorem collarPt_contDiffAt (CI : Work.RPV.CurveIsotopy) {ρ₀ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ) (k : ℤ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hkshape : ContDiffOn ℝ 12 (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2)
      (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ))
    (hne : karS CI W ρh δ k τ 0 ≠ 0) (t : ℝ) :
    ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.levelPt (kgam CI W ρh δ k τ σ t) σ
      (kac CI W ρh δ k τ σ t)) 0 := by
  -- the open neighbourhood of `(0, u)` on which `kshape` is jointly smooth
  have hmemAt : ∀ u : ℝ, (Set.Ioo (-1 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) ∈ 𝓝 ((0 : ℝ), u) :=
    fun u => (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨by norm_num, trivial⟩
  have hkshapeAt : ContDiffAt ℝ 12
      (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2) (0, t) :=
    hkshape.contDiffAt (hmemAt t)
  -- σ-slice of `kshape` at `t`
  have hksh12 : ContDiffAt ℝ 12 (fun σ : ℝ => kshape CI W ρh δ k τ σ t) 0 := by
    have hφ : ContDiffAt ℝ 12 (fun σ : ℝ => (σ, t)) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have h := hkshapeAt.comp 0 hφ
    simpa only [Function.comp_def] using h
  have hksh8 : ContDiffAt ℝ 8 (fun σ : ℝ => kshape CI W ρh δ k τ σ t) 0 :=
    hksh12.of_le (by norm_num)
  -- smoothness of the signed area `karS` at `0`
  have hkarS11 : ContDiffAt ℝ 11 (fun σ => karS CI W ρh δ k τ σ) 0 := by
    have hks : ContDiffOn ℝ (11 + 1)
        (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2) (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) :=
      hkshape
    have h := contDiffAt_signedArea_of_contDiffOn
      (fun σ t => kshape CI W ρh δ k τ σ t) 11 hks
    rw [show (fun σ => karS CI W ρh δ k τ σ)
        = (fun σ => Work.RPB.signedArea (fun t => kshape CI W ρh δ k τ σ t)) from rfl]
    exact h
  -- smoothness of the normalisation factor `kg` at `0`
  have hkg11 : ContDiffAt ℝ 11 (fun σ => kg CI W ρh δ k τ σ) 0 := by
    have hnum : ContDiffAt ℝ 11 (fun σ : ℝ => 2 * Real.pi * (1 + σ)) 0 := by fun_prop
    unfold kg
    exact hnum.div hkarS11 hne
  have hkg8 : ContDiffAt ℝ 8 (fun σ => kg CI W ρh δ k τ σ) 0 := hkg11.of_le (by norm_num)
  -- σ-slice of the collar curve `kgam` at `t`
  have hkgam8 : ContDiffAt ℝ 8 (fun σ => kgam CI W ρh δ k τ σ t) 0 := by
    have hpair : ContDiffAt ℝ 8
        (fun σ : ℝ => (kg CI W ρh δ k τ σ, kshape CI W ρh δ k τ σ t)) 0 :=
      hkg8.prodMk hksh8
    have hout : ContDiffAt ℝ 8 (fun p : ℝ × ℂ => kdiagM p.1 p.2)
        (kg CI W ρh δ k τ 0, kshape CI W ρh δ k τ 0 t) :=
      kdiagM_contDiff_pair.contDiffAt.of_le (by simp)
    have h := hout.comp 0 hpair
    simpa only [Function.comp_def, kgam] using h
  -- joint smoothness of `(σ,u) ↦ kgam σ u` at every `(0,u)`
  have hkgamJoint9 : ∀ u : ℝ,
      ContDiffAt ℝ 9 (fun z : ℝ × ℝ => kgam CI W ρh δ k τ z.1 z.2) (0, u) := by
    intro u
    have hkshapeAt9 : ContDiffAt ℝ 9
        (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2) (0, u) :=
      (hkshape.contDiffAt (hmemAt u)).of_le (by norm_num)
    have hkg9 : ContDiffAt ℝ 9 (fun z : ℝ × ℝ => kg CI W ρh δ k τ z.1) (0, u) := by
      have h9 : ContDiffAt ℝ 9 (fun σ : ℝ => kg CI W ρh δ k τ σ) 0 :=
        hkg11.of_le (by norm_num)
      have h := h9.comp ((0 : ℝ), u) (contDiffAt_fst (p := ((0 : ℝ), u)))
      simpa only [Function.comp_def] using h
    have hpair : ContDiffAt ℝ 9
        (fun z : ℝ × ℝ => (kg CI W ρh δ k τ z.1, kshape CI W ρh δ k τ z.1 z.2)) (0, u) :=
      hkg9.prodMk hkshapeAt9
    have hout : ContDiffAt ℝ 9 (fun p : ℝ × ℂ => kdiagM p.1 p.2)
        (kg CI W ρh δ k τ 0, kshape CI W ρh δ k τ 0 u) :=
      kdiagM_contDiff_pair.contDiffAt.of_le (by simp)
    have h := hout.comp (0, u) hpair
    simpa only [Function.comp_def, kgam] using h
  -- smoothness of the flux integral in `σ`
  have hInt : ContDiffAt ℝ 8
      (fun σ : ℝ => ∫ u in (0 : ℝ)..t,
        Work.RPV.ωC (deriv (fun s => kgam CI W ρh δ k τ s u) σ)
          (deriv (fun s => kgam CI W ρh δ k τ σ s) u)) 0 := by
    apply contDiffAt_param_intervalIntegral 8 _ 0 0 t
    intro u hu
    have hF : ContDiffAt ℝ 9 (fun z : ℝ × ℝ => kgam CI W ρh δ k τ z.1 z.2) (0, u) :=
      hkgamJoint9 u
    have hF1 : ContDiffAt ℝ 8
        (fun z : ℝ × ℝ => deriv (fun s => kgam CI W ρh δ k τ s z.2) z.1) (0, u) :=
      contDiffAt_sliceDeriv_fst (a := (0 : ℝ)) (b := u) hF
    have hF2 : ContDiffAt ℝ 8
        (fun z : ℝ × ℝ => deriv (fun s => kgam CI W ρh δ k τ z.1 s) z.2) (0, u) :=
      contDiffAt_sliceDeriv_snd (a := (0 : ℝ)) (b := u) hF
    exact contDiffAt_omegaC_pair hF1 hF2
  -- smoothness of the phase `kac`
  have hkac : ContDiffAt ℝ 8 (fun σ => kac CI W ρh δ k τ σ t) 0 := by
    have hA0 : ContDiffAt ℝ 8 (fun σ => kA0 W ρh δ k τ σ) 0 :=
      (kA0_contDiff W ρh δ k τ).contDiffAt.of_le (by simp)
    have h := hA0.add hInt
    simpa only [kac] using h
  -- assemble through the smooth `levelPt`
  have hΦ : ContDiffAt ℝ 8
      (fun σ : ℝ => (kgam CI W ρh δ k τ σ t, (σ, kac CI W ρh δ k τ σ t))) 0 :=
    hkgam8.prodMk (contDiffAt_id.prodMk hkac)
  have hlev : ContDiffAt ℝ 8
      (fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2)
      (kgam CI W ρh δ k τ 0 t, (0, kac CI W ρh δ k τ 0 t)) :=
    chartJets_levelPt_contDiff.contDiffAt
  have h := hlev.comp 0 hΦ
  simpa only [Function.comp_def] using h

end Work.RPB.B5
