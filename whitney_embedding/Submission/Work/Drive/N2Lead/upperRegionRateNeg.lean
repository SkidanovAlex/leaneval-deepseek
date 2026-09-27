import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-! ## Helper lemmas for the `-ρ` branch of the upper certificate's `hrate` row -/

/-- Real scalar multiplication on `ℂ` is complex multiplication by the embedded scalar. -/
lemma smul_complex_eq_mul (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := by
  simp [Complex.smul_re, Complex.smul_im]

/-- The real part of the principal square root is nonnegative. -/
lemma sqrt_re_nonneg' (z : ℂ) : 0 ≤ z.sqrt.re := by
  rw [sqrt_re_eq]
  positivity

/-- The Fréchet derivative of the squaring map on `ℂ` in coordinates. -/
lemma fderiv_sq_apply' (c a : ℂ) :
    (fderiv ℝ (fun z : ℂ => z ^ 2) c) a = (2 * c) * a := by
  rw [show (fun z : ℂ => z ^ 2) = (fun z : ℂ => z) ^ 2 from rfl, fderiv_pow 2 differentiableAt_id]
  simp

/-- The Fréchet derivative of an affine map of `ℝ`. -/
lemma fderiv_affine' (c lam t : ℝ) :
    fderiv ℝ (fun s : ℝ => c + lam * s) t = lam • (1 : ℝ →L[ℝ] ℝ) :=
  (((hasFDerivAt_id (𝕜 := ℝ) t).const_mul lam).const_add c).fderiv

/-- **Differentiating the model identity `Ψ (z)² = φ (z²)`.**  The derivative of `Ψ` at `z` in the
direction `a`, multiplied by `2 Ψ z`, equals the derivative of `φ` at `z²` in the direction
`(2 z) · a`. -/
lemma saddlePsi_fderiv_mul' {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (z a : ℂ) :
    2 * saddlePsi η δ z * ((fderiv ℝ (saddlePsi η δ) z) a)
      = (fderiv ℝ (saddlePhi η δ) (z ^ 2)) ((2 * z) * a) := by
  have h2δ : (0 : ℝ) < 2 - 4 * δ := by linarith
  have hΨdiff : DifferentiableAt ℝ (saddlePsi η δ) z :=
    ((contDiff_saddlePsi η δ hδ hδ₂).differentiable (by simp)).differentiableAt
  have hPdiff : DifferentiableAt ℝ (saddlePhi η δ) (z ^ 2) :=
    ((contDiff_saddlePhi η δ hδ h2δ).differentiable (by simp)).differentiableAt
  have hfun : (fun w : ℂ => (saddlePsi η δ w) ^ 2)
      = (fun w : ℂ => saddlePhi η δ (w ^ 2)) :=
    funext (fun w => saddlePsi_sq hδ h2δ.le w)
  have h1 := DFunLike.congr_fun (congrArg (fun g : ℂ → ℂ => fderiv ℝ g z) hfun) a
  rw [fderiv_fun_pow 2 hΨdiff] at h1
  rw [show (fun w : ℂ => saddlePhi η δ (w ^ 2))
      = (saddlePhi η δ) ∘ (fun w : ℂ => w ^ 2) from rfl] at h1
  rw [fderiv_comp (f := fun w : ℂ => w ^ 2) (g := saddlePhi η δ) z hPdiff
      (by fun_prop)] at h1
  rw [ContinuousLinearMap.comp_apply] at h1
  rw [fderiv_sq_apply'] at h1
  simpa using h1

/-- **The derivative of `φ` along the imaginary axis.**  At `ζ = η + i w` (the point of the level
`Re ζ = η` with imaginary part `w`), the derivative of `φ` in the direction `i` is `σ' + i`, where
`σ'` is the derivative of the level coordinate `σ (η, ·)`. -/
lemma fderiv_saddlePhi_apply_I' {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) (w : ℝ) :
    (fderiv ℝ (saddlePhi η δ) ((η : ℂ) + (w : ℂ) * Complex.I)) Complex.I
      = ((deriv (modelSigma η δ η) w : ℝ) : ℂ) + Complex.I := by
  have hfd : HasFDerivAt (saddlePhi η δ)
      (fderiv ℝ (saddlePhi η δ) ((η : ℂ) + (w : ℂ) * Complex.I))
      ((η : ℂ) + (w : ℂ) * Complex.I) :=
    (((contDiff_saddlePhi η δ hδ h2).differentiable (by simp)).differentiableAt
      (x := (η : ℂ) + (w : ℂ) * Complex.I)).hasFDerivAt
  have hcurve : HasDerivAt (fun u : ℝ => (η : ℂ) + (u : ℂ) * Complex.I) Complex.I w := by
    simpa using (((hasDerivAt_id w).ofReal_comp).mul_const (Complex.I:ℂ)).const_add (η:ℂ)
  have h1 : HasDerivAt (fun u : ℝ => saddlePhi η δ ((η : ℂ) + (u : ℂ) * Complex.I))
      ((fderiv ℝ (saddlePhi η δ) ((η : ℂ) + (w : ℂ) * Complex.I)) Complex.I) w :=
    hfd.comp_hasDerivAt (l := saddlePhi η δ) w hcurve
  have h2' : HasDerivAt (fun u : ℝ => saddlePhi η δ ((η : ℂ) + (u : ℂ) * Complex.I))
      (((deriv (modelSigma η δ η) w : ℝ) : ℂ) + Complex.I) w := by
    have hfun : (fun u : ℝ => saddlePhi η δ ((η : ℂ) + (u : ℂ) * Complex.I))
        = (fun u : ℝ => ((saddleSigma η δ (η, u) : ℝ) : ℂ) + ((u : ℝ) : ℂ) * Complex.I) := by
      funext u
      apply Complex.ext
      · rw [saddlePhi_re]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      · rw [saddlePhi_im]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    rw [hfun]
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => saddleSigma η δ (η, t)) :=
      (contDiff_saddleSigma η δ hδ h2).comp (ContDiff.prodMk contDiff_const contDiff_id)
    have hgdiff : DifferentiableAt ℝ (modelSigma η δ η) w :=
      ((hg.differentiable (by simp)).differentiableAt (x := w))
    have hσ : HasDerivAt (fun u : ℝ => saddleSigma η δ (η, u)) (deriv (modelSigma η δ η) w) w :=
      hgdiff.hasDerivAt
    have hI : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ) * Complex.I) Complex.I w := by
      simpa using (((hasDerivAt_id w).ofReal_comp).mul_const (Complex.I:ℂ))
    exact hσ.ofReal_comp.add hI
  exact h1.unique h2'

/-- **The derivative of the model `ζ = σ + i w` in `w`.** -/
lemma hasDerivAt_modelZeta' {η δ s : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) (w : ℝ) :
    HasDerivAt (fun u : ℝ => modelZeta η δ s u)
      (((deriv (modelSigma η δ s) w : ℝ) : ℂ) + Complex.I) w := by
  have hσdiff : DifferentiableAt ℝ (modelSigma η δ s) w :=
    ((contDiff_modelSigma' η δ s hδ h2).differentiable (by simp)).differentiableAt
  have h1 : HasDerivAt (fun u : ℝ => ((modelSigma η δ s u : ℂ)))
      (((deriv (modelSigma η δ s) w : ℝ)) : ℂ) w :=
    hσdiff.hasDerivAt.ofReal_comp
  have h2' : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) Complex.I w := by
    simpa using ((hasDerivAt_id w).ofReal_comp.mul_const (Complex.I : ℂ))
  have hsum := h1.add h2'
  have hfun2 : (fun u : ℝ => modelZeta η δ s u)
      = (fun u : ℝ => ((modelSigma η δ s u : ℂ)) + (u : ℂ) * Complex.I) := rfl
  rw [hfun2]
  exact hsum

open scoped Manifold ContDiff Topology in
/-- **The mirror of `Work.Drive.N2Lead.upperRegionRate`: the `-ρ` branch of the upper certificate's `hrate` row, about the centre `-1`.**  Same setting as `upperRegionRate` (a point `y` of the upper level `f = c + lam·η` of a saddle chart, in the model region `|Im (Z ·)²| < c₀`), but now for the points whose picture `Ψ (Z y)` has **negative** real part — i.e. `Ψ (Z y) = -ρ w` with `ρ w = √(σ(η,w) + i w)` — which are the points of the level drawn in the *left* region `Ω_L = {Re < 0} ∩ ball 0 5` of `Work.Drive.N2Lead.isCertifiedAt_of_starRegions`.  Conclusion: the picture is never `-1` and its rate about `-1` never vanishes along `ker df`.

The proof is the mirror of the `+1` case: `Ψ (Z y) = -ρ w` and `mfderiv (· ↦ Ψ (Z ·)) y v = -s • ρ'(w)` with `s ≠ 0`, and the rate about the matched centre `-1` is `Im (conj ((-ρ) - (-1)) · (-ρ')) = Im (conj (ρ - 1) · ρ')`, which is `< 0` by the PROVED `Work.Drive.N2Lead.modelArc_cross_about_one`; so if the derivative were a real multiple of `Ψ (Z y) - (-1)` the imaginary part of `conj (Ψ (Z y) + 1)` times it would be `t · Im (|Ψ (Z y) + 1|²) = 0`, a contradiction.  `Ψ (Z y) ≠ -1`: `(Ψ (Z y))² = σ(η,w) + i w` and `Ψ (Z y) = -1` forces `w = 0` and `(Z y)² = 1`, i.e. `η = 1`, contradicting `hη'`.  Route as in `upperRegionRate`: `(Z y)².re = η` (`hlam`), `mfderiv (· ↦ (Z ·)²) y v = s·I` with `s ≠ 0` (`hv`, `hZimm`), the chain rule from `saddlePsi_sq` and the explicit `saddlePhi`, `Re (mobiusRho η δ η w) > 0` selects the branch from `hneg`. -/
theorem upperRegionRateNeg {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {c lam η δ c₀ C₀ : ℝ} {U : Set M} {Z : M → ℂ} {y : M}
    (hU : IsOpen U)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    (hZimm : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x))
    (hlev : ∀ x ∈ U, f x = c + lam * ((Z x) ^ 2).re)
    (hlam : lam ≠ 0)
    (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hc₀ : c₀ ≤ 2)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 8 * C₀ * η ≤ δ)
    (hyU : y ∈ U) (hyw : |((Z y) ^ 2).im| < c₀) (hyval : f y = c + lam * η)
    (hneg : (Work.Drive.N2.saddlePsi η δ (Z y)).re < 0)
    {v : TangentSpace (𝓡 2) y}
    (hv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0) (hvne : v ≠ 0) :
    Work.Drive.N2.saddlePsi η δ (Z y) ≠ (-1 : ℂ) ∧
      ¬ ∃ t : ℝ, mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
            (fun x : M => (Work.Drive.N2.saddlePsi η δ (Z x) : ℂ)) y v
          = t • ((Work.Drive.N2.saddlePsi η δ (Z y) : ℂ) - (-1 : ℂ)) := by
  have hδ₂ : δ < 1 / 2 := by linarith
  have h2δ : (0 : ℝ) < 2 - 4 * δ := by linarith
  -- ### the level coordinate of `y`
  have hzre : ((Z y) ^ 2).re = η := by
    have h1 := hlev y hyU
    rw [hyval] at h1
    exact mul_left_cancel₀ hlam (by linarith)
  have hzsq_ne : (Z y) ^ 2 ≠ 0 := by
    intro h0
    rw [h0] at hzre
    simp at hzre
    linarith
  have hz_ne : Z y ≠ 0 := fun h0 => hzsq_ne (by rw [h0]; ring)
  have hw2 : |((Z y) ^ 2).im| < 2 := lt_of_lt_of_le hyw hc₀
  have hwIcc : ((Z y) ^ 2).im ∈ Set.Icc (-2) 2 := by
    rw [Set.mem_Icc]
    exact abs_le.mp hw2.le
  have hζeq : (Z y) ^ 2 = (η : ℂ) + (((Z y) ^ 2).im : ℂ) * Complex.I := by
    have h := Complex.re_add_im ((Z y) ^ 2)
    rw [hzre] at h
    exact h.symm
  -- ### abbreviations
  set w : ℝ := ((Z y) ^ 2).im with hwdef
  set a : ℂ := mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v with hadef
  set dψ : ℂ := mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
    (fun x : M => (Work.Drive.N2.saddlePsi η δ (Z x) : ℂ)) y v with hdψdef
  set ζ' : ℂ := mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (Z x) ^ 2) y v with hζ'def
  set A : ℂ := (Work.Drive.N2.saddlePsi η δ (Z y) : ℂ) + 1 with hAdef
  set ρ : ℂ := mobiusRho η δ η w with hρdef
  set ρ' : ℂ := deriv (fun u : ℝ => mobiusRho η δ η u) w with hρ'def
  set σ' : ℝ := deriv (modelSigma η δ η) w with hσ'def
  -- ### differentiability
  have hZmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) Z y :=
    (hZsm.contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt (by simp)
  have hΨmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Work.Drive.N2.saddlePsi η δ) (Z y) :=
    ((Work.Drive.N2.contDiff_saddlePsi η δ hδ hδ₂).contMDiff.mdifferentiableAt (by simp))
  have hsqmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => z ^ 2) (Z y) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z ^ 2) :=
      ContDiff.pow contDiff_id 2
    exact h.contMDiff.mdifferentiableAt (by simp)
  have hGmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (Z x) ^ 2) y :=
    hsqmd.comp y hZmd
  have hRmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun x : M => ((Z x) ^ 2).re) y :=
    Complex.reCLM.mdifferentiableAt.comp y hGmd
  -- ### the chain rules
  have hψderiv : dψ = (fderiv ℝ (Work.Drive.N2.saddlePsi η δ) (Z y)) a := by
    rw [hdψdef, hadef]
    have h := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, ℂ))
      (f := Z) (g := Work.Drive.N2.saddlePsi η δ) y hΨmd hZmd v
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hGderiv : ζ' = (2 * Z y) * a := by
    have h := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, ℂ))
      (f := Z) (g := fun z : ℂ => z ^ 2) y hsqmd hZmd v
    have h2 : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => z ^ 2) (Z y))
        ((mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y) v) = (2 * Z y) * a := by
      rw [← hadef, mfderiv_eq_fderiv]
      exact fderiv_sq_apply' (Z y) a
    exact h.trans h2
  -- ### the level coordinate of the derivative vanishes
  have hre0 : ζ'.re = 0 := by
    rw [hζ'def]
    have hR : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x : M => ((Z x) ^ 2).re) y v = 0 := by
      have heq : f =ᶠ[𝓝 y] (fun x : M => c + lam * ((Z x) ^ 2).re) := by
        filter_upwards [hU.mem_nhds hyU] with x hx
        exact hlev x hx
      have h1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x : M => c + lam * ((Z x) ^ 2).re) y v = 0 := by
        rw [← heq.mfderiv_eq_v433]
        exact hv
      have h2 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x : M => ((Z x) ^ 2).re) y v = 0 := by
        have hgmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => c + lam * s)
            ((Z y) ^ 2).re := by
          have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => c + lam * s) :=
            contDiff_const.add (contDiff_const.mul contDiff_id)
          exact h.contMDiff.mdifferentiableAt (by simp)
        have heq2 : f =ᶠ[𝓝 y]
            ((fun s : ℝ => c + lam * s) ∘ (fun x : M => ((Z x) ^ 2).re)) := heq
        have hfmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f y :=
          (hgmd.comp y hRmd).congr_of_eventuallyEq heq2
        have hkeq : (fun x : M => ((Z x) ^ 2).re) =ᶠ[𝓝 y] (fun x : M => (f x - c) / lam) := by
          filter_upwards [hU.mem_nhds hyU] with x hx
          rw [hlev x hx, add_sub_cancel_left, mul_div_cancel_left₀ _ hlam]
        have hkmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s - c) / lam) (f y) := by
          have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (s - c) / lam) :=
            (contDiff_id.sub contDiff_const).div_const lam
          exact hh.contMDiff.mdifferentiableAt (by simp)
        have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
          (f := f) (g := fun s : ℝ => (s - c) / lam) y hkmd hfmd v
        have hv1 : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ((fun s : ℝ => (s - c) / lam) ∘ f) y) v = 0 := by
          rw [hcomp, hv, map_zero]
        rw [hkeq.mfderiv_eq_v433]
        exact hv1
      exact h2
    have hR' : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Complex.reCLM ∘ (fun x : M => (Z x) ^ 2)) y) v = 0 := hR
    have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, ℝ))
      (f := fun x : M => (Z x) ^ 2) (g := Complex.reCLM) y Complex.reCLM.mdifferentiableAt hGmd v
    rw [← hζ'def] at hcomp
    rw [mfderiv_eq_fderiv] at hcomp
    rw [ContinuousLinearMap.fderiv] at hcomp
    have hthis : Complex.reCLM ζ' = 0 := hcomp.symm.trans hR'
    exact hthis
  -- ### the derivative of the level coordinate is nonzero
  have hζ'ne : ζ' ≠ 0 := by
    intro h0
    have h2z : (2 : ℂ) * Z y ≠ 0 := mul_ne_zero (by norm_num) hz_ne
    have ha0 : a = 0 := by
      have h := hGderiv
      rw [h0] at h
      exact (mul_eq_zero.mp h.symm).resolve_left h2z
    have hv0 : v = 0 := by
      rw [hadef] at ha0
      exact hZimm y hyU (by rw [ha0, map_zero])
    exact hvne hv0
  have hζ'im : ζ' = ((ζ'.im : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.re_add_im ζ', hre0]
    simp
  -- ### the model facts
  have hρsq : ρ * ρ = modelZeta η δ η w := by
    rw [hρdef]
    exact sqrt_mul_self_of_ne_zero (modelZeta_ne_zero hδ hδ₂ hη w)
  have hρrel : 2 * ρ * ρ' = ((σ' : ℝ) : ℂ) + Complex.I := by
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => mobiusRho η δ η u) w :=
      ((mobiusRho_contDiff (η := η) hδ hδ₂ hη).differentiable (by simp)).differentiableAt
    have hfun : (fun u : ℝ => (mobiusRho η δ η u) ^ 2) = (fun u : ℝ => modelZeta η δ η u) := by
      funext u
      rw [pow_two]
      exact sqrt_mul_self_of_ne_zero (modelZeta_ne_zero hδ hδ₂ hη u)
    have hL : HasDerivAt (fun u : ℝ => (mobiusRho η δ η u) ^ 2)
        (2 * mobiusRho η δ η w * deriv (fun u : ℝ => mobiusRho η δ η u) w) w := by
      have hd := hdiff.hasDerivAt.pow 2
      refine hd.congr_deriv ?_
      simp
    have hmain := (hfun ▸ hL).unique (hasDerivAt_modelZeta' (s := η) hδ h2δ w)
    exact hmain
  have hρre : 0 ≤ ρ.re := by
    rw [hρdef]
    exact sqrt_re_nonneg' (modelZeta η δ η w)
  have hρne : ρ ≠ 0 :=
    fun h0 => modelZeta_ne_zero hδ hδ₂ hη w (by rw [← hρsq, h0]; ring)
  -- ### the branch: `ψ (z) = -ρ`
  have hΨsq : (Work.Drive.N2.saddlePsi η δ (Z y)) ^ 2 = modelZeta η δ η w := by
    rw [Work.Drive.N2.saddlePsi_sq hδ h2δ.le, hζeq]
    apply Complex.ext
    · rw [Work.Drive.N2.saddlePhi_re, modelZeta_re, Work.Drive.N2.saddleSigma_apply,
        modelSigma_eq]
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    · rw [Work.Drive.N2.saddlePhi_im, modelZeta_im]
      simp
  have hΨneg : (Work.Drive.N2.saddlePsi η δ (Z y)) = -ρ := by
    have hfac : ((Work.Drive.N2.saddlePsi η δ (Z y)) - ρ)
        * ((Work.Drive.N2.saddlePsi η δ (Z y)) + ρ) = 0 := by
      have hh : (Work.Drive.N2.saddlePsi η δ (Z y)) ^ 2 - ρ ^ 2 = 0 := by
        rw [hΨsq, ← hρsq]
        ring
      have hprod : ((Work.Drive.N2.saddlePsi η δ (Z y)) - ρ)
          * ((Work.Drive.N2.saddlePsi η δ (Z y)) + ρ)
          = (Work.Drive.N2.saddlePsi η δ (Z y)) ^ 2 - ρ ^ 2 := by ring
      rw [hprod, hh]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exfalso
      have hre : (Work.Drive.N2.saddlePsi η δ (Z y)).re = ρ.re := by
        rw [sub_eq_zero.mp h1]
      linarith [hρre, hneg, hre]
    · exact eq_neg_of_add_eq_zero_left h1
  have hΨne1 : (Work.Drive.N2.saddlePsi η δ (Z y)) ≠ (-1 : ℂ) := by
    intro h1
    have hρ1 : ρ = 1 := by
      have h2 : -ρ = -1 := by rw [← hΨneg, h1]
      exact neg_inj.mp h2
    have hmod : modelZeta η δ η w = 1 := by
      rw [← hρsq, hρ1]
      ring
    have hw0 : w = 0 := by
      have h := congrArg Complex.im hmod
      rw [modelZeta_im] at h
      simpa using h
    have hη1 : η = 1 := by
      have h := congrArg Complex.re hmod
      rw [modelZeta_re, hw0, modelSigma_eq,
        Work.Drive.N2.saddleM_eq_zero_of_abs_le hδ (by rw [abs_zero]; linarith)] at h
      simpa using h
    linarith [hη']
  -- ### the derivative identity
  have hID : 2 * (Work.Drive.N2.saddlePsi η δ (Z y)) * dψ
      = (fderiv ℝ (Work.Drive.N2.saddlePhi η δ) ((Z y) ^ 2)) ζ' := by
    rw [hψderiv, hGderiv]
    exact saddlePsi_fderiv_mul' hδ hδ₂ (Z y) a
  have hfdI : (fderiv ℝ (Work.Drive.N2.saddlePhi η δ) ((η : ℂ) + (w : ℂ) * Complex.I)) Complex.I
      = ((σ' : ℝ) : ℂ) + Complex.I :=
    fderiv_saddlePhi_apply_I' hδ h2δ w
  have hID' : 2 * (Work.Drive.N2.saddlePsi η δ (Z y)) * dψ
      = ((ζ'.im : ℝ) : ℂ) * (((σ' : ℝ) : ℂ) + Complex.I) := by
    have h0 : 2 * (Work.Drive.N2.saddlePsi η δ (Z y)) * dψ
        = (fderiv ℝ (Work.Drive.N2.saddlePhi η δ) ((η : ℂ) + (w : ℂ) * Complex.I))
          (((ζ'.im : ℝ) : ℂ) * Complex.I) := by
      rw [hID]
      conv_lhs => rw [hζ'im]
      rw [show ((Z y) ^ 2) = (η : ℂ) + (w : ℂ) * Complex.I by rw [hζeq]]
    have harg : (((ζ'.im : ℝ) : ℂ) * Complex.I) = (ζ'.im : ℝ) • (Complex.I : ℂ) := by
      rw [smul_complex_eq_mul]
    calc 2 * (Work.Drive.N2.saddlePsi η δ (Z y)) * dψ
        = (fderiv ℝ (Work.Drive.N2.saddlePhi η δ) ((η : ℂ) + (w : ℂ) * Complex.I))
            (((ζ'.im : ℝ) : ℂ) * Complex.I) := h0
      _ = (fderiv ℝ (Work.Drive.N2.saddlePhi η δ) ((η : ℂ) + (w : ℂ) * Complex.I))
            ((ζ'.im : ℝ) • (Complex.I : ℂ)) := by rw [harg]
      _ = (ζ'.im : ℝ) • ((fderiv ℝ (Work.Drive.N2.saddlePhi η δ)
            ((η : ℂ) + (w : ℂ) * Complex.I)) Complex.I) := by
            rw [ContinuousLinearMap.map_smul]
      _ = (ζ'.im : ℝ) • (((σ' : ℝ) : ℂ) + Complex.I) := by rw [hfdI]
      _ = ((ζ'.im : ℝ) : ℂ) * (((σ' : ℝ) : ℂ) + Complex.I) := by rw [smul_complex_eq_mul]
  have hdψ : dψ = -(((ζ'.im : ℝ) : ℂ) * ρ') := by
    have h := hID'
    rw [hΨneg, ← hρrel] at h
    have hc : (2 : ℂ) * (-ρ) ≠ 0 := mul_ne_zero (by norm_num) (neg_ne_zero.mpr hρne)
    have h2 : (2 * (-ρ)) * dψ = (2 * (-ρ)) * (-(((ζ'.im : ℝ) : ℂ) * ρ')) := by
      rw [h]
      ring
    exact mul_left_cancel₀ hc h2
  have hζ'imne : ζ'.im ≠ 0 := by
    intro h0
    refine hζ'ne ?_
    rw [hζ'im, h0]
    simp
  -- ### the cross product with `ψ (z) + 1` is nonzero
  have hcross : (star A * dψ).im ≠ 0 := by
    have hkey : star A * dψ = ((ζ'.im : ℝ) : ℂ) * (star (ρ - 1) * ρ') := by
      rw [hAdef, hΨneg, hdψ]
      rw [show (-ρ + 1 : ℂ) = 1 - ρ by ring]
      rw [show (1 - ρ : ℂ) = -(ρ - 1) by ring, star_neg]
      ring
    rw [hkey, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero]
    exact mul_ne_zero hζ'imne
      (ne_of_lt (modelArc_cross_about_one hδ hδ' hη hη' hη le_rfl hC₀ hsmall w hwIcc))
  refine ⟨hΨne1, ?_⟩
  rintro ⟨t, ht⟩
  exact hcross (by
    rw [ht]
    rw [show (Work.Drive.N2.saddlePsi η δ (Z y)) - (-1) = A by rw [hAdef]; ring]
    rw [smul_complex_eq_mul]
    have hkey : star A * ((t : ℂ) * A) = ((t * Complex.normSq A : ℝ) : ℂ) := by
      have h3 : star A * A = ((Complex.normSq A : ℝ) : ℂ) := by
        rw [mul_comm (star A) A]
        exact Complex.mul_conj A
      have h4 : star A * ((t : ℂ) * A) = (t : ℂ) * (star A * A) := by ring
      rw [h4, h3, ← Complex.ofReal_mul]
    rw [hkey, Complex.ofReal_im])

end

end Work.Drive.N2Lead
