import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.upperRegionRateAux
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

noncomputable section

open scoped Manifold ContDiff Topology in
/-- **The *model* (in-region) half of the `hrate` row of the upper certificate** (`NOTES_LEAD_saddlePacket.md` §4.3, the "model" case: the model arc `w ↦ √(σ(η,w) + i w)`).  At a point `y` of the **upper level** `f = c + lam·η` of a saddle chart (`f = c + lam·Re (Z ·)²` on the open `U`, `Z` an immersion on `U`, `lam ≠ 0`) that lies **in the model region** `|Im (Z ·)²| < c₀`, the planar picture `z ↦ Ψ (Z z)` of the model piece (`Ψ = Work.Drive.N2.saddlePsi η δ`) is never `1` and its rate about the centre `1` is non-zero **in every direction of `ker df`**.

This is exactly the `hrate` obligation of `Work.Drive.N2Lead.isCertifiedAt_of_starRegions` for the right-hand region `Ω_R = {Re > 0} ∩ ball 0 5` of the upper certificate, restricted to the points drawn by the model piece (the off-region points are drawn by `A ∘ foot` and are the other half of `hrate`).  The mathematical content: `(Z y)² = η + i w` with `w = ((Z y)²).im`, `|w| < c₀ ≤ 2` (this is where `hlam : lam ≠ 0` is used); with `ρ w := Work.Drive.N2Lead.mobiusRho η δ η w = √(σ(η,w) + i w)` one has `Ψ (Z y) = ±ρ w`, and since `Re (ρ w) > 0` the hypothesis `hpos` forces `Ψ (Z y) = ρ w`; along `v ∈ ker df` the chart gives `mfderiv (· ↦ (Z ·)²) y v = s·I` with `s ≠ 0`, whence `mfderiv (· ↦ Ψ (Z ·)) y v = s • deriv (mobiusRho η δ η) w`.  So the claim is `Im (conj (ρ w - 1) · ρ'(w)) ≠ 0` with `s ≠ 0`, which is the PROVED `Work.Drive.N2Lead.modelArc_cross_about_one` (with `s := η`, so `hsη : η ≤ η` is free). -/
theorem upperRegionRate {M : Type*} [TopologicalSpace M]
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
    (hpos : 0 < (Work.Drive.N2.saddlePsi η δ (Z y)).re)
    {v : TangentSpace (𝓡 2) y}
    (hv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0) (hvne : v ≠ 0) :
    Work.Drive.N2.saddlePsi η δ (Z y) ≠ (1 : ℂ) ∧
      ¬ ∃ t : ℝ, mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
            (fun x : M => (Work.Drive.N2.saddlePsi η δ (Z x) : ℂ)) y v
          = t • ((Work.Drive.N2.saddlePsi η δ (Z y) : ℂ) - (1 : ℂ)) := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hδ₂ : δ < 1 / 2 := by linarith
  have h2δ : (0 : ℝ) < 2 - 4 * δ := by linarith
  have h2δ' : (0 : ℝ) ≤ 2 - 4 * δ := le_of_lt h2δ
  -- the level of `y` in `Z`-coordinates
  have hZre : ((Z y) ^ 2).re = η := by
    have h := hlev y hyU
    rw [hyval] at h
    exact mul_left_cancel₀ hlam (by linarith)
  have hZy0 : Z y ≠ 0 := by
    intro h0
    have h1 : ((Z y) ^ 2).re = 0 := by rw [h0]; simp
    rw [hZre] at h1
    linarith
  have hZmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) Z y :=
    (hZsm.contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt hn
  -- auxiliary differentiability statements
  have hsqC : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun ζ : ℂ => ζ ^ 2) (Z y) := by
    rw [mdifferentiableAt_iff_differentiableAt]; fun_prop
  have hsq2 : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun u : ℂ => u ^ 2) (saddlePsi η δ (Z y)) := by
    rw [mdifferentiableAt_iff_differentiableAt]; fun_prop
  have hPhi_ch : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (Z x) ^ 2) y v
      = (fderiv ℝ (fun ζ : ℂ => ζ ^ 2) (Z y)) (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v) := by
    rw [show (fun x : M => (Z x) ^ 2) = (fun ζ : ℂ => ζ ^ 2) ∘ Z from rfl,
      mfderiv_comp_apply (f := Z) (g := fun ζ : ℂ => ζ ^ 2) y hsqC hZmd v, mfderiv_eq_fderiv]
    rfl
  have hPhi_md : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (Z x) ^ 2) y := hsqC.comp y hZmd
  -- the level function kills the real part of the derivative of `(Z ·)²`
  have hqc : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun ζ : ℂ => c + lam * (ζ ^ 2).re) (Z y) :=
    (mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ)).mpr (by fun_prop)
  have hfeq : f =ᶠ[𝓝 y] (fun x : M => c + lam * ((Z x) ^ 2).re) := by
    filter_upwards [hU.mem_nhds hyU] with x hx
    exact hlev x hx
  have h1p : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x : M => c + lam * ((Z x) ^ 2).re) y v = 0 := by
    rw [← hfeq.mfderiv_eq_v433]; exact hv
  have h1'' : (fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) (Z y))
      (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v) = 0 := by
    have e1 := mfderiv_comp_apply (f := Z) (g := fun ζ : ℂ => c + lam * (ζ ^ 2).re) y hqc hZmd v
    have h1' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ((fun ζ : ℂ => c + lam * (ζ ^ 2).re) ∘ Z) y v = 0 := h1p
    rw [e1] at h1'
    rw [mfderiv_eq_fderiv, fderiv_const_add] at h1'
    exact h1'
  -- the ℂ-typed derivative of `(Z ·)²` along `v`, and its real part
  set dPhi : ℂ := (fderiv ℝ (fun ζ : ℂ => ζ ^ 2) (Z y)) (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v) with hdPhi
  have hcs : fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) (Z y)
      = lam • fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z y) := by
    rw [show (fun ζ : ℂ => lam * (ζ ^ 2).re) = lam • (fun ζ : ℂ => (ζ ^ 2).re) from rfl,
      fderiv_const_smul (by fun_prop : DifferentiableAt ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z y))]
  have hrc : fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z y)
      = Complex.reCLM.comp (fderiv ℝ (fun ζ : ℂ => ζ ^ 2) (Z y)) := by
    rw [show (fun ζ : ℂ => (ζ ^ 2).re) = (⇑Complex.reCLM) ∘ (fun ζ : ℂ => ζ ^ 2) from rfl,
      fderiv_comp (𝕜 := ℝ) (Z y) (g := ⇑Complex.reCLM) (f := fun ζ : ℂ => ζ ^ 2)
        Complex.reCLM.differentiableAt (by fun_prop : DifferentiableAt ℝ (fun ζ : ℂ => ζ ^ 2) (Z y)),
      ContinuousLinearMap.fderiv (f := Complex.reCLM)]
  have hLW : (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z y))
      (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v) = 0 := by
    have h := h1''
    rw [hcs] at h
    have h2 : (lam • fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z y))
        (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v)
        = lam * ((fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z y))
            (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v)) :=
      smul_apply_real lam (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z y))
        (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v)
    rw [h2] at h
    exact (mul_eq_zero.mp h).resolve_left hlam
  have hPhi_re : dPhi.re = 0 :=
    (re_fderiv_sq (Z y) (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v)).trans hLW
  -- `s` and `dPhi = s * I`
  set s : ℝ := dPhi.im with hs
  have hdΦ : dPhi = (s : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [hPhi_re]; simp [Complex.mul_re]
    · rw [hs]; simp [Complex.mul_im]
  have hs_ne : s ≠ 0 := by
    intro hs0
    have hd0 : dPhi = 0 := by
      apply Complex.ext
      · rw [hPhi_re]; simp
      · rw [← hs]; exact hs0
    have hzv : (fderiv ℝ (fun ζ : ℂ => ζ ^ 2) (Z y)) (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v) = 0 := by
      rw [← hdPhi]; exact hd0
    have hW0 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v = 0 := by
      have h2 := fderiv_sq_apply (Z y) (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z y v)
      rw [h2] at hzv
      rcases mul_eq_zero.mp hzv with h' | h'
      · exact absurd h' (mul_ne_zero two_ne_zero hZy0)
      · exact h'
    exact hvne ((hZimm y hyU) (by rw [hW0, map_zero]))
  -- the imaginary part of `(Z y)²`
  set w : ℝ := ((Z y) ^ 2).im with hw
  -- ℂ-typed proxies for the three derivatives along `v`
  set dP : ℂ := mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePsi η δ (Z x)) y v with hdP
  set dP2 : ℂ := mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (saddlePsi η δ (Z x)) ^ 2) y v with hdP2
  set dQ : ℂ := mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePhi η δ ((Z x) ^ 2)) y v with hdQ
  have hΨmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (saddlePsi η δ) (Z y) :=
    ((contDiff_saddlePsi η δ hδ hδ₂).contMDiff.contMDiffAt).mdifferentiableAt hn
  have hPmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePsi η δ (Z x)) y :=
    hΨmd.comp y hZmd
  have hA : dP2 = 2 * (saddlePsi η δ (Z y)) * dP := by
    have e1 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          ((fun u : ℂ => u ^ 2) ∘ (fun x : M => saddlePsi η δ (Z x))) y v
        = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun u : ℂ => u ^ 2) (saddlePsi η δ (Z y)))
          (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePsi η δ (Z x)) y v) :=
      mfderiv_comp_apply (f := fun x : M => saddlePsi η δ (Z x)) (g := fun u : ℂ => u ^ 2)
        y hsq2 hPmd v
    have e2 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (saddlePsi η δ (Z x)) ^ 2) y v
        = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun u : ℂ => u ^ 2) (saddlePsi η δ (Z y)))
          (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePsi η δ (Z x)) y v) :=
      (congrArg (fun F : M → ℂ => mfderiv (𝓡 2) 𝓘(ℝ, ℂ) F y v)
        (show (fun x : M => (saddlePsi η δ (Z x)) ^ 2)
          = (fun u : ℂ => u ^ 2) ∘ (fun x : M => saddlePsi η δ (Z x)) from rfl)).trans e1
    have e3 : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun u : ℂ => u ^ 2) (saddlePsi η δ (Z y)))
          (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePsi η δ (Z x)) y v)
        = (fderiv ℝ (fun u : ℂ => u ^ 2) (saddlePsi η δ (Z y))) dP := by
      rw [mfderiv_eq_fderiv, ← hdP]
      rfl
    have e4 : (fderiv ℝ (fun u : ℂ => u ^ 2) (saddlePsi η δ (Z y))) dP
        = 2 * (saddlePsi η δ (Z y)) * dP :=
      fderiv_sq_apply (saddlePsi η δ (Z y)) dP
    exact hdP2.trans (e2.trans (e3.trans e4))
  have hΦc : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (saddlePhi η δ) ((Z y) ^ 2) :=
    ((contDiff_saddlePhi η δ hδ h2δ).contMDiff.contMDiffAt).mdifferentiableAt hn
  have hB : dQ = (fderiv ℝ (saddlePhi η δ) ((Z y) ^ 2)) dPhi := by
    have e1 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          ((saddlePhi η δ) ∘ (fun x : M => (Z x) ^ 2)) y v
        = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (saddlePhi η δ) ((Z y) ^ 2))
          (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (Z x) ^ 2) y v) :=
      mfderiv_comp_apply (f := fun x : M => (Z x) ^ 2) (g := saddlePhi η δ) y hΦc hPhi_md v
    have e2 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePhi η δ ((Z x) ^ 2)) y v
        = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (saddlePhi η δ) ((Z y) ^ 2))
          (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (Z x) ^ 2) y v) :=
      (congrArg (fun F : M → ℂ => mfderiv (𝓡 2) 𝓘(ℝ, ℂ) F y v)
        (show (fun x : M => saddlePhi η δ ((Z x) ^ 2))
          = (saddlePhi η δ) ∘ (fun x : M => (Z x) ^ 2) from rfl)).trans e1
    have e3 : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (saddlePhi η δ) ((Z y) ^ 2))
          (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (Z x) ^ 2) y v)
        = (fderiv ℝ (saddlePhi η δ) ((Z y) ^ 2)) dPhi := by
      rw [mfderiv_eq_fderiv]
      exact congrArg (fun z => (fderiv ℝ (saddlePhi η δ) ((Z y) ^ 2)) z) hPhi_ch
    exact hdQ.trans (e2.trans e3)
  have hfunEq : (fun x : M => (saddlePsi η δ (Z x)) ^ 2)
      = fun x : M => saddlePhi η δ ((Z x) ^ 2) :=
    funext fun x => saddlePsi_sq hδ h2δ' (Z x)
  have hC : dP2 = dQ := by
    have h : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => (saddlePsi η δ (Z x)) ^ 2) y v
        = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun x : M => saddlePhi η δ ((Z x) ^ 2)) y v := by
      rw [hfunEq]
      rfl
    exact hdP2.trans (h.trans hdQ.symm)
  have hD : (fderiv ℝ (saddlePhi η δ) ((Z y) ^ 2)) dPhi
      = s • (((deriv (modelSigma η δ η) w : ℝ) : ℂ) + Complex.I) := by
    rw [hdΦ, fderiv_saddlePhi_mul_I hδ h2δ ((Z y) ^ 2), hZre, ← hw]
  have hmain : 2 * (saddlePsi η δ (Z y)) * dP
      = s • (((deriv (modelSigma η δ η) w : ℝ) : ℂ) + Complex.I) :=
    hA.symm.trans (hC.trans (hB.trans hD))
  -- the model arcs and their rate
  set ρ : ℂ := mobiusRho η δ η w with hρ
  set ρ' : ℂ := deriv (fun u : ℝ => mobiusRho η δ η u) w with hρ'
  have hζne : modelZeta η δ η w ≠ 0 := modelZeta_ne_zero hδ hδ₂ hη w
  have hρsq : ρ ^ 2 = modelZeta η δ η w := by
    rw [hρ, pow_two, mobiusRho_eq_sqrt_modelZeta, sqrt_mul_self_of_ne_zero hζne]
  have hρne : ρ ≠ 0 := fun h0 => hζne (by rw [← hρsq, h0]; ring)
  have hρnn : 0 ≤ ρ.re := by
    rw [hρ, mobiusRho_eq_sqrt_modelZeta, sqrt_re_eq]
    positivity
  have hρre_ne : ρ.re ≠ 0 := by
    intro h0
    have h1 : (modelZeta η δ η w).re = -(ρ.im) ^ 2 := by
      have h := congrArg Complex.re hρsq
      rw [pow_two, Complex.mul_re, h0] at h
      linarith
    have h2 : w = 0 := by
      have h := congrArg Complex.im hρsq
      rw [pow_two, Complex.mul_im, h0, modelZeta_im] at h
      linarith
    have h3 : (modelZeta η δ η w).re = η := by
      rw [modelZeta_re, modelSigma_eq, h2, saddleM_zero hδ h2δ', zero_mul, add_zero]
    nlinarith [h1, h3, hη, sq_nonneg ρ.im]
  have hρpos : 0 < ρ.re := lt_of_le_of_ne hρnn (Ne.symm hρre_ne)
  have hPsq : (saddlePsi η δ (Z y)) ^ 2 = modelZeta η δ η w := by
    rw [saddlePsi_sq hδ h2δ', saddlePhi, modelZeta, modelSigma, hZre, hw]
  have hPy : saddlePsi η δ (Z y) = ρ := by
    have hfac : (saddlePsi η δ (Z y) - ρ) * (saddlePsi η δ (Z y) + ρ) = 0 := by
      have hsq : (saddlePsi η δ (Z y)) ^ 2 = ρ ^ 2 := by rw [hPsq, hρsq]
      have hd : (saddlePsi η δ (Z y) - ρ) * (saddlePsi η δ (Z y) + ρ)
          = (saddlePsi η δ (Z y)) ^ 2 - ρ ^ 2 := by ring
      rw [hd, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have hneg : (saddlePsi η δ (Z y)).re = -ρ.re := by
        rw [eq_neg_of_add_eq_zero_right h]; simp
      linarith
  have hrel : 2 * ρ * ρ' = (((deriv (modelSigma η δ η) w : ℝ)) : ℂ) + Complex.I := by
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => mobiusRho η δ η u) w :=
      ((mobiusRho_contDiff (η := η) hδ hδ₂ hη).differentiable (by simp)).differentiableAt
    have hfun : (fun u : ℝ => (mobiusRho η δ η u) ^ 2) = (fun u : ℝ => modelZeta η δ η u) := by
      funext u
      rw [pow_two, mobiusRho_eq_sqrt_modelZeta,
        sqrt_mul_self_of_ne_zero (modelZeta_ne_zero hδ hδ₂ hη u)]
    have hL : HasDerivAt (fun u : ℝ => (mobiusRho η δ η u) ^ 2) (2 * ρ * ρ') w := by
      have hd := hdiff.hasDerivAt.pow 2
      refine hd.congr_deriv ?_
      rw [hρ, hρ']
      simp
    have hσdiff : DifferentiableAt ℝ (modelSigma η δ η) w :=
      ((contDiff_modelSigma' η δ η hδ h2δ).differentiable (by simp)).differentiableAt
    have hR : HasDerivAt (fun u : ℝ => modelZeta η δ η u)
        ((((deriv (modelSigma η δ η) w : ℝ)) : ℂ) + Complex.I) w := by
      have h1 : HasDerivAt (fun u : ℝ => ((modelSigma η δ η u : ℂ)))
          (((deriv (modelSigma η δ η) w : ℝ)) : ℂ) w := HasDerivAt.ofReal_comp hσdiff.hasDerivAt
      have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) Complex.I w := by
        have hh := HasDerivAt.ofReal_comp (hasDerivAt_id w)
        have hh2 := hh.mul_const Complex.I
        simpa using hh2
      have hsum := h1.add h2
      have hfun2 : (fun u : ℝ => modelZeta η δ η u)
          = (fun u : ℝ => ((modelSigma η δ η u : ℂ)) + (u : ℂ) * Complex.I) := rfl
      rw [hfun2]
      exact hsum
    exact (hfun ▸ hL).unique hR
  have hEq2 : 2 * ρ * dP = 2 * ρ * (s • ρ') := by
    have hm := hmain
    rw [hPy, ← hrel] at hm
    rw [hm, Complex.real_smul, Complex.real_smul]
    ring
  have hdPrho : dP = s • ρ' :=
    mul_left_cancel₀ (mul_ne_zero two_ne_zero hρne) hEq2
  have hPy_ne_one : saddlePsi η δ (Z y) ≠ 1 := by
    intro h1
    have hz : modelZeta η δ η w = 1 := by rw [← hPsq, h1]; ring
    have him : w = 0 := by
      have h := congrArg Complex.im hz
      rw [modelZeta_im] at h
      simpa using h
    have hre : η = 1 := by
      have h := congrArg Complex.re hz
      rw [modelZeta_re, modelSigma_eq, him, saddleM_zero hδ h2δ', zero_mul, add_zero] at h
      simpa using h
    linarith
  have hwIcc : w ∈ Set.Icc (-2) 2 :=
    abs_le.mp (le_of_lt (lt_of_lt_of_le hyw hc₀))
  have hcross : (star (ρ - 1) * ρ').im < 0 := by
    have h := modelArc_cross_about_one (η := η) (δ := δ) (s := η) (C₀ := C₀) hδ hδ'
      hη hη' hη le_rfl hC₀ hsmall w hwIcc
    simpa only [hρ, hρ'] using h
  refine ⟨hPy_ne_one, ?_⟩
  rintro ⟨t, ht⟩
  have heq : t • (ρ - 1) = s • ρ' := by
    rw [← hdPrho, ht, hPy]
  have hzero : (star (ρ - 1) * (t • (ρ - 1))).im = 0 := by
    rw [Complex.real_smul]
    have hconj : star (ρ - 1) * (ρ - 1) = ((Complex.normSq (ρ - 1) : ℝ) : ℂ) := by
      rw [← starRingEnd_apply, mul_comm, Complex.mul_conj]
    have hrw : star (ρ - 1) * ((t : ℂ) * (ρ - 1))
        = (t : ℂ) * (star (ρ - 1) * (ρ - 1)) := by ring
    rw [hrw, hconj]
    simp
  have hval : (star (ρ - 1) * (s • ρ')).im = s * (star (ρ - 1) * ρ').im := by
    rw [Complex.real_smul]
    have hrw : star (ρ - 1) * ((s : ℂ) * ρ') = (s : ℂ) * (star (ρ - 1) * ρ') := by ring
    rw [hrw, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hfin : s * (star (ρ - 1) * ρ').im = 0 := by
    rw [← hval, ← heq, hzero]
  exact (mul_ne_zero hs_ne (ne_of_lt hcross)) hfin
end

end Work.Drive.N2Lead
