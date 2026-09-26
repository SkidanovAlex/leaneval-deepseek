import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.CKFinal.LineDecay.lam_analytic_pieces

namespace Work.CKFinal.LineDecay

open MeasureTheory UpperHalfPlane

noncomputable section

/-- **Holomorphy of the two sides of the CKMRV identity in the complex variable `z = λ = π r²`**,
for the un-hatted pair `(K^{(d)}, 𝒢)`.  Every integral converges for `z.re > -π`: on `(0,1]` the
kernel is bounded (no pole of `z ↦ K(τ,z)` on the imaginary axis between `0` and `i`, by
`LineDecay/orbit_classification`), while on `[1,∞)` the cusp-subtracted kernel `K - Aexp` and the
second difference `Φ` are `O(poly·e^{-πt})` (`funnelKernelTail_sharp`-type bounds).  Hence
`e^{-zt}` gives an integrable dominating function on a neighbourhood of every `z₀` with
`z₀.re > -π`, and differentiating under the integral sign gives `DifferentiableOn`, hence
`AnalyticOnNhd` on the open half-plane. -/
theorem lam_analytic_kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) :
    AnalyticOnNhd ℂ (Work.CKFinal.LHSz (Work.Kernels.Kfun ℓ d)
        (Work.Asymptotics.Gcusp ℓ d) τ) {z : ℂ | -(Real.pi) < z.re}
    ∧ AnalyticOnNhd ℂ (Work.CKFinal.RHSz (Work.Kernels.Kfun ℓ d) τ)
        {z : ℂ | -(Real.pi) < z.re} := by
  set S : Set ℂ := {z : ℂ | -(Real.pi) < z.re} with hS
  have hSopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hτD : τ ∈ Work.Asymptotics.DomainD := mem_DomainD_of_re_half hτ (by linarith)
  obtain ⟨c₀, hc₀, hb₀⟩ := kax_flat_axis ℓ d hd hτD
  obtain ⟨C, M, T₀, hC, hM, hT₀, hbT⟩ := kax_tail_bound ℓ d hd hτD
  obtain ⟨Bφ, Aφ, hBφ, hAφ, hΦ⟩ := Phi_axis_pointwise_bound ℓ d hd τ hτ (by linarith)
  obtain ⟨Bs, hBs, hbS⟩ := kax_bdd_segment ℓ d hd τ hτ hy
  -- elementary entire pieces
  have hexpτ : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (Complex.I * (τ : ℂ) * z)) S :=
    ((by fun_prop : Differentiable ℂ
        (fun z : ℂ => Complex.exp (Complex.I * (τ : ℂ) * z))).differentiableOn.analyticOnNhd
      isOpen_univ).mono (Set.subset_univ S)
  have hexpneg : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-z)) Set.univ :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-z))).differentiableOn.analyticOnNhd
      isOpen_univ
  have hlamS : AnalyticOnNhd ℂ lamS S :=
    analyticOnNhd_lamS.mono (Set.subset_univ S)
  have hhigh : AnalyticOnNhd ℂ (fun z : ℂ => highPartC (Work.Asymptotics.Gcusp ℓ d) τ z) S :=
    (analyticOnNhd_highPartC (Work.Asymptotics.Gcusp ℓ d) τ).mono (Set.subset_univ S)
  -- the five integrals
  have hlow : AnalyticOnNhd ℂ (fun z : ℂ => lowInt (Work.Kernels.Kfun ℓ d) τ z) S := by
    have h := laplace_analytic_compact (f := fun t : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ 0 t)
      (a := 0) (b := 1) (B := c₀) hc₀.le
      ((measurable_kax_snd ℓ d hd τ 0).aestronglyMeasurable)
      (fun t ht => by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact hb₀ t ht.1 ht.2)
    exact h.mono (Set.subset_univ S)
  have htail : AnalyticOnNhd ℂ
      (fun z : ℂ => tailInt (Work.Kernels.Kfun ℓ d) (Work.Asymptotics.Gcusp ℓ d) τ z) S := by
    have h := laplace_analytic_Ici
      (f := fun t : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ 0 t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
      (C := C) (M := M) (T := T₀) hC.le hM hT₀
      (((measurable_kax_snd ℓ d hd τ 0).sub
        (measurable_Aexp (Work.Asymptotics.Gcusp ℓ d) τ)).aestronglyMeasurable)
      (fun t ht => hbT t ht)
    exact h
  have hphi : AnalyticOnNhd ℂ (fun z : ℂ => phiInt (Work.Kernels.Kfun ℓ d) τ z) S := by
    have hbound : ∀ t ∈ Set.Ici (1 : ℝ),
        ‖Phi (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ (Bφ * (1 + ‖(τ : ℂ)‖) ^ Aφ) * (1 + t) ^ Aφ
              * Real.exp (-(Real.pi * (t - 0))) := by
      intro t ht
      have h1 := hΦ t ht
      have h2 : Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))
          ≤ Real.exp (-(Real.pi * t)) := by
        rw [div_le_iff₀ (by positivity)]
        have h3 : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * (τ.im - t)) := by
          linarith [Real.exp_pos (2 * Real.pi * (τ.im - t))]
        calc Real.exp (-(Real.pi * t))
            = Real.exp (-(Real.pi * t)) * 1 := by ring
          _ ≤ Real.exp (-(Real.pi * t)) * (1 + Real.exp (2 * Real.pi * (τ.im - t))) :=
              mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg _)
      calc ‖Phi (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ Bφ * (1 + ‖(τ : ℂ)‖) ^ Aφ * (1 + t) ^ Aφ
              * (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := h1
        _ ≤ Bφ * (1 + ‖(τ : ℂ)‖) ^ Aφ * (1 + t) ^ Aφ * Real.exp (-(Real.pi * t)) := by
            apply mul_le_mul_of_nonneg_left h2
            have ht1 : (1 : ℝ) ≤ t := ht
            exact mul_nonneg (mul_nonneg hBφ (Real.rpow_nonneg (by positivity) _))
              (Real.rpow_nonneg (by linarith) _)
        _ = (Bφ * (1 + ‖(τ : ℂ)‖) ^ Aφ) * (1 + t) ^ Aφ
              * Real.exp (-(Real.pi * (t - 0))) := by rw [sub_zero]
    have h := laplace_analytic_Ici (f := fun t : ℝ => Phi (Work.Kernels.Kfun ℓ d) τ t)
      (C := Bφ * (1 + ‖(τ : ℂ)‖) ^ Aφ) (M := Aφ) (T := 0)
      (mul_nonneg hBφ (Real.rpow_nonneg (by positivity) _)) hAφ le_rfl
      ((measurable_Phi_axis ℓ d hd τ).aestronglyMeasurable) hbound
    exact h
  have hhor1 : AnalyticOnNhd ℂ (fun z : ℂ => horInt1 (Work.Kernels.Kfun ℓ d) τ z) S := by
    have hPsi : AnalyticOnNhd ℂ (fun w : ℂ => ∫ x in (0 : ℝ)..1,
        Kax (Work.Kernels.Kfun ℓ d) τ (x - 1) hsplit * Complex.exp (-(w * (x : ℂ)))) Set.univ := by
      refine laplace_analytic_compact
        (f := fun x : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ (x - 1) hsplit)
        (a := 0) (b := 1) (B := Bs) hBs ?_ ?_
      · exact ((measurable_kax_fst ℓ d hd τ).comp
          (measurable_id.sub measurable_const)).aestronglyMeasurable
      · intro x hx
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        exact hbS (x - 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmul : AnalyticOnNhd ℂ (fun z : ℂ => Complex.I * z) Set.univ :=
      analyticOnNhd_const.mul analyticOnNhd_id
    have hcomp : AnalyticOnNhd ℂ (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        Kax (Work.Kernels.Kfun ℓ d) τ (x - 1) hsplit
          * Complex.exp (-((-(Complex.I * z)) * (x : ℂ)))) Set.univ :=
      hPsi.comp hmul.neg (fun z _ => Set.mem_univ _)
    refine AnalyticOnNhd.congr hSopen ((hcomp.mul hexpneg).mono (Set.subset_univ S))
      (fun z _ => ?_)
    exact (horInt1_eq (Work.Kernels.Kfun ℓ d) τ z).symm
  have hhor2 : AnalyticOnNhd ℂ (fun z : ℂ => horInt2 (Work.Kernels.Kfun ℓ d) τ z) S := by
    have hPsi : AnalyticOnNhd ℂ (fun w : ℂ => ∫ x in (-1 : ℝ)..0,
        Kax (Work.Kernels.Kfun ℓ d) τ (x + 1) hsplit * Complex.exp (-(w * (x : ℂ)))) Set.univ := by
      refine laplace_analytic_compact
        (f := fun x : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ (x + 1) hsplit)
        (a := -1) (b := 0) (B := Bs) hBs ?_ ?_
      · exact ((measurable_kax_fst ℓ d hd τ).comp
          (measurable_id.add measurable_const)).aestronglyMeasurable
      · intro x hx
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        exact hbS (x + 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmul : AnalyticOnNhd ℂ (fun z : ℂ => Complex.I * z) Set.univ :=
      analyticOnNhd_const.mul analyticOnNhd_id
    have hcomp : AnalyticOnNhd ℂ (fun z : ℂ => ∫ x in (-1 : ℝ)..0,
        Kax (Work.Kernels.Kfun ℓ d) τ (x + 1) hsplit
          * Complex.exp (-((-(Complex.I * z)) * (x : ℂ)))) Set.univ :=
      hPsi.comp hmul.neg (fun z _ => Set.mem_univ _)
    refine AnalyticOnNhd.congr hSopen ((hcomp.mul hexpneg).mono (Set.subset_univ S))
      (fun z _ => ?_)
    exact (horInt2_eq (Work.Kernels.Kfun ℓ d) τ z).symm
  constructor
  · have hLHS : (LHSz (Work.Kernels.Kfun ℓ d) (Work.Asymptotics.Gcusp ℓ d) τ)
        = fun z : ℂ => Complex.exp (Complex.I * (τ : ℂ) * z)
            + lamS z * (lowInt (Work.Kernels.Kfun ℓ d) τ z
                + tailInt (Work.Kernels.Kfun ℓ d) (Work.Asymptotics.Gcusp ℓ d) τ z)
            + highPartC (Work.Asymptotics.Gcusp ℓ d) τ z := by
      funext z
      simp only [LHSz, LHSzHat]
      ring
    rw [hLHS]
    exact (hexpτ.add (hlamS.mul (hlow.add htail))).add hhigh
  · have hRHS : (RHSz (Work.Kernels.Kfun ℓ d) τ)
        = fun z : ℂ => lamS z * lowInt (Work.Kernels.Kfun ℓ d) τ z
            + (-Complex.I * horInt1 (Work.Kernels.Kfun ℓ d) τ z
                + Complex.I * horInt2 (Work.Kernels.Kfun ℓ d) τ z)
            + phiInt (Work.Kernels.Kfun ℓ d) τ z := by
      funext z
      simp only [RHSz]
    rw [hRHS]
    exact (((hlamS.mul hlow).add (((analyticOnNhd_const (v := -Complex.I)).mul hhor1).add
      ((analyticOnNhd_const (v := Complex.I)).mul hhor2)))).add hphi

end

end Work.CKFinal.LineDecay
