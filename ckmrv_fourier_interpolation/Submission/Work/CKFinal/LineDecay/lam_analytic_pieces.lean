import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.lam_analytic_aux
import Submission.Work.CKFinal.LineDecay.laplace_analytic_compact
import Submission.Work.CKFinal.LineDecay.laplace_analytic_Ici
import Submission.Work.CKFinal.LineDecay.Phi_axis_pointwise_bound
import Submission.Work.CKFinal.LineDecay.kax_bdd_segment

/-!
# The pieces of the holomorphy proof of `lam_analytic_kfun`

`psi1C`, `highPartC` and the two exponential phases of the horizontal segments are entire; the
integrands `t ↦ K^{(d)}(τ,x+it)` and `t ↦ Φ(τ,t)` are measurable; and the Laplace-type integrals
of `lowInt`, `tailInt`, `phiInt`, `horInt1`, `horInt2` are analytic on `{z : -π < z.re}`.
-/

namespace Work.CKFinal.LineDecay

open MeasureTheory UpperHalfPlane

noncomputable section

/-- `Ψ_1 w = ∫_0^1 (1-s) e^{-ws} ds`, the model Laplace transform used for `psi1C`. -/
def Psi1 (w : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, ((1 - s : ℝ) : ℂ) * Complex.exp (-(w * (s : ℂ)))

lemma analyticOnNhd_Psi1 : AnalyticOnNhd ℂ Psi1 Set.univ := by
  have h : AnalyticOnNhd ℂ
      (fun w : ℂ => ∫ s in (0 : ℝ)..1, ((1 - s : ℝ) : ℂ) * Complex.exp (-(w * (s : ℂ))))
      Set.univ := by
    apply laplace_analytic_compact (B := 1) (by norm_num)
    · exact (by fun_prop : Measurable (fun s : ℝ => ((1 - s : ℝ) : ℂ))).aestronglyMeasurable
    · intro t ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have ht1 : 0 < t := ht.1
      have ht2 : t ≤ 1 := ht.2
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
      linarith
  exact h

lemma psi1C_eq (z : ℂ) :
    psi1C z = Psi1 (-(Complex.I * z)) + Psi1 (Complex.I * z) := by
  have hpt : ∀ s : ℝ, 2 * (((1 - s : ℝ) : ℂ) * Complex.cos ((s : ℂ) * z))
      = ((1 - s : ℝ) : ℂ) * Complex.exp (-((-(Complex.I * z)) * (s : ℂ)))
        + ((1 - s : ℝ) : ℂ) * Complex.exp (-((Complex.I * z) * (s : ℂ))) := by
    intro s
    have h1 : Complex.exp ((s : ℂ) * z * Complex.I)
        = Complex.exp (-((-(Complex.I * z)) * (s : ℂ))) := by
      congr 1; ring
    have h2 : Complex.exp (-((s : ℂ) * z) * Complex.I)
        = Complex.exp (-((Complex.I * z) * (s : ℂ))) := by
      congr 1; ring
    have hcos := Complex.two_cos ((s : ℂ) * z)
    rw [h1, h2] at hcos
    calc 2 * (((1 - s : ℝ) : ℂ) * Complex.cos ((s : ℂ) * z))
        = ((1 - s : ℝ) : ℂ) * (2 * Complex.cos ((s : ℂ) * z)) := by ring
      _ = ((1 - s : ℝ) : ℂ) * (Complex.exp (-((-(Complex.I * z)) * (s : ℂ)))
            + Complex.exp (-((Complex.I * z) * (s : ℂ)))) := by rw [hcos]
      _ = _ := by ring
  have hInt1 : IntervalIntegrable
      (fun s : ℝ => ((1 - s : ℝ) : ℂ) * Complex.exp (-((-(Complex.I * z)) * (s : ℂ))))
      volume (0:ℝ) 1 :=
    ContinuousOn.intervalIntegrable (by fun_prop)
  have hInt2 : IntervalIntegrable
      (fun s : ℝ => ((1 - s : ℝ) : ℂ) * Complex.exp (-((Complex.I * z) * (s : ℂ))))
      volume (0:ℝ) 1 :=
    ContinuousOn.intervalIntegrable (by fun_prop)
  unfold psi1C Psi1
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr (fun s _ => hpt s)]
  rw [intervalIntegral.integral_add hInt1 hInt2]

lemma analyticOnNhd_psi1C : AnalyticOnNhd ℂ psi1C Set.univ := by
  have hmul : AnalyticOnNhd ℂ (fun z : ℂ => Complex.I * z) Set.univ :=
    analyticOnNhd_const.mul analyticOnNhd_id
  have h1 : AnalyticOnNhd ℂ (fun z : ℂ => Psi1 (-(Complex.I * z))) Set.univ :=
    analyticOnNhd_Psi1.comp hmul.neg (fun z _ => Set.mem_univ _)
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ => Psi1 (Complex.I * z)) Set.univ :=
    analyticOnNhd_Psi1.comp hmul (fun z _ => Set.mem_univ _)
  refine (h1.add h2).congr isOpen_univ (fun z _ => ?_)
  exact (psi1C_eq z).symm

lemma highPartC_eq (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) :
    highPartC G τ z
      = z * psi1C z * Complex.exp (-z) * G 0 0 τ
        + Complex.I * psi1C z * (z + 1) * Complex.exp (-z) * G 0 1 τ
        + (z - (2 * Real.pi : ℂ)) * psi1C (z - (2 * Real.pi : ℂ))
            * Complex.exp (-(z - (2 * Real.pi : ℂ))) * G 1 0 τ
        + Complex.I * psi1C (z - (2 * Real.pi : ℂ)) * ((z - (2 * Real.pi : ℂ)) + 1)
            * Complex.exp (-(z - (2 * Real.pi : ℂ))) * G 1 1 τ := rfl

lemma analyticOnNhd_highPartC (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun z : ℂ => highPartC G τ z) Set.univ := by
  have hpsi : AnalyticOnNhd ℂ psi1C Set.univ := analyticOnNhd_psi1C
  have hz : AnalyticOnNhd ℂ (fun z : ℂ => z) Set.univ := analyticOnNhd_id
  have hc : AnalyticOnNhd ℂ (fun _ : ℂ => (2 * Real.pi : ℂ)) Set.univ := analyticOnNhd_const
  have hz1 : AnalyticOnNhd ℂ (fun z : ℂ => z - (2 * Real.pi : ℂ)) Set.univ := hz.sub hc
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ => psi1C (z - (2 * Real.pi : ℂ))) Set.univ :=
    hpsi.comp hz1 (fun z _ => Set.mem_univ _)
  have hexp : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-z)) Set.univ :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-z))).differentiableOn.analyticOnNhd
      isOpen_univ
  have hexp2 : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-(z - (2 * Real.pi : ℂ)))) Set.univ :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-(z - (2 * Real.pi : ℂ))))).differentiableOn.analyticOnNhd
      isOpen_univ
  have hc00 : AnalyticOnNhd ℂ (fun _ : ℂ => G 0 0 τ) Set.univ := analyticOnNhd_const
  have hc01 : AnalyticOnNhd ℂ (fun _ : ℂ => G 0 1 τ) Set.univ := analyticOnNhd_const
  have hc10 : AnalyticOnNhd ℂ (fun _ : ℂ => G 1 0 τ) Set.univ := analyticOnNhd_const
  have hc11 : AnalyticOnNhd ℂ (fun _ : ℂ => G 1 1 τ) Set.univ := analyticOnNhd_const
  have hI : AnalyticOnNhd ℂ (fun _ : ℂ => Complex.I) Set.univ := analyticOnNhd_const
  have hz2 : AnalyticOnNhd ℂ (fun z : ℂ => z + 1) Set.univ := hz.add (analyticOnNhd_const (v := (1:ℂ)))
  have hz3 : AnalyticOnNhd ℂ (fun z : ℂ => (z - (2 * Real.pi : ℂ)) + 1) Set.univ :=
    hz1.add (analyticOnNhd_const (v := (1:ℂ)))
  have ht1 : AnalyticOnNhd ℂ
      (fun z : ℂ => z * psi1C z * Complex.exp (-z) * G 0 0 τ) Set.univ :=
    ((hz.mul hpsi).mul hexp).mul hc00
  have ht2 : AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.I * psi1C z * (z + 1) * Complex.exp (-z) * G 0 1 τ) Set.univ :=
    (((hI.mul hpsi).mul hz2).mul hexp).mul hc01
  have ht3 : AnalyticOnNhd ℂ
      (fun z : ℂ => (z - (2 * Real.pi : ℂ)) * psi1C (z - (2 * Real.pi : ℂ))
        * Complex.exp (-(z - (2 * Real.pi : ℂ))) * G 1 0 τ) Set.univ :=
    ((hz1.mul h2).mul hexp2).mul hc10
  have ht4 : AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.I * psi1C (z - (2 * Real.pi : ℂ)) * ((z - (2 * Real.pi : ℂ)) + 1)
        * Complex.exp (-(z - (2 * Real.pi : ℂ))) * G 1 1 τ) Set.univ :=
    (((hI.mul h2).mul hz3).mul hexp2).mul hc11
  refine (((ht1.add ht2).add ht3).add ht4).congr isOpen_univ (fun z _ => ?_)
  exact (highPartC_eq G τ z).symm


/-- Continuity (hence measurability) of `x ↦ x +ᵥ z` for `z : ℍ` fixed. -/
lemma continuous_vadd_const (z : UpperHalfPlane) :
    Continuous (fun x : ℝ => x +ᵥ z) := by
  have hf : Continuous (fun x : ℝ => (x : ℂ) + (z : ℂ)) := by fun_prop
  have hz : ∀ x : ℝ, 0 < ((x : ℂ) + (z : ℂ)).im := by
    intro x
    rw [Complex.add_im, Complex.ofReal_im, zero_add]
    exact z.im_pos
  have h : (fun x : ℝ => x +ᵥ z)
      = fun x : ℝ => UpperHalfPlane.mk ((x : ℂ) + (z : ℂ)) (hz x) := by
    funext x
    exact UpperHalfPlane.ext (by rw [UpperHalfPlane.coe_vadd])
  rw [h]
  exact hf.upperHalfPlaneMk hz

lemma measurable_vadd_const (z : UpperHalfPlane) :
    Measurable (fun x : ℝ => x +ᵥ z) :=
  (continuous_vadd_const z).measurable

/-- Measurability of `x ↦ K^{(d)}(τ, x+i)`. -/
lemma measurable_kax_fst (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    Measurable (fun x : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ x 1) := by
  have h : Measurable (fun x : ℝ => Work.Kernels.Kfun ℓ d τ
      (x +ᵥ Work.Kernels.imagAxis 1 (by norm_num))) :=
    (Work.Asymptotics.measurable_Kfun_snd_all ℓ d hd τ).comp
      (measurable_vadd_const (Work.Kernels.imagAxis 1 (by norm_num)))
  have hEq : (fun x : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ x 1)
      = fun x : ℝ => Work.Kernels.Kfun ℓ d τ
          (x +ᵥ Work.Kernels.imagAxis 1 (by norm_num)) := by
    funext x
    rw [Kax, dif_pos (by norm_num : (0:ℝ) < 1)]
  rw [hEq]
  exact h

/-- Measurability of `t ↦ Aexp G τ t`. -/
lemma measurable_Aexp (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    Measurable (fun t : ℝ => Work.Asymptotics.Aexp G τ t) := by
  unfold Work.Asymptotics.Aexp
  fun_prop

/-- `lamS` is entire. -/
lemma analyticOnNhd_lamS : AnalyticOnNhd ℂ lamS Set.univ := by
  have h : lamS = fun z : ℂ => 2 - Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z)) :=
    rfl
  rw [h]
  have h1 : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (Complex.I * z)) Set.univ :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (Complex.I * z))).differentiableOn.analyticOnNhd
      isOpen_univ
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-(Complex.I * z))) Set.univ :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Complex.I * z)))).differentiableOn.analyticOnNhd
      isOpen_univ
  exact (analyticOnNhd_const.sub h1).sub h2

/-- The pointwise form of `horInt1`. -/
lemma horInt1_eq (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) :
    horInt1 K τ z
      = (∫ x in (0 : ℝ)..1, Kax K τ (x - 1) hsplit * Complex.exp (-((-(Complex.I * z)) * (x : ℂ))))
        * Complex.exp (-z) := by
  unfold horInt1
  rw [intervalIntegral.integral_congr (fun x _ => ?_)]
  · rw [← intervalIntegral.integral_mul_const]
  · have hkey : Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I)
        = -((-(Complex.I * z)) * (x : ℂ)) + (-z) := by
      unfold hsplit
      push_cast
      linear_combination (z) * Complex.I_mul_I
    rw [hkey, Complex.exp_add, mul_assoc]

/-- The pointwise form of `horInt2`. -/
lemma horInt2_eq (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) :
    horInt2 K τ z
      = (∫ x in (-1 : ℝ)..0, Kax K τ (x + 1) hsplit * Complex.exp (-((-(Complex.I * z)) * (x : ℂ))))
        * Complex.exp (-z) := by
  unfold horInt2
  rw [intervalIntegral.integral_congr (fun x _ => ?_)]
  · rw [← intervalIntegral.integral_mul_const]
  · have hkey : Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I)
        = -((-(Complex.I * z)) * (x : ℂ)) + (-z) := by
      unfold hsplit
      push_cast
      linear_combination (z) * Complex.I_mul_I
    rw [hkey, Complex.exp_add, mul_assoc]


end

end Work.CKFinal.LineDecay
