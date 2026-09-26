import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.Compact

/-- **The `low + trunc + high` decomposition reproduces the contour integral, with the
cusp-`i∞` tail estimate assumed only at the point `τ` under consideration.**

This is `Work.Asymptotics.paperLayer_agreement` with the hypothesis on `K - Aexp` weakened from a
global bound on `τ ∈ 𝒟` (with the `τ`-dependent factor `(scale τ)^N`) to a bound holding at the
single point `τ`: the only place where the tail estimate is used is the integrability of
`t ↦ (K^{(d)}(τ,it) - Aexp G τ t) e^{-πr²t}` on `(1,∞)`, which is a statement about one `τ`.

The proof is the telescoping `∫_0^∞ = ∫_0^1 + ∫_1^∞ = ∫_0^1 + ∫_1^∞(K - A) + ∫_1^∞ A` together
with the closed form of `∫_1^∞ A(τ,it)e^{-πr²t}dt`, which is `highPart`: the double zeros of
`2 - 2cos(πr²) = 4 sin²(πr²/2)` at `λ = πr² = 0` and at `μ = πr² - 2π = 0` are exactly the factors
`psi1`, and `∫_1^∞ t^j e^{-νt}dt = e^{-ν}(ν+1)^j/ν^{j+1}`. -/
theorem local_agreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    (h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0)
    {K : Set UpperHalfPlane}
    (hflatK : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpolyK : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K → r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      Work.Asymptotics.paperLayer G ℓ d τ r
        = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
  intro τ r hτK hr hInt
  obtain ⟨C, M, T₀, hC, hM, hT₀, hpoly⟩ := hpolyK
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  set L : ℝ := Real.pi * r ^ 2 with hL
  set Mu : ℝ := L - 2 * Real.pi with hMu
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLne : L ≠ 0 := hLpos.ne'
  have hcosL : sinSq r = ((2 - 2 * Real.cos L : ℝ) : ℂ) := by
    rw [sinSq_eq_two_sub_two_cos r, hL]
  have hcosMu : sinSq r = ((2 - 2 * Real.cos Mu : ℝ) : ℂ) := by
    have h : Real.cos Mu = Real.cos (Real.pi * r ^ 2 - 2 * Real.pi) := by rw [hMu, hL]
    rw [sinSq_eq_two_sub_two_cos_sub r, h]
  set F : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  have hargE : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t
    congr 1
    rw [hL]; push_cast; ring
  have hF_eq : F = fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    funext t
    simp only [hF]
    rw [hargE t]
  set P : ℝ → ℂ := fun t => (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hP
  set Q : ℝ → ℂ := fun t => (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ)) with hQ
  have hAe_eq : ∀ t : ℝ, Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) = P t + Q t := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hMu, hL]
      push_cast
      ring
    simp only [Aexp, hP, hQ]
    rw [add_mul, add_mul]
    rw [show (Complex.exp (2 * Real.pi * t) * (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ))
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hFint : IntegrableOn F (Set.Ioi 0) := by rw [hF]; exact hInt
  have hFint1 : IntegrableOn F (Set.Ioi 1) := hFint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hFint01 : IntegrableOn F (Set.Ioc 0 1) := hFint.mono_set Set.Ioc_subset_Ioi_self
  -- integrability of the tail `K - A`, from the local two-regime tail estimate
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_Kfun ℓ d hd τ
  have hmeasA : Measurable (fun t : ℝ => Aexp G τ t) := by unfold Aexp; fun_prop
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(L : ℂ) * (t : ℂ))) := by fun_prop
  have hDom : IntegrableOn (fun t : ℝ => C * Real.exp (Real.pi * T₀) * 2 ^ M
      * (t ^ M * Real.exp (-((Real.pi + L) * t)))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_const_mul_real
      (integrableOn_rpow_mul_exp_neg_mul_Ioi M (Real.pi + L) (by linarith))
      (C * Real.exp (Real.pi * T₀) * 2 ^ M)
  have hDiffInt : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) := by
    refine Integrable.mono' hDom ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have hb := hpoly τ t hτK ht1
    have h2 : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
      calc (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
        _ = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) (by linarith)
    have h3 : Real.exp (-(Real.pi * (t - T₀)))
        = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t)) := by
      rw [show -(Real.pi * (t - T₀)) = Real.pi * T₀ + -(Real.pi * t) by ring, Real.exp_add]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(L : ℂ) * (t : ℂ)).re = -(L * t) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      ring
    rw [hre]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖ * Real.exp (-(L * t))
        ≤ (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) * Real.exp (-(L * t)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = (C * Real.exp (Real.pi * T₀))
            * ((1 + t) ^ M * (Real.exp (-(Real.pi * t)) * Real.exp (-(L * t)))) := by
          rw [h3]; ring
      _ ≤ (C * Real.exp (Real.pi * T₀))
            * ((2 ^ M * t ^ M) * (Real.exp (-(Real.pi * t)) * Real.exp (-(L * t)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (C * Real.exp (Real.pi * T₀) * 2 ^ M)
            * (t ^ M * Real.exp (-((Real.pi + L) * t))) := by
          rw [show Real.exp (-((Real.pi + L) * t))
              = Real.exp (-(Real.pi * t)) * Real.exp (-(L * t)) by
                rw [← Real.exp_add]; congr 1; ring]
          ring
  have hAeInt : IntegrableOn (fun t : ℝ => Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
      (Set.Ioi 1) := by
    have h1 : IntegrableOn (fun t : ℝ => F t - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi 1) :=
      Integrable.sub hFint1 hDiffInt
    refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
    rw [hF_eq]
    ring
  -- the two moment integrals
  have hPint : IntegrableOn P (Set.Ioi 1) := by
    rw [hP]
    exact integrableOn_affine_mul_exp_neg_mul_complex L hLpos (G 0 0 τ) (G 0 1 τ)
  have hPval : ∫ t in Set.Ioi (1 : ℝ), P t
      = G 0 0 τ * (Complex.exp (-(L : ℂ)) / (L : ℂ))
        + (Complex.I * G 0 1 τ)
          * (Complex.exp (-(L : ℂ)) * ((L : ℂ) + 1) / (L : ℂ) ^ 2) := by
    rw [hP]
    exact integral_affine_mul_exp_neg_mul_Ioi_one hLpos (G 0 0 τ) (G 0 1 τ)
  have hmain : sinSq r * (∫ t in Set.Ioi (1 : ℝ),
        Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))) = highPart G τ r := by
    by_cases hMu_pos : 0 < Mu
    · have hQint : IntegrableOn Q (Set.Ioi 1) := by
        rw [hQ]
        exact integrableOn_affine_mul_exp_neg_mul_complex Mu hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hQval : ∫ t in Set.Ioi (1 : ℝ), Q t
          = G 1 0 τ * (Complex.exp (-(Mu : ℂ)) / (Mu : ℂ))
            + (Complex.I * G 1 1 τ)
              * (Complex.exp (-(Mu : ℂ)) * ((Mu : ℂ) + 1) / (Mu : ℂ) ^ 2) := by
        rw [hQ]
        exact integral_affine_mul_exp_neg_mul_Ioi_one hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hAeval : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = (∫ t in Set.Ioi (1 : ℝ), P t) + ∫ t in Set.Ioi (1 : ℝ), Q t := by
        rw [← integral_add hPint hQint]
        exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => hAe_eq t)
      rw [hAeval, hPval, hQval, mul_add,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        sinSq_mul_closed hMu_pos.ne' hcosMu (Complex.exp (-(Mu : ℂ))) (G 1 0 τ)
          (Complex.I * G 1 1 τ),
        highPart_eq_closed, hMu, hL]
      ring
    · have hMu_nonpos : Mu ≤ 0 := not_lt.mp hMu_pos
      have hQint : IntegrableOn Q (Set.Ioi 1) := by
        have h1 : IntegrableOn (fun t : ℝ =>
            Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) - P t) (Set.Ioi 1) :=
          Integrable.sub hAeInt hPint
        refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
        rw [hAe_eq t]
        ring
      have hG10 : G 1 0 τ = 0 ∧ G 1 1 τ = 0 :=
        eq_zero_of_integrableOn_affine_mul_exp_neg hMu_nonpos hQint
      have hAevalP : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = ∫ t in Set.Ioi (1 : ℝ), P t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        rw [hAe_eq t, hQ, hG10.1, hG10.2]
        ring
      rw [hAevalP, hPval,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        highPart_eq_closed, hG10.1, hG10.2, hL]
      ring
  -- the telescoping
  have hsplit0 : ∫ t in Set.Ioi (0 : ℝ), F t
      = (∫ t in (0 : ℝ)..1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t := by
    have hunion : ∫ t in Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ), F t
        = (∫ t in Set.Ioc (0 : ℝ) 1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2)))
        measurableSet_Ioi hFint01 hFint1
    have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h3)
        · exact h1
        · exact lt_trans zero_lt_one h3
      · intro h1
        by_cases h2 : x ≤ 1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (lt_of_not_ge h2)
    rw [hset] at hunion
    rw [hunion, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsplit1 : ∫ t in Set.Ioi (1 : ℝ), F t
      = (∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
        + ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [← integral_add hAeInt hDiffInt]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [hF_eq]; ring)
  have htruncIoi : ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))
      = ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0)).symm
  have hlow : layerLow ℓ d τ r = sinSq r * ∫ t in (0 : ℝ)..1, F t := by
    rw [layerLow, hF]
  have htrunc : layerTrunc G ℓ d τ r
      = sinSq r * ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [layerTrunc]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ici (fun t _ => by rw [hargE t])
  rw [show Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r
      = sinSq r * ∫ t in Set.Ioi (0 : ℝ), F t from by
        rw [Work.Kernels.kernelTransform, sinSq, hF]]
  rw [paperLayer, hlow, htrunc, htruncIoi, ← hmain, hsplit0, hsplit1]
  ring

end Work.Asymptotics.Compact
