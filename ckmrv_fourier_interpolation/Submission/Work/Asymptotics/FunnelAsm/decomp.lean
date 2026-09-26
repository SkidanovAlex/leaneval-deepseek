/-
# The telescoping decomposition of the CKMRV layer on the funnel

This file proves `Work.Asymptotics.FunnelAsm.decomp`:

  `paperLayer (Gcusp ℓ d) ℓ d τ r = PSum ℓ d τ r`

for `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and `r ≠ 0` in the convergence region
`d = 8 ∨ 2 < r²`, where `PSum = layerLow + sinSq·(preT + spikeT + tailT) + highTailClosed`.

The proof is the telescoping of CKMRV §5.2: `layerTrunc = sinSq·∫_1^∞(K-𝒢)e^{-λt}` is split at
`Im τ ∓ 1` (the pieces are `preT`, `spikeT` and `tailT`, with the two `𝒢`-integrals from the
closed forms `highPart_eq_integral` and `highTailClosed_eq_integral` cancelling); the two closed
forms themselves are proved in `Submission/Work/Asymptotics/FunnelAsm/aexpClosed.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.FunnelAsm.aexpClosed
import Submission.Work.Asymptotics.FunnelAsm.tailGcuspW
import Submission.Work.Asymptotics.HalfFunnel.funnelPreDeclash
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

namespace Work.Asymptotics.FunnelAsm

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

noncomputable section

/-! ## The Gaussian norm -/

lemma norm_exp_gauss (r t : ℝ) :
    ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
      = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [Complex.norm_exp]
  have hcast : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = -(((Real.pi * r ^ 2 * t : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hcast, Complex.neg_re, Complex.ofReal_re]

lemma continuous_exp_gauss (r : ℝ) :
    Continuous (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
  refine Complex.continuous_exp.comp ?_
  fun_prop

/-! ## Integrability of the two integrands on the windows -/

lemma integrableOn_kappa_window (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} {r : ℝ} (hτ : Funnel τ) (hr : r ≠ 0) (hreg : d = 8 ∨ 2 < r ^ 2) :
    IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 1 (τ.im - 1)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := (HalfFunnel.funnelPreDeclash ℓ d hd).1
  have hbdy : ∀ t : ℝ, 1 ≤ t → t ≤ τ.im - 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp ((if d = 8 then 0 else 2 * Real.pi) * t) * Real.exp (-(Real.pi * r ^ 2 * t)) := by
    intro t ht1 ht2
    rw [norm_mul, norm_exp_gauss]
    have hK := hb τ t hτ.1 hτ.2 ht1 ht2
    have hexpnn : 0 ≤ Real.exp (-(Real.pi * r ^ 2 * t)) := Real.exp_nonneg _
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp ((if d = 8 then 0 else 2 * Real.pi) * t))
          * Real.exp (-(Real.pi * r ^ 2 * t)) :=
          mul_le_mul_of_nonneg_right hK hexpnn
      _ = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp ((if d = 8 then 0 else 2 * Real.pi) * t)
            * Real.exp (-(Real.pi * r ^ 2 * t)) := by ring
  set g : ℝ → ℝ := fun t => C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      * Real.exp ((if d = 8 then 0 else 2 * Real.pi) * t)
      * Real.exp (-(Real.pi * r ^ 2 * t)) with hg
  have hgcont : Continuous g := by
    rw [hg]; fun_prop
  have hgint : IntegrableOn g (Set.Ioc 1 (τ.im - 1)) :=
    (hgcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  refine Integrable.mono' (g := g) hgint
    ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (continuous_exp_gauss r).measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [hg]
  exact hbdy t ht.1.le ht.2

/-! ## The pole bound and the `Aexp` split -/

lemma norm_pole_sum_le {τ : UpperHalfPlane} (hτ : Funnel τ) (c₁ c₂ : ℂ) (t : ℝ) :
    ‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
      + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖
      ≤ ‖c₁‖ / (1 - τ.re) + ‖c₂‖ / (1 + τ.re) := by
  have hre1 : 0 < 1 - τ.re := by have h := (mem_DomainD.mp hτ.1).2.1; linarith
  have hre2 : 0 < 1 + τ.re := by have h := (mem_DomainD.mp hτ.1).1; linarith
  have hz1 : 1 - τ.re ≤ ‖(t : ℂ) * Complex.I - ((τ : ℂ) - 1)‖ := by
    have h1 : ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)).re = 1 - τ.re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, mul_one, sub_zero, zero_sub,
        UpperHalfPlane.coe_re]
      ring
    have h2 : |((t : ℂ) * Complex.I - ((τ : ℂ) - 1)).re| = 1 - τ.re := by
      rw [h1, abs_of_pos hre1]
    rw [← h2]
    exact Complex.abs_re_le_norm _
  have hz2 : 1 + τ.re ≤ ‖(t : ℂ) * Complex.I - ((τ : ℂ) + 1)‖ := by
    have h1 : ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)).re = -(1 + τ.re) := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, mul_one,
        sub_zero, zero_sub, UpperHalfPlane.coe_re]
      ring
    have h2 : |((t : ℂ) * Complex.I - ((τ : ℂ) + 1)).re| = 1 + τ.re := by
      rw [h1, abs_neg, abs_of_pos hre2]
    rw [← h2]
    exact Complex.abs_re_le_norm _
  have hb1 : ‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))‖ ≤ ‖c₁‖ / (1 - τ.re) := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hre1 hz1
  have hb2 : ‖c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖ ≤ ‖c₂‖ / (1 + τ.re) := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hre2 hz2
  exact le_trans (norm_add_le _ _) (add_le_add hb1 hb2)

/-- The split of the `Aexp`-integrand into the `λ`- and the `μ`-exponential parts. -/
lemma aexp_split (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r t : ℝ) :
    Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ)
          * Complex.exp (-(((Real.pi * r ^ 2 : ℝ)) : ℂ) * (t : ℂ))
        + (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ) * (t : ℂ)) := by
  have h1 : Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(((Real.pi * r ^ 2 : ℝ)) : ℂ) * (t : ℂ)) := by
    congr 1; push_cast; ring
  have hexp : Complex.exp (2 * Real.pi * t)
        * Complex.exp (-(((Real.pi * r ^ 2 : ℝ)) : ℂ) * (t : ℂ))
      = Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [Aexp, Fin.isValue]
  rw [h1, add_mul, add_mul]
  rw [show Complex.exp (2 * Real.pi * t) * (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
        * Complex.exp (-(((Real.pi * r ^ 2 : ℝ)) : ℂ) * (t : ℂ))
      = (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
        * (Complex.exp (2 * Real.pi * t)
            * Complex.exp (-(((Real.pi * r ^ 2 : ℝ)) : ℂ) * (t : ℂ))) from by ring, hexp]

/-! ## Integrability of the spike piece -/

lemma integrableOn_kappa_spike (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} {r : ℝ} (hτ : Funnel τ) (hr : r ≠ 0) (hreg : d = 8 ∨ 2 < r ^ 2) :
    IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc (τ.im - 1) (τ.im + 1)) := by
  obtain ⟨c₁, c₂, C, N, M, hC, hN, hM, hc₁, hc₂, hb⟩ := (HalfFunnel.funnelPreDeclash ℓ d hd).2
  have hbdy : ∀ t : ℝ, τ.im - 1 ≤ t → t ≤ τ.im + 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ (‖c₁‖ / (1 - τ.re) + ‖c₂‖ / (1 + τ.re)
            + C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
          * Real.exp (-(Real.pi * r ^ 2 * t)) := by
    intro t ht1 ht2
    rw [norm_mul, norm_exp_gauss]
    have hK : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
            + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := hb τ t hτ.1 hτ.2 ht1 ht2
    have hpole : ‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
        + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖
        ≤ ‖c₁‖ / (1 - τ.re) + ‖c₂‖ / (1 + τ.re) := norm_pole_sum_le hτ c₁ c₂ t
    have hsplit : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        ≤ (‖c₁‖ / (1 - τ.re) + ‖c₂‖ / (1 + τ.re))
          + C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
      have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ ‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
              + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖
            + C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
        have h := norm_add_le (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
            + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
              + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))))
        have heq : (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
              + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))
            + (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))
                + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))))
            = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t := by ring
        rw [heq] at h
        linarith [h, hK]
      linarith [h1, hpole]
    exact mul_le_mul_of_nonneg_right hsplit (Real.exp_nonneg _)
  -- bound `‖c₁‖ ≤ C`, `‖c₂‖ ≤ C` are available; use the constant `Cp` for the polynomial part
  have hbound1 : ‖c₁‖ / (1 - τ.re) ≤ C / (1 - τ.re) :=
    div_le_div_of_nonneg_right hc₁ (le_of_lt (by
      have h := (mem_DomainD.mp hτ.1).2.1; linarith))
  have hbound2 : ‖c₂‖ / (1 + τ.re) ≤ C / (1 + τ.re) :=
    div_le_div_of_nonneg_right hc₂ (le_of_lt (by
      have h := (mem_DomainD.mp hτ.1).1; linarith))
  -- the global dominator
  set g : ℝ → ℝ := fun t => (C / (1 - τ.re) + C / (1 + τ.re)
      + C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) * Real.exp (-(Real.pi * r ^ 2 * t)) with hg
  have hgcont : Continuous g := by rw [hg]; fun_prop
  have hgint : IntegrableOn g (Set.Ioc (τ.im - 1) (τ.im + 1)) :=
    (hgcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  refine Integrable.mono' (g := g) hgint
    ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (continuous_exp_gauss r).measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [hg]
  refine le_trans (hbdy t (le_of_lt ht.1) ht.2) ?_
  exact mul_le_mul_of_nonneg_right (by linarith [hbound1, hbound2]) (Real.exp_nonneg _)

/-! ## Integrability of the `Aexp` pieces -/

lemma integrableOn_A_finite (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (r a b : ℝ) :
    IntegrableOn (fun t : ℝ => Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (Set.Ioc a b) := by
  have hc : Continuous (fun t : ℝ => Aexp G τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    refine Continuous.mul ?_ (continuous_exp_gauss r)
    unfold Aexp; fun_prop
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

lemma integrableOn_A_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} {r : ℝ} (hτ : Funnel τ) (hr : r ≠ 0) (hreg : d = 8 ∨ 2 < r ^ 2) :
    IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi (τ.im + 1)) := by
  have hB : (1 : ℝ) ≤ τ.im + 1 := by have := hτ.2; linarith
  have hLpos : 0 < Real.pi * r ^ 2 := by
    rw [sq]; exact mul_pos Real.pi_pos (mul_self_pos.mpr hr)
  rcases lt_or_ge 0 (Real.pi * r ^ 2 - 2 * Real.pi) with hμpos | hμnp
  · have hP := integrableOn_affine_exp_neg_Ioi' hLpos hB (Gcusp ℓ d 0 0 τ) (Gcusp ℓ d 0 1 τ)
    have hQ := integrableOn_affine_exp_neg_Ioi' hμpos hB (Gcusp ℓ d 1 0 τ) (Gcusp ℓ d 1 1 τ)
    refine IntegrableOn.congr_fun (hP.add hQ) (fun t _ => ?_) measurableSet_Ioi
    rw [aexp_split]
    simp only [Pi.add_apply]
  · have hpair : Gcusp ℓ d 1 0 τ = 0 ∧ Gcusp ℓ d 1 1 τ = 0 := by
      by_cases h8 : d = 8
      · exact ⟨gcusp_one_zero ℓ h8 0 τ, gcusp_one_zero ℓ h8 1 τ⟩
      · exfalso
        have h2 : 2 < r ^ 2 := by
          rcases hreg with h | h
          · exact absurd h h8
          · exact h
        have : (0 : ℝ) < Real.pi * r ^ 2 - 2 * Real.pi := by nlinarith [Real.pi_pos]
        linarith
    obtain ⟨h10, h11⟩ := hpair
    have hP := integrableOn_affine_exp_neg_Ioi' hLpos hB (Gcusp ℓ d 0 0 τ) (Gcusp ℓ d 0 1 τ)
    refine IntegrableOn.congr_fun hP (fun t _ => ?_) measurableSet_Ioi
    rw [aexp_split, h10, h11]
    ring

lemma integrableOn_tail_diff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} {r : ℝ} (hτ : Funnel τ) (hr : r ≠ 0) (hreg : d = 8 ∨ 2 < r ^ 2) :
    IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp (Gcusp ℓ d) τ t)
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi (τ.im + 1)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := funnelKernelTailGcuspW ℓ d hd
  have hB : (1 : ℝ) ≤ τ.im + 1 := by have := hτ.2; linarith
  have hcpos : 0 < Real.pi + Real.pi * r ^ 2 := by
    have h2 : (0:ℝ) < r ^ 2 := by rw [sq]; exact mul_self_pos.mpr hr
    exact add_pos Real.pi_pos (mul_pos Real.pi_pos h2)
  have hpow : ∀ t : ℝ, 1 ≤ t → (1 + t) ^ M ≤ (2:ℝ) ^ M * t ^ M := by
    intro t ht
    have h1 : (0:ℝ) ≤ 1 + t := by linarith
    have h2 : 1 + t ≤ 2 * t := by linarith
    have h3 : (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow h1 h2 hM
    rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : (0:ℝ) ≤ t)] at h3
  set g : ℝ → ℝ := fun t => (C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * τ.im)
      * (2:ℝ) ^ M) * (t ^ M * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t))) with hg
  have hgint : IntegrableOn g (Set.Ioi (τ.im + 1)) := by
    rw [hg]
    exact ((integrableOn_rpow_mul_exp_neg_mul_Ioi M (Real.pi + Real.pi * r ^ 2) hcpos).mono_set
      (Set.Ioi_subset_Ioi hB)).const_mul _
  refine Integrable.mono' (g := g) hgint
    (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub (by unfold Aexp; fun_prop)).mul
      (continuous_exp_gauss r).measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [hg, norm_mul, norm_exp_gauss]
  have htB : τ.im + 1 ≤ t := ht.le
  have ht1 : (1:ℝ) ≤ t := by linarith
  have hK := hb τ t hτ htB
  have hexp : Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (-(Real.pi * r ^ 2 * t))
      = Real.exp (Real.pi * τ.im) * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hstep1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (Real.pi * τ.im) * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t)) := by
    have h := mul_le_mul_of_nonneg_right hK (Real.exp_nonneg (-(Real.pi * r ^ 2 * t)))
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * (t - τ.im)))) * Real.exp (-(Real.pi * r ^ 2 * t)) := h
      _ = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (-(Real.pi * r ^ 2 * t))) := by ring
      _ = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * (Real.exp (Real.pi * τ.im) * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t))) := by
          rw [hexp]
      _ = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (Real.pi * τ.im) * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t)) := by ring
  have hstep2 : C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (Real.pi * τ.im) * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t))
      ≤ (C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * τ.im) * (2:ℝ) ^ M)
        * (t ^ M * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t))) := by
    have h2 : 0 ≤ Real.exp (-((Real.pi + Real.pi * r ^ 2) * t)) := Real.exp_nonneg _
    have h3 := hpow t ht1
    have h4 : C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (Real.pi * τ.im)
        ≤ C * (Work.Kernels.scale τ) ^ N * ((2:ℝ) ^ M * t ^ M)
          * Real.exp (Real.pi * τ.im) := by
      have h1nn : (0:ℝ) ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * τ.im) :=
        mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N))
          (Real.exp_nonneg _)
      have := mul_le_mul_of_nonneg_left h3 h1nn
      calc C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (Real.pi * τ.im)
          = (C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * τ.im)) * (1 + t) ^ M := by ring
        _ ≤ (C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * τ.im))
              * ((2:ℝ) ^ M * t ^ M) := this
        _ = C * (Work.Kernels.scale τ) ^ N * ((2:ℝ) ^ M * t ^ M)
              * Real.exp (Real.pi * τ.im) := by ring
    calc C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * τ.im) * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t))
        = (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (Real.pi * τ.im))
            * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t)) := by ring
      _ ≤ (C * (Work.Kernels.scale τ) ^ N * ((2:ℝ) ^ M * t ^ M)
              * Real.exp (Real.pi * τ.im))
            * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t)) :=
          mul_le_mul_of_nonneg_right h4 h2
      _ = (C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * τ.im) * (2:ℝ) ^ M)
            * (t ^ M * Real.exp (-((Real.pi + Real.pi * r ^ 2) * t))) := by ring
  exact le_trans hstep1 hstep2


/-! ## The telescoping -/

lemma wgt_sq (r t : ℝ) :
    Work.Asymptotics.wgt (r ^ 2) t = Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  rw [Work.Asymptotics.wgt_eq_exp]
  congr 1
  push_cast
  ring

lemma aeeq_Ioi_Ici : Set.Ioi (1 : ℝ) =ᵐ[volume] Set.Ici (1 : ℝ) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · rw [Set.diff_eq_empty.mpr Set.Ioi_subset_Ici_self]
    simp
  · refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton 1)
    intro x hx
    simp only [Set.mem_singleton_iff]
    exact le_antisymm (not_lt.mp hx.2) hx.1

theorem decomp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → r ≠ 0 → (d = 8 ∨ 2 < r ^ 2) →
      paperLayer (Gcusp ℓ d) ℓ d τ r = PSum ℓ d τ r := by
  intro τ r hτ hr hreg
  have hY1 : (1 : ℝ) ≤ τ.im - 1 := by have := hτ.2; linarith
  have hY3 : (1 : ℝ) ≤ τ.im + 1 := by have := hτ.2; linarith
  set κ : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hκ
  set α : ℝ → ℂ := fun t => Aexp (Gcusp ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hα
  have hsub_eq : ∀ t : ℝ, (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Aexp (Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = κ t - α t := by intro t; rw [hκ, hα]; ring
  -- integrability
  have hκ1 : IntegrableOn κ (Set.Ioc 1 (τ.im - 1)) :=
    integrableOn_kappa_window ℓ d hd hτ hr hreg
  have hκ2 : IntegrableOn κ (Set.Ioc (τ.im - 1) (τ.im + 1)) :=
    integrableOn_kappa_spike ℓ d hd hτ hr hreg
  have hα1 : IntegrableOn α (Set.Ioc 1 (τ.im - 1)) :=
    integrableOn_A_finite (Gcusp ℓ d) τ r 1 (τ.im - 1)
  have hα2 : IntegrableOn α (Set.Ioc (τ.im - 1) (τ.im + 1)) :=
    integrableOn_A_finite (Gcusp ℓ d) τ r (τ.im - 1) (τ.im + 1)
  have hα3 : IntegrableOn α (Set.Ioi (τ.im + 1)) :=
    integrableOn_A_tail ℓ d hd hτ hr hreg
  have hsub3 : IntegrableOn (fun t : ℝ => κ t - α t) (Set.Ioi (τ.im + 1)) := by
    rw [show (fun t : ℝ => κ t - α t) = fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp (Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) from
      funext (fun t => (hsub_eq t).symm)]
    exact integrableOn_tail_diff ℓ d hd hτ hr hreg
  -- the four pieces of the layer
  have hpre : preT ℓ d τ (r ^ 2) = ∫ t in Set.Ioc 1 (τ.im - 1), κ t := by
    rw [preT, intervalIntegral.integral_of_le hY1]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by
      show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.wgt (r ^ 2) t = κ t
      rw [hκ, wgt_sq])
  have hspike : spikeT ℓ d τ (r ^ 2) = ∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), κ t := by
    rw [spikeT, intervalIntegral.integral_of_le (by linarith : τ.im - 1 ≤ τ.im + 1)]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by
      show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.wgt (r ^ 2) t = κ t
      rw [hκ, wgt_sq])
  have htail : tailT ℓ d τ (r ^ 2) = ∫ t in Set.Ioi (τ.im + 1), (κ t - α t) := by
    rw [tailT]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      show (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
        * Work.Asymptotics.wgt (r ^ 2) t = κ t - α t
      rw [wgt_sq, hsub_eq t])
  have htrunc : layerTrunc (Gcusp ℓ d) ℓ d τ r = sinSq r * ∫ t in Set.Ici 1, (κ t - α t) := by
    rw [layerTrunc]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ici (fun t _ => hsub_eq t)
  have hhighp : highPart (Gcusp ℓ d) τ r = sinSq r * ∫ t in Set.Ioi 1, α t :=
    highPart_eq_integral ℓ d hd hτ hr hreg
  have hhight : highTailClosed ℓ d τ r = sinSq r * ∫ t in Set.Ioi (τ.im + 1), α t :=
    highTailClosed_eq_integral ℓ d hd hτ hr hreg
  -- the union identity
  have hset : Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1) ∪ Set.Ioi (τ.im + 1)
      = Set.Ioi (1 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h3)
      · exact h1
      · linarith
      · linarith
    · intro h
      rcases lt_trichotomy t (τ.im - 1) with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨h, le_of_lt hlt⟩)
      · exact Or.inl (Or.inl ⟨h, le_of_eq heq⟩)
      · rcases lt_trichotomy t (τ.im + 1) with hlt2 | heq2 | hgt2
        · exact Or.inl (Or.inr ⟨hgt, le_of_lt hlt2⟩)
        · exact Or.inl (Or.inr ⟨hgt, le_of_eq heq2⟩)
        · exact Or.inr hgt2
  have hd12 : Disjoint (Set.Ioc (1:ℝ) (τ.im - 1)) (Set.Ioc (τ.im - 1) (τ.im + 1)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2.1))
  have hd3 : Disjoint (Set.Ioc (1:ℝ) (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1))
      (Set.Ioi (τ.im + 1)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => by
      have hx2' : τ.im + 1 < x := hx2
      rcases hx1 with hx | hx
      · exact absurd hx.2 (not_le.mpr (lt_trans (by linarith : τ.im - 1 < τ.im + 1) hx2'))
      · exact absurd hx.2 (not_le.mpr hx2'))
  have hunion : ∫ t in Set.Ioi 1, (κ t - α t)
      = (∫ t in Set.Ioc 1 (τ.im - 1), (κ t - α t))
        + (∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), (κ t - α t))
        + (∫ t in Set.Ioi (τ.im + 1), (κ t - α t)) := by
    rw [← hset]
    have hA : ∫ t in Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1), (κ t - α t)
        = (∫ t in Set.Ioc 1 (τ.im - 1), (κ t - α t))
          + ∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), (κ t - α t) :=
      MeasureTheory.setIntegral_union hd12 measurableSet_Ioc (hκ1.sub hα1) (hκ2.sub hα2)
    have hB : ∫ t in (Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1))
          ∪ Set.Ioi (τ.im + 1), (κ t - α t)
        = (∫ t in Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1), (κ t - α t))
          + ∫ t in Set.Ioi (τ.im + 1), (κ t - α t) :=
      MeasureTheory.setIntegral_union hd3 measurableSet_Ioi
        (IntegrableOn.union (hκ1.sub hα1) (hκ2.sub hα2)) hsub3
    rw [hB, hA]
  have hunionA : ∫ t in Set.Ioi 1, α t
      = (∫ t in Set.Ioc 1 (τ.im - 1), α t) + (∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), α t)
        + (∫ t in Set.Ioi (τ.im + 1), α t) := by
    rw [← hset]
    have hA : ∫ t in Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1), α t
        = (∫ t in Set.Ioc 1 (τ.im - 1), α t)
          + ∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), α t :=
      MeasureTheory.setIntegral_union hd12 measurableSet_Ioc hα1 hα2
    have hB : ∫ t in (Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1))
          ∪ Set.Ioi (τ.im + 1), α t
        = (∫ t in Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1), α t)
          + ∫ t in Set.Ioi (τ.im + 1), α t :=
      MeasureTheory.setIntegral_union hd3 measurableSet_Ioi
        (IntegrableOn.union hα1 hα2) hα3
    rw [hB, hA]
  have hci : ∫ t in Set.Ici 1, (κ t - α t) = ∫ t in Set.Ioi 1, (κ t - α t) :=
    MeasureTheory.setIntegral_congr_set aeeq_Ioi_Ici.symm
  -- the integral identity
  have hkey : (∫ t in Set.Ici 1, (κ t - α t)) + (∫ t in Set.Ioi 1, α t)
      = (∫ t in Set.Ioc 1 (τ.im - 1), κ t) + (∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), κ t)
        + (∫ t in Set.Ioi (τ.im + 1), (κ t - α t))
        + (∫ t in Set.Ioi (τ.im + 1), α t) := by
    rw [hci, hunion, hunionA, integral_sub hκ1 hα1, integral_sub hκ2 hα2]
    ring
  -- conclusion
  have hg : sinSq r * (∫ t in Set.Ici 1, (κ t - α t)) + sinSq r * (∫ t in Set.Ioi 1, α t)
      = sinSq r * ((∫ t in Set.Ioc 1 (τ.im - 1), κ t)
            + (∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), κ t)
            + (∫ t in Set.Ioi (τ.im + 1), (κ t - α t)))
        + sinSq r * (∫ t in Set.Ioi (τ.im + 1), α t) := by
    rw [← mul_add, hkey]
    ring
  rw [paperLayer, PSum, htrunc, hpre, hspike, htail, hhighp, hhight]
  have hstep : (layerLow ℓ d τ r + sinSq r * (∫ t in Set.Ici 1, (κ t - α t)))
        + sinSq r * (∫ t in Set.Ioi 1, α t)
      = layerLow ℓ d τ r + (sinSq r * (∫ t in Set.Ici 1, (κ t - α t))
          + sinSq r * (∫ t in Set.Ioi 1, α t)) := by ring
  rw [hstep, hg]
  ring


end

end Work.Asymptotics.FunnelAsm
