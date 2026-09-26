/-
# The telescoping decomposition of the CKMRV layer on the funnel

This file provides the analytic core of the telescoping decomposition
`paperLayer (Gcusp ℓ d) ℓ d τ r = PSum ℓ d τ r` on the funnel: the moment integrals on a general
half line `(B,∞)` and the `psi1`-regularised closed form
`Work.Asymptotics.FunnelAsm.aexp_integral_closed` of `sinSq r · ∫_B^∞ 𝒢(τ,it)e^{-λt}dt`,
together with the two specialisations

* `highPart_eq_integral` (`B = 1`) and
* `highTailClosed_eq_integral` (`B = Im τ + 1`).
-/
import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.FunnelAsm.tailGcuspW

namespace Work.Asymptotics.FunnelAsm

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

noncomputable section

/-! ## The moment integrals on a general half line -/

lemma hasDerivAt_exp_neg_mul' (c : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ)))
      (Complex.exp (-(c : ℂ) * (x : ℂ)) * (-(c : ℂ))) x := by
  have hinner : HasDerivAt (fun y : ℝ => -(c : ℂ) * (y : ℂ)) (-(c : ℂ)) x := by
    simpa using ((HasDerivAt.ofReal_comp (hasDerivAt_id x)).const_mul (-(c : ℂ)))
  exact (Complex.hasDerivAt_exp (-(c : ℂ) * (x : ℂ))).comp x hinner

lemma exp_neg_mul_ofReal' (c y : ℝ) :
    Complex.exp (-(c : ℂ) * (y : ℂ)) = ((Real.exp (-(c * y)) : ℝ) : ℂ) := by
  rw [show -(c : ℂ) * (y : ℂ) = ((-(c * y) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]

lemma integrableOn_exp_neg_mul_complex' (c B : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi B hc) ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    rw [Complex.norm_exp]
    have hre : (-(c : ℂ) * (t : ℂ)).re = -(c * t) := by simp
    rw [hre]
    exact le_of_eq (by ring_nf)

lemma integrableOn_id_mul_exp_neg_mul_complex' (c B : ℝ) (hc : 0 < c) (hB : 1 ≤ B) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) := by
  have hdom : IntegrableOn (fun t : ℝ => t * Real.exp (-(c * t))) (Set.Ioi B) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_Ioi 1 c hc
    simpa [Real.rpow_one] using h.mono_set (Set.Ioi_subset_Ioi hB)
  refine Integrable.mono' hdom ?_ ?_
  · exact (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (0 : ℝ) < t := lt_of_lt_of_le (show (0 : ℝ) < B by linarith)
      (le_of_lt (Set.mem_Ioi.mp ht))
    simp [Complex.norm_exp, abs_of_pos ht1]

/-- `exp (-(c y)) → 0` at `+∞` for `c > 0`, in `ℂ`. -/
lemma tendsto_exp_neg_mul_atTop (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ))) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => -(c * y)) Filter.atTop Filter.atBot :=
    (Filter.Tendsto.const_mul_atTop_of_neg (show -c < 0 by linarith) Filter.tendsto_id).congr'
      (Filter.Eventually.of_forall (fun y => by simp))
  have h2 : Filter.Tendsto (fun y : ℝ => Real.exp (-(c * y))) Filter.atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h1
  have h3 : Filter.Tendsto (fun y : ℝ => ((Real.exp (-(c * y)) : ℝ) : ℂ)) Filter.atTop
      (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto 0).comp h2
  simpa [exp_neg_mul_ofReal', Complex.ofReal_zero] using h3

/-- `y · exp (-(c y)) → 0` at `+∞` for `c > 0`, in `ℂ`. -/
lemma tendsto_id_mul_exp_neg_mul_atTop (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => (y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ))) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => y * Real.exp (-(c * y))) Filter.atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
    simpa [Real.rpow_one] using this
  have h3 : Filter.Tendsto (fun y : ℝ => ((y * Real.exp (-(c * y)) : ℝ) : ℂ)) Filter.atTop
      (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto 0).comp h1
  refine h3.congr' ?_
  filter_upwards with y
  rw [exp_neg_mul_ofReal']
  push_cast
  ring

lemma integral_exp_neg_mul_Ioi' {c B : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi B, Complex.exp (-(c : ℂ) * (t : ℂ))
      = Complex.exp (-(c : ℂ) * (B : ℂ)) / (c : ℂ) := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hderiv : ∀ x ∈ Set.Ici B,
      HasDerivAt (fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ))
        (Complex.exp (-(c : ℂ) * (x : ℂ))) x := by
    intro x _
    refine ((hasDerivAt_exp_neg_mul' c x).neg.div_const (c : ℂ)).congr_deriv ?_
    field_simp
  have hint := integrableOn_exp_neg_mul_complex' c B hc
  have htend : Filter.Tendsto (fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ))
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_mul_atTop c hc).neg.div_const (c : ℂ)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun y : ℝ => -(Complex.exp (-(c : ℂ) * (y : ℂ))) / (c : ℂ))
    (f' := fun y : ℝ => Complex.exp (-(c : ℂ) * (y : ℂ))) hderiv hint htend
  rw [h, zero_sub]
  ring

lemma integral_id_mul_exp_neg_mul_Ioi' {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B) :
    ∫ t in Set.Ioi B, (t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ))
      = Complex.exp (-(c : ℂ) * (B : ℂ)) * ((c : ℂ) * (B : ℂ) + 1) / (c : ℂ) ^ 2 := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hderiv : ∀ x ∈ Set.Ici B,
      HasDerivAt (fun y : ℝ => -((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ)) / (c : ℂ)
        + Complex.exp (-(c : ℂ) * (y : ℂ)) / (c : ℂ) ^ 2))
        ((x : ℂ) * Complex.exp (-(c : ℂ) * (x : ℂ))) x := by
    intro x _
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id x))
    have h1 := (hx.mul (hasDerivAt_exp_neg_mul' c x)).div_const (c : ℂ)
    have h2 := (hasDerivAt_exp_neg_mul' c x).div_const ((c : ℂ) ^ 2)
    refine (h1.add h2).neg.congr_deriv ?_
    field_simp
    ring
  have hint := integrableOn_id_mul_exp_neg_mul_complex' c B hc hB
  have htend : Filter.Tendsto (fun y : ℝ => -((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ)) / (c : ℂ)
      + Complex.exp (-(c : ℂ) * (y : ℂ)) / (c : ℂ) ^ 2)) Filter.atTop (𝓝 0) := by
    have h1 := (tendsto_id_mul_exp_neg_mul_atTop c hc).div_const (c : ℂ)
    have h2 := (tendsto_exp_neg_mul_atTop c hc).div_const ((c : ℂ) ^ 2)
    simpa using (h1.add h2).neg
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun y : ℝ => -((y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ)) / (c : ℂ)
      + Complex.exp (-(c : ℂ) * (y : ℂ)) / (c : ℂ) ^ 2))
    (f' := fun y : ℝ => (y : ℂ) * Complex.exp (-(c : ℂ) * (y : ℂ)))
    (a := B) (m := 0) hderiv hint htend
  rw [h, zero_sub, neg_neg]
  field_simp

/-- The two-term affine moment integral on a general half line. -/
lemma integral_affine_mul_exp_neg_mul_Ioi' {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B) (a b : ℂ) :
    ∫ t in Set.Ioi B, (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(c : ℂ) * (t : ℂ))
      = a * (Complex.exp (-(c : ℂ) * (B : ℂ)) / (c : ℂ))
        + (Complex.I * b) * (Complex.exp (-(c : ℂ) * (B : ℂ)) * ((c : ℂ) * (B : ℂ) + 1)
            / (c : ℂ) ^ 2) := by
  have hE := integrableOn_exp_neg_mul_complex' c B hc
  have hI := integrableOn_id_mul_exp_neg_mul_complex' c B hc hB
  have h1 : IntegrableOn (fun t : ℝ => a * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    Integrable.const_mul hE a
  have h2 : IntegrableOn (fun t : ℝ => (Complex.I * b)
      * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ)))) (Set.Ioi B) :=
    Integrable.const_mul hI (Complex.I * b)
  rw [show (∫ t in Set.Ioi B, (a + (t : ℂ) * Complex.I * b)
        * Complex.exp (-(c : ℂ) * (t : ℂ)))
      = ∫ t in Set.Ioi B, (a * Complex.exp (-(c : ℂ) * (t : ℂ))
          + (Complex.I * b) * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ)))) from
      setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring),
    integral_add h1 h2]
  rw [integral_const_mul, integral_exp_neg_mul_Ioi' hc,
    integral_const_mul, integral_id_mul_exp_neg_mul_Ioi' hc hB]


/-! ## The `psi1`-regularised closed forms -/

lemma two_sub_two_cos_mul_div' {c : ℝ} (hc : c ≠ 0) (E : ℂ) :
    ((2 - 2 * Real.cos c : ℝ) : ℂ) * (E / (c : ℂ)) = (c : ℂ) * (psi1 c : ℂ) * E := by
  have h : ((2 - 2 * Real.cos c : ℝ) : ℂ) = (c : ℂ) ^ 2 * (psi1 c : ℂ) := by
    rw [← sq_mul_psi1 c]; push_cast; ring
  rw [h]; field_simp

lemma two_sub_two_cos_mul_div_sq' {c B : ℝ} (hc : c ≠ 0) (E : ℂ) :
    ((2 - 2 * Real.cos c : ℝ) : ℂ) * (E * ((c : ℂ) * (B : ℂ) + 1) / (c : ℂ) ^ 2)
      = (psi1 c : ℂ) * ((c : ℂ) * (B : ℂ) + 1) * E := by
  have h : ((2 - 2 * Real.cos c : ℝ) : ℂ) = (c : ℂ) ^ 2 * (psi1 c : ℂ) := by
    rw [← sq_mul_psi1 c]; push_cast; ring
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [h]
  field_simp
  try ring

lemma sinSq_mul_closed' {r c B : ℝ} (hc : c ≠ 0)
    (hcos : sinSq r = ((2 - 2 * Real.cos c : ℝ) : ℂ)) (E a b : ℂ) :
    sinSq r * (a * (E / (c : ℂ)) + b * (E * ((c : ℂ) * (B : ℂ) + 1) / (c : ℂ) ^ 2))
      = (c : ℂ) * (psi1 c : ℂ) * E * a
        + (psi1 c : ℂ) * ((c : ℂ) * (B : ℂ) + 1) * E * b := by
  rw [hcos, mul_add,
    show ((2 - 2 * Real.cos c : ℝ) : ℂ) * (a * (E / (c : ℂ)))
        = a * (((2 - 2 * Real.cos c : ℝ) : ℂ) * (E / (c : ℂ))) by ring,
    two_sub_two_cos_mul_div' hc E,
    show ((2 - 2 * Real.cos c : ℝ) : ℂ) * (b * (E * ((c : ℂ) * (B : ℂ) + 1) / (c : ℂ) ^ 2))
        = b * (((2 - 2 * Real.cos c : ℝ) : ℂ)
            * (E * ((c : ℂ) * (B : ℂ) + 1) / (c : ℂ) ^ 2)) by ring,
    two_sub_two_cos_mul_div_sq' hc E]
  ring

lemma integrableOn_affine_exp_neg_Ioi' {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B) (a b : ℂ) :
    IntegrableOn (fun t : ℝ => (a + (t : ℂ) * Complex.I * b)
      * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) := by
  have hE := integrableOn_exp_neg_mul_complex' c B hc
  have hI := integrableOn_id_mul_exp_neg_mul_complex' c B hc hB
  have h1 : IntegrableOn (fun t : ℝ => a * Complex.exp (-(c : ℂ) * (t : ℂ))) (Set.Ioi B) :=
    Integrable.const_mul hE a
  have h2 : IntegrableOn (fun t : ℝ => (Complex.I * b)
      * ((t : ℂ) * Complex.exp (-(c : ℂ) * (t : ℂ)))) (Set.Ioi B) :=
    Integrable.const_mul hI (Complex.I * b)
  refine IntegrableOn.congr_fun (h1.add h2) (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

/-- **The closed form of a general `Aexp`-integral on `(B,∞)`**, `psi1`-regularised.

For `B ≥ 1`, `0 < λ = πr²` and (μ = λ - 2π > 0 or `G 1 j = 0`),

`sinSq r · ∫_B^∞ 𝒢(τ,it)e^{-λt}dt
   = λ psi1(λ) e^{-λB}G₀₀ + psi1(λ)(λB+1)e^{-λB}·iG₀₁
     + μ psi1(μ) e^{-μB}G₁₀ + psi1(μ)(μB+1)e^{-μB}·iG₁₁`. -/
lemma aexp_integral_closed (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    {r B : ℝ} (hB : 1 ≤ B) (hr : r ≠ 0)
    (hG1 : Real.pi * r ^ 2 - 2 * Real.pi ≤ 0 → G 1 0 τ = 0 ∧ G 1 1 τ = 0) :
    sinSq r * ∫ t in Set.Ioi B,
        Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = ((Real.pi * r ^ 2 : ℝ) : ℂ) * (psi1 (Real.pi * r ^ 2) : ℂ)
          * Complex.exp (-(((Real.pi * r ^ 2 : ℝ)) : ℂ) * (B : ℂ)) * G 0 0 τ
        + (psi1 (Real.pi * r ^ 2) : ℂ) * ((((Real.pi * r ^ 2 : ℝ)) : ℂ) * (B : ℂ) + 1)
          * Complex.exp (-(((Real.pi * r ^ 2 : ℝ)) : ℂ) * (B : ℂ)) * (Complex.I * G 0 1 τ)
        + (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ)
          * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
          * Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ) * (B : ℂ)) * G 1 0 τ
        + (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
          * ((((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ) * (B : ℂ) + 1)
          * Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ) * (B : ℂ))
          * (Complex.I * G 1 1 τ) := by
  set L : ℝ := Real.pi * r ^ 2 with hL
  set Mu : ℝ := Real.pi * r ^ 2 - 2 * Real.pi with hMu
  have hLpos : 0 < L := by rw [hL]; positivity
  have hcosL : sinSq r = ((2 - 2 * Real.cos L : ℝ) : ℂ) := by
    rw [sinSq_eq_two_sub_two_cos r, hL]
  have hcosMu : sinSq r = ((2 - 2 * Real.cos Mu : ℝ) : ℂ) := by
    rw [sinSq_eq_two_sub_two_cos_sub r, hMu]
  -- the two summands
  set P : ℝ → ℂ := fun t => (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hPdef
  set Q : ℝ → ℂ := fun t => (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ)) with hQdef
  have hexp_arg : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t
    congr 1
    rw [hL]; push_cast; ring
  have hAe_eq : ∀ t : ℝ, Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = P t + Q t := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hMu, hL]; push_cast; ring
    simp only [Aexp, hPdef, hQdef]
    rw [hexp_arg t, add_mul, add_mul,
      show Complex.exp (2 * Real.pi * t) * (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hPint : IntegrableOn P (Set.Ioi B) := by
    rw [hPdef]; exact integrableOn_affine_exp_neg_Ioi' hLpos hB (G 0 0 τ) (G 0 1 τ)
  have hPval : ∫ t in Set.Ioi B, P t
      = G 0 0 τ * (Complex.exp (-(L : ℂ) * (B : ℂ)) / (L : ℂ))
        + (Complex.I * G 0 1 τ) * (Complex.exp (-(L : ℂ) * (B : ℂ))
            * ((L : ℂ) * (B : ℂ) + 1) / (L : ℂ) ^ 2) := by
    rw [hPdef]
    exact integral_affine_mul_exp_neg_mul_Ioi' hLpos hB (G 0 0 τ) (G 0 1 τ)
  rcases lt_or_ge 0 Mu with hMu_pos | hMu_np
  · -- `μ > 0`: both moment integrals converge
    have hQint : IntegrableOn Q (Set.Ioi B) := by
      rw [hQdef]; exact integrableOn_affine_exp_neg_Ioi' hMu_pos hB (G 1 0 τ) (G 1 1 τ)
    have hQval : ∫ t in Set.Ioi B, Q t
        = G 1 0 τ * (Complex.exp (-(Mu : ℂ) * (B : ℂ)) / (Mu : ℂ))
          + (Complex.I * G 1 1 τ) * (Complex.exp (-(Mu : ℂ) * (B : ℂ))
              * ((Mu : ℂ) * (B : ℂ) + 1) / (Mu : ℂ) ^ 2) := by
      rw [hQdef]
      exact integral_affine_mul_exp_neg_mul_Ioi' hMu_pos hB (G 1 0 τ) (G 1 1 τ)
    have hAeval : ∫ t in Set.Ioi B, Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = (∫ t in Set.Ioi B, P t) + ∫ t in Set.Ioi B, Q t := by
      rw [show (∫ t in Set.Ioi B, Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
            = ∫ t in Set.Ioi B, (P t + Q t) from
          setIntegral_congr_fun measurableSet_Ioi (fun t _ => hAe_eq t),
        integral_add hPint hQint]
    rw [hAeval, hPval, hQval, mul_add,
      sinSq_mul_closed' hLpos.ne' hcosL (Complex.exp (-(L : ℂ) * (B : ℂ))) (G 0 0 τ)
        (Complex.I * G 0 1 τ),
      sinSq_mul_closed' hMu_pos.ne' hcosMu (Complex.exp (-(Mu : ℂ) * (B : ℂ))) (G 1 0 τ)
        (Complex.I * G 1 1 τ), hMu, hL]
    ring
  · -- `μ ≤ 0`: the coefficients of `e^{2πt}` vanish
    obtain ⟨h10, h11⟩ := hG1 hMu_np
    have hQzero : Q = fun _ : ℝ => (0 : ℂ) := by
      funext t; rw [hQdef, h10, h11]; ring
    have hQint : IntegrableOn Q (Set.Ioi B) := by
      rw [hQzero]; exact integrableOn_zero
    have hQval : (∫ t in Set.Ioi B, Q t) = 0 := by
      rw [hQzero]; simp
    have hAeval : ∫ t in Set.Ioi B, Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = (∫ t in Set.Ioi B, P t) + ∫ t in Set.Ioi B, Q t := by
      rw [show (∫ t in Set.Ioi B, Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
            = ∫ t in Set.Ioi B, (P t + Q t) from
          setIntegral_congr_fun measurableSet_Ioi (fun t _ => hAe_eq t),
        integral_add hPint hQint]
    rw [hAeval, hQval, add_zero, hPval, h10, h11,
      sinSq_mul_closed' hLpos.ne' hcosL (Complex.exp (-(L : ℂ) * (B : ℂ))) (G 0 0 τ)
        (Complex.I * G 0 1 τ), hMu, hL]
    ring

/-- `Gcusp ℓ 8` has no `e^{2πt}`-row. -/
lemma gcusp_one_zero (ℓ : Work.Kernels.LogLambdaData) {d : ℕ} (hd : d = 8) :
    ∀ (j : Fin 2) (τ : UpperHalfPlane), Gcusp ℓ d 1 j τ = 0 := by
  subst hd
  intro j τ
  fin_cases j <;> simp [Gcusp, Gcusp8]

/-- **The closed form of `highPart` as an integral on `(1,∞)`.** -/
lemma highPart_eq_integral (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} {r : ℝ} (hτ : Funnel τ) (hr : r ≠ 0) (hreg : d = 8 ∨ 2 < r ^ 2) :
    highPart (Gcusp ℓ d) τ r
      = sinSq r * ∫ t in Set.Ioi (1 : ℝ),
          Aexp (Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  have hclosed := aexp_integral_closed (Gcusp ℓ d) τ (B := 1) le_rfl hr (by
    intro hle
    by_cases h8 : d = 8
    · exact ⟨gcusp_one_zero ℓ h8 0 τ, gcusp_one_zero ℓ h8 1 τ⟩
    · exfalso
      have h2 : 2 < r ^ 2 := by
        rcases hreg with h | h
        · exact absurd h h8
        · exact h
      have hpos : 0 < Real.pi * r ^ 2 - 2 * Real.pi := by nlinarith [Real.pi_pos]
      exact absurd hle (not_le.mpr hpos))
  simp only [Complex.ofReal_one, mul_one] at hclosed
  rw [highPart_eq_closed, ← hclosed]

/-- **The closed form of `highTailClosed` as an integral on `(Im τ + 1, ∞)`.** -/
lemma highTailClosed_eq_integral (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} {r : ℝ} (hτ : Funnel τ) (hr : r ≠ 0) (hreg : d = 8 ∨ 2 < r ^ 2) :
    highTailClosed ℓ d τ r
      = sinSq r * ∫ t in Set.Ioi (τ.im + 1),
          Aexp (Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  have hB : (1 : ℝ) ≤ τ.im + 1 := by have := hτ.2; linarith
  have hclosed := aexp_integral_closed (Gcusp ℓ d) τ (B := τ.im + 1) hB hr (by
    intro hle
    by_cases h8 : d = 8
    · exact ⟨gcusp_one_zero ℓ h8 0 τ, gcusp_one_zero ℓ h8 1 τ⟩
    · exfalso
      have h2 : 2 < r ^ 2 := by
        rcases hreg with h | h
        · exact absurd h h8
        · exact h
      have hpos : 0 < Real.pi * r ^ 2 - 2 * Real.pi := by nlinarith [Real.pi_pos]
      exact absurd hle (not_le.mpr hpos))
  simp only [highTailClosed, Fin.isValue]
  rw [hclosed]
  ring


end

end Work.Asymptotics.FunnelAsm
