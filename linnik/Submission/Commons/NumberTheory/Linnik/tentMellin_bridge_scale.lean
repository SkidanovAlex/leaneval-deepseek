import Mathlib
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec
import Submission.Commons.NumberTheory.Linnik.tentWeight_laplace
import Submission.Commons.NumberTheory.Linnik.tentWeight_bounds
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.Analysis.Complex.perron_log_identity
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_completed_tentF_eq
import Submission.Commons.NumberTheory.DirichletCharacter.leftEdge_logDeriv_bound
import Submission.Commons.NumberTheory.DirichletCharacter.horizontalSegment_logDeriv_bound_le_one
import Submission.Commons.NumberTheory.DirichletCharacter.horizontalGamma_logDeriv_bound
import Submission.Commons.NumberTheory.DirichletCharacter.goodHeight_separated
import Submission.Commons.Analysis.Integral.norm_intervalIntegral_mul_le
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_gammaFactor_mul_eq
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re

open Complex DirichletCharacter Metric Filter MeasureTheory
open Commons.NumberTheory.DirichletCharacter
open scoped Real BigOperators Topology

set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

namespace Commons.NumberTheory.Linnik

/-! ## The entire tent kernel -/

/-- `(1 - e^{-K z})/z` as an entire function (value `K` at `z = 0`). -/
noncomputable def tentH (K : ℝ) (z : ℂ) : ℂ :=
  - dslope (fun w : ℂ => Complex.exp (-(((K : ℝ) : ℂ) * w))) 0 z

/-- The Laplace transform of `tentWeight L K`, extended to an entire function:
`z ↦ e^{-(L-2K)z} ((1 - e^{-Kz})/z)^2`. -/
noncomputable def tentK (L K : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * z)) * (tentH K z) ^ 2

lemma tentH_diff (K : ℝ) : Differentiable ℂ (tentH K) := by
  unfold tentH
  refine Differentiable.neg ?_
  have hd : DifferentiableOn ℂ (fun w : ℂ => Complex.exp (-(((K : ℝ) : ℂ) * w))) Set.univ :=
    fun z _ => (by fun_prop : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (-(((K : ℝ) : ℂ) * w))) z).differentiableWithinAt
  have hd' := (differentiableOn_dslope
    (f := fun w : ℂ => Complex.exp (-(((K : ℝ) : ℂ) * w))) (c := (0 : ℂ))
    (s := Set.univ) (by simp : Set.univ ∈ nhds (0 : ℂ))).mpr hd
  exact fun z => ((hd' z (by simp)).differentiableAt (by simp))

lemma tentH_eq (K : ℝ) (z : ℂ) (hz : z ≠ 0) :
    tentH K z = (1 - Complex.exp (-(((K : ℝ) : ℂ) * z))) / z := by
  unfold tentH
  rw [dslope_of_ne _ hz, slope_def_module]
  simp only [sub_zero, smul_eq_mul]
  rw [show Complex.exp (-(((K : ℝ) : ℂ) * 0)) = 1 by simp]
  field_simp
  ring

lemma tentH_zero (K : ℝ) : tentH K 0 = (K : ℂ) := by
  unfold tentH
  rw [dslope_same]
  have h3 : HasDerivAt (fun w : ℂ => (((K : ℝ) : ℂ) * w)) (((K : ℝ) : ℂ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (((K : ℝ) : ℂ))
  have h2 : HasDerivAt (fun w : ℂ => -(((K : ℝ) : ℂ) * w)) (-(((K : ℝ) : ℂ))) 0 := h3.neg
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (-(((K : ℝ) : ℂ) * w)))
      (-(((K : ℝ) : ℂ))) 0 := by simpa using h2.cexp
  rw [h1.deriv]
  simp

lemma tentK_diff (L K : ℝ) : Differentiable ℂ (tentK L K) := by
  unfold tentK
  exact (by fun_prop : Differentiable ℂ
    (fun z : ℂ => Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * z)))).mul ((tentH_diff K).pow 2)

lemma tentK_eq_closed (L K : ℝ) (z : ℂ) (hz : z ≠ 0) :
    tentK L K z = Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * z)) *
      (((1 - Complex.exp (-(((K : ℝ) : ℂ) * z))) / z) ^ 2) := by
  unfold tentK
  rw [tentH_eq K z hz]


/-! ## The tent weight as a combination of ReLU's -/

lemma tentWeight_eq_relu {L K : ℝ} (hK : 0 ≤ K) (x : ℝ) :
    tentWeight L K x = max (L - 2 * K - x) 0 - 2 * max (L - K - x) 0 + max (L - x) 0 := by
  rw [tentWeight_spec]
  by_cases h1 : x ≤ L - 2 * K
  · rw [if_pos h1, max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_left (by linarith)]
    ring
  · rw [if_neg h1, max_eq_right (by linarith)]
    by_cases h2 : x ≤ L - K
    · rw [if_pos h2, max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · rw [if_neg h2, max_eq_right (by linarith)]
      by_cases h3 : x ≤ L
      · rw [if_pos h3, max_eq_left (by linarith)]
        ring
      · rw [if_neg h3, max_eq_right (by linarith)]
        ring

/-! ## The kernel as a finite combination of exponentials -/

lemma tentK_eq_sum {L K : ℝ} (z : ℂ) (hz : z ≠ 0) :
    tentK L K z =
      (Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * z)) - 2 * Complex.exp (-(((L - K : ℝ) : ℂ) * z))
        + Complex.exp (-(((L : ℝ) : ℂ) * z))) / z ^ 2 := by
  rw [tentK_eq_closed L K z hz]
  have h1 : Complex.exp (-(((L - K : ℝ) : ℂ) * z))
      = Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * z)) * Complex.exp (-(((K : ℝ) : ℂ) * z)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (-(((L : ℝ) : ℂ) * z))
      = Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * z)) * (Complex.exp (-(((K : ℝ) : ℂ) * z)))^2 := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  field_simp
  ring


/-! ## The Perron kernel identity -/

/-- Inverse Laplace/Perron kernel at the point `1`: the vertical integral of
`e^{(1+it)β}/(1+it)^2` is `max β 0`. -/
lemma perron_exp_kernel (β : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I) * (β : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)
      = ((max β 0 : ℝ) : ℂ) := by
  have hx : 0 < Real.exp β := Real.exp_pos β
  have h := Commons.Analysis.Complex.perron_log_identity (c := 1) one_pos hx
  have hkey : ∀ t : ℝ,
      (Real.exp β : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) / (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)
        = Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I) * (β : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hx)),
      ← Complex.ofReal_log (le_of_lt hx), Real.log_exp, mul_comm]
  have h2 : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I) * (β : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (Real.exp β : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (hkey t).symm))
  have h' : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (Real.exp β : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)
      = if (1 : ℝ) < Real.exp β then ((Real.log (Real.exp β) : ℝ) : ℂ) else 0 := by
    simpa only [Complex.ofReal_one] using h
  rw [h2, h', Real.log_exp]
  by_cases hβ : (1 : ℝ) < Real.exp β
  · rw [if_pos hβ, show max β 0 = β from max_eq_left (le_of_lt (Real.one_lt_exp_iff.mp hβ))]
  · rw [if_neg hβ, show max β 0 = 0 from
      max_eq_right (le_of_not_gt (fun h => hβ (Real.one_lt_exp_iff.mpr h)))]
    simp

/-! ## The single-term inversion -/

/-- Pointwise rewriting of the integrand. -/
lemma exp_split' (A : ℂ) (a b : ℝ) :
    Complex.exp (A * (a : ℂ)) * Complex.exp (-(A + 1) * (b : ℂ))
      = (Complex.exp (b : ℂ))⁻¹ * Complex.exp (A * ((a - b : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  have : A * (a : ℂ) + -(A + 1) * (b : ℂ) = -(b : ℂ) + A * ((a - b : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_neg]

lemma integrand_eq {L K : ℝ} {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 1 ≤ n) (t : ℝ) :
    tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ))
        * ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)))
      = ((n : ℂ))⁻¹ * ((((Real.log (Q : ℝ) : ℝ) : ℂ)) ^ 2)⁻¹ * ((
          Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
          - 2 * Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
          + Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)))
        / (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)) := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
  have hlog_n : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hnpos)).symm
  set A : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hA
  set lq : ℂ := ((Real.log (Q : ℝ) : ℝ) : ℂ) with hlq
  set z : ℂ := (1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq with hz_def
  have hA0 : A ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp [hA] at hh
  have hlq0 : lq ≠ 0 := by
    simp only [hlq, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hlogQ
  have hzA : z = -(A * lq) := by
    rw [hz_def, hA]; ring
  have hz : z ≠ 0 := by
    rw [hzA, ← neg_mul]; exact mul_ne_zero (neg_ne_zero.mpr hA0) hlq0
  have hcpow : (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))
      = Complex.exp (-(A + 1) * ((Real.log (n : ℝ) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hnne, hlog_n]
    congr 1
    rw [hA]; ring
  rw [hcpow, tentK_eq_sum (L := L) (K := K) z hz]
  rw [show z ^ 2 = A ^ 2 * lq ^ 2 by rw [hzA]; ring]
  rw [show Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * z))
        = Complex.exp (A * (((L - 2 * K) * Real.log (Q : ℝ) : ℝ) : ℂ)) by
      congr 1; rw [hzA, hA, hlq]; push_cast; ring]
  rw [show Complex.exp (-(((L - K : ℝ) : ℂ) * z))
        = Complex.exp (A * (((L - K) * Real.log (Q : ℝ) : ℝ) : ℂ)) by
      congr 1; rw [hzA, hA, hlq]; push_cast; ring]
  rw [show Complex.exp (-(((L : ℝ) : ℂ) * z))
        = Complex.exp (A * (((L) * Real.log (Q : ℝ) : ℝ) : ℂ)) by
      congr 1; rw [hzA, hA, hlq]; push_cast; ring]
  rw [div_mul_eq_mul_div]
  rw [show (Complex.exp (A * (((L - 2 * K) * Real.log (Q : ℝ) : ℝ) : ℂ))
          - 2 * Complex.exp (A * (((L - K) * Real.log (Q : ℝ) : ℝ) : ℂ))
          + Complex.exp (A * (((L) * Real.log (Q : ℝ) : ℝ) : ℂ)))
        * Complex.exp (-(A + 1) * ((Real.log (n : ℝ) : ℝ) : ℂ))
      = Complex.exp (A * (((L - 2 * K) * Real.log (Q : ℝ) : ℝ) : ℂ))
          * Complex.exp (-(A + 1) * ((Real.log (n : ℝ) : ℝ) : ℂ))
        - 2 * (Complex.exp (A * (((L - K) * Real.log (Q : ℝ) : ℝ) : ℂ))
          * Complex.exp (-(A + 1) * ((Real.log (n : ℝ) : ℝ) : ℂ)))
        + Complex.exp (A * (((L) * Real.log (Q : ℝ) : ℝ) : ℂ))
          * Complex.exp (-(A + 1) * ((Real.log (n : ℝ) : ℝ) : ℂ)) by ring]
  rw [exp_split' A ((L - 2 * K) * Real.log (Q : ℝ)) (Real.log (n : ℝ)),
      exp_split' A ((L - K) * Real.log (Q : ℝ)) (Real.log (n : ℝ)),
      exp_split' A ((L) * Real.log (Q : ℝ)) (Real.log (n : ℝ))]
  rw [show Complex.exp ((Real.log (n : ℝ) : ℝ) : ℂ) = (n : ℂ) by
    rw [← Complex.ofReal_exp, Real.exp_log hnpos]; simp]
  field_simp


lemma integrable_perron_exp (β : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I) * (β : ℂ)) /
        (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)) volume := by
  have hg : Integrable (fun t : ℝ => Real.exp β * (1 + t ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul (Real.exp β)
  refine Integrable.mono' hg ?_ ?_
  · apply Continuous.aestronglyMeasurable
    refine Continuous.div ?_ ?_ ?_
    · exact Continuous.cexp (by fun_prop)
    · fun_prop
    · intro t
      have : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
      exact pow_ne_zero 2 this
  · filter_upwards with t
    have hA : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rw [norm_div, Complex.norm_exp, Complex.norm_pow]
    have hre : (((1 : ℂ) + (t : ℂ) * Complex.I) * (β : ℂ)).re = β := by
      simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.mul_im]
    rw [hre]
    have hnorm : ‖((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = 1 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im]
      ring
    rw [hnorm]
    rw [div_eq_mul_inv]


lemma single_inversion {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q)
    {n : ℕ} (hn : 1 ≤ n) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ,
        tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ))
          * ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)))
      = ((n : ℂ))⁻¹ * ((tentWeight L K (Real.log (n : ℝ) / Real.log (Q : ℝ)) : ℝ) : ℂ)
        / ((Real.log (Q : ℝ) : ℝ) : ℂ) := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  set lq : ℂ := ((Real.log (Q : ℝ) : ℝ) : ℂ) with hlq
  have hlqne : lq ≠ 0 := by
    simp only [hlq, ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hlogQ
  -- rewrite the integrand pointwise
  have hpt : (fun t : ℝ => tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ))
        * ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))))
      = fun t : ℝ => ((n : ℂ))⁻¹ * (lq ^ 2)⁻¹ *
          ((Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
            - 2 * Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
            + Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)))
          / (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)) := by
    funext t
    rw [integrand_eq hQ hn t]
  rw [hpt, MeasureTheory.integral_const_mul]
  -- split the integral
  set g : ℝ → ℂ := fun t : ℝ => Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
        * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
        (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) with hg
  set h : ℝ → ℂ := fun t : ℝ => Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
        * ((((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
        (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) with hh
  set k : ℝ → ℂ := fun t : ℝ => Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
        * ((((L) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
        (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) with hk
  have hgi : Integrable g volume := integrable_perron_exp _
  have hhi : Integrable h volume := integrable_perron_exp _
  have hki : Integrable k volume := integrable_perron_exp _
  have h1 : Integrable (fun t : ℝ => g t - 2 * h t) volume := hgi.sub (hhi.const_mul 2)
  have hsplit : (∫ t : ℝ, ((Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
            - 2 * Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
            + Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)))
          / (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)))
      = (∫ t : ℝ, g t) - 2 * (∫ t : ℝ, h t) + (∫ t : ℝ, k t) := by
    rw [show (fun t : ℝ => ((Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
            - 2 * Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ))
            + Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
              * ((((L) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)))
          / (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)))
        = fun t : ℝ => g t - 2 * h t + k t by
      funext t; simp only [hg, hh, hk]; ring]
    rw [show (∫ t : ℝ, g t - 2 * h t + k t) = ∫ t : ℝ, (fun s : ℝ => g s - 2 * h s) t + k t
      from rfl]
    rw [MeasureTheory.integral_add h1 hki,
      MeasureTheory.integral_sub hgi (hhi.const_mul 2), MeasureTheory.integral_const_mul]
  rw [hsplit]
  -- evaluate each
  have hp1 := perron_exp_kernel ((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ))
  have hp2 := perron_exp_kernel ((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ))
  have hp3 := perron_exp_kernel ((L) * Real.log (Q : ℝ) - Real.log (n : ℝ))
  have e1 : (∫ t : ℝ, g t) = 2 * (Real.pi : ℂ) *
      (((max ((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0 : ℝ)) : ℂ) := by
    rw [hg]
    have := hp1
    rw [show (∫ t : ℝ, Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)) = ∫ t : ℝ,
          Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) from rfl]
    have hne : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)]
    have hmul : (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2))
        = ∫ t : ℝ, Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
      rw [← mul_assoc, mul_one_div_cancel hne, one_mul]
    rw [← hmul, this]
  have e2 : (∫ t : ℝ, h t) = 2 * (Real.pi : ℂ) *
      (((max ((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0 : ℝ)) : ℂ) := by
    rw [hh]
    have hmul : (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2))
        = ∫ t : ℝ, Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
      rw [← mul_assoc, mul_one_div_cancel (by
        simp [Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)]), one_mul]
    rw [← hmul, hp2]
  have e3 : (∫ t : ℝ, k t) = 2 * (Real.pi : ℂ) *
      (((max ((L) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0 : ℝ)) : ℂ) := by
    rw [hk]
    have hmul : (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2))
        = ∫ t : ℝ, Complex.exp (((1 : ℂ) + (t : ℂ) * Complex.I)
            * ((((L) * Real.log (Q : ℝ) - Real.log (n : ℝ) : ℝ)) : ℂ)) /
          (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
      rw [← mul_assoc, mul_one_div_cancel (by
        simp [Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)]), one_mul]
    rw [← hmul, hp3]
  rw [e1, e2, e3]
  -- real algebra: the max-combination is `log Q * tentWeight`
  have hmax : ∀ c : ℝ, max (c * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0
      = Real.log (Q : ℝ) * max (c - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0 := by
    intro c
    rw [show c * Real.log (Q : ℝ) - Real.log (n : ℝ)
          = (c - Real.log (n : ℝ) / Real.log (Q : ℝ)) * Real.log (Q : ℝ) by field_simp]
    rw [show (0 : ℝ) = 0 * Real.log (Q : ℝ) by ring,
      ← max_mul_of_nonneg (c - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0
        (c := Real.log (Q : ℝ)) (le_of_lt hlogQ)]
    ring
  have hreal : max ((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0
        - 2 * max ((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0
        + max ((L) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0
      = Real.log (Q : ℝ) * tentWeight L K (Real.log (n : ℝ) / Real.log (Q : ℝ)) := by
    rw [hmax (L - 2 * K), hmax (L - K), hmax L,
      show Real.log (Q : ℝ) * max ((L - 2 * K) - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0
          - 2 * (Real.log (Q : ℝ) * max ((L - K) - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0)
          + Real.log (Q : ℝ) * max ((L) - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0
        = Real.log (Q : ℝ) * (max ((L - 2 * K) - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0
          - 2 * max ((L - K) - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0
          + max ((L) - Real.log (n : ℝ) / Real.log (Q : ℝ)) 0) by ring,
      ← tentWeight_eq_relu (le_of_lt hK) (Real.log (n : ℝ) / Real.log (Q : ℝ))]
  have hkey : (2 * (Real.pi : ℂ)) * (((max ((L - 2 * K) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0 : ℝ)) : ℂ)
        - 2 * ((2 * (Real.pi : ℂ)) * (((max ((L - K) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0 : ℝ)) : ℂ))
        + (2 * (Real.pi : ℂ)) * (((max ((L) * Real.log (Q : ℝ) - Real.log (n : ℝ)) 0 : ℝ)) : ℂ)
      = (2 * (Real.pi : ℂ)) * (((Real.log (Q : ℝ) * tentWeight L K (Real.log (n : ℝ) / Real.log (Q : ℝ)) : ℝ)) : ℂ) := by
    rw [← hreal]
    push_cast
    ring
  rw [hkey]
  have hmain : (1 / (2 * Real.pi)) * ((n : ℂ)⁻¹ * (lq ^ 2)⁻¹ *
        ((2 * (Real.pi : ℂ)) *
          (((Real.log (Q : ℝ) * tentWeight L K (Real.log (n : ℝ) / Real.log (Q : ℝ)) : ℝ)) : ℂ)))
      = (n : ℂ)⁻¹ * ((tentWeight L K (Real.log (n : ℝ) / Real.log (Q : ℝ)) : ℝ) : ℂ) / lq := by
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)]
    have hnne : (n : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by exact_mod_cast hn : (0:ℝ) < n))
    rw [Complex.ofReal_mul, ← hlq]
    field_simp
  exact hmain


/-! ## The Mellin identity for the Dirichlet sum -/

/-- Bound of the kernel on the line `Re s = 2`. -/
lemma norm_tentK_line_two {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q)
    (t : ℝ) :
    ‖tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
      ≤ Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
          (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 *
          (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  set lq : ℂ := ((Real.log (Q : ℝ) : ℝ) : ℂ) with hlq
  have hre_lq : lq.re = Real.log (Q : ℝ) := by rw [hlq, Complex.ofReal_re]
  have him_lq : lq.im = 0 := by rw [hlq, Complex.ofReal_im]
  have hlqne : lq ≠ 0 := by
    intro h
    have h' : lq.re = 0 := by simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [hre_lq] at h'
    exact hlogQ.ne' h'
  set A : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hA
  have hre_A : A.re = 1 := by rw [hA]; simp
  have him_A : A.im = t := by rw [hA]; simp
  set z : ℂ := (1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq with hz_def
  have hz_eq : z = -(A * lq) := by rw [hz_def, hA]; ring
  have hAne : A ≠ 0 := by
    intro h
    have h' : A.re = 0 := by simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [hre_A] at h'
    norm_num at h'
  have hz_ne : z ≠ 0 := by
    rw [hz_eq]
    exact neg_ne_zero.mpr (mul_ne_zero hAne hlqne)
  have hre_z : z.re = -Real.log (Q : ℝ) := by
    rw [hz_eq, Complex.neg_re, Complex.mul_re]
    simp only [hre_A, him_A, hre_lq, him_lq, mul_zero, sub_zero, one_mul]
  have hnormz : Complex.normSq z = (1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2 := by
    have h1 : Complex.normSq A = 1 + t ^ 2 := by
      rw [Complex.normSq_apply, hre_A, him_A]; ring
    have h2 : Complex.normSq lq = (Real.log (Q : ℝ)) ^ 2 := by
      rw [Complex.normSq_apply, hre_lq, him_lq]; ring
    have h3 : Complex.normSq (-(1:ℂ)) = 1 := by
      rw [Complex.normSq_apply]; simp
    rw [hz_eq, show -(A * lq) = (-1 : ℂ) * (A * lq) by ring, Complex.normSq_mul,
      Complex.normSq_mul, h3, h1, h2]
    ring
  rw [tentK_eq_closed _ _ _ hz_ne, norm_mul, Complex.norm_exp, Complex.norm_pow, norm_div]
  have hexp : (-(((L - 2 * K : ℝ) : ℂ) * z)).re = (L - 2 * K) * Real.log (Q : ℝ) := by
    rw [Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hre_z, mul_zero, sub_zero]
    ring
  rw [hexp]
  have hnum : ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ ≤ 1 + Real.exp (K * Real.log (Q : ℝ)) := by
    calc ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-(((K : ℝ) : ℂ) * z))‖ := norm_sub_le _ _
      _ = 1 + Real.exp (K * Real.log (Q : ℝ)) := by
          rw [norm_one, Complex.norm_exp]
          congr 1
          rw [Complex.neg_re, Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, hre_z, mul_zero, sub_zero]
          ring
  have h2 : (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2
      ≤ (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 *
        (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by
    have hnormz' : ‖z‖ ^ 2 = (1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hnormz]
    rw [div_pow, hnormz', div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnum 2) (by positivity)
  calc Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
        (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2
      ≤ Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
          ((1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 *
            (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
    _ = Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
          (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 *
          (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by ring



lemma norm_nat_cpow (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖(n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ = ((n : ℝ))⁻¹ ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  have hre : (-((2 : ℂ) + (t : ℂ) * Complex.I)).re = -2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    simp
  rw [hre, show ((-2 : ℝ)) = -(2:ℝ) by norm_num, Real.rpow_neg (le_of_lt hnpos),
    Real.rpow_two, inv_pow]

/-- The Mellin identity: the Dirichlet sum equals `1/(2πi)` times the vertical
integral of `-L'/L` against the tent kernel, at scale `log Q`. -/
theorem mellin_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q)
    {X : ℕ} (hX : (Q : ℝ) ^ L ≤ (X : ℝ)) :
    ((Real.log (Q : ℝ) : ℝ) : ℂ)⁻¹ *
        (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ))
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
          (- logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * Complex.I)) *
            tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ)) := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  set lq : ℂ := ((Real.log (Q : ℝ) : ℝ) : ℂ) with hlq
  have hlqne : lq ≠ 0 := by
    intro h
    have h' : lq.re = 0 := by simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [hlq, Complex.ofReal_re] at h'
    exact hlogQ.ne' h'
  set Cb : ℝ := Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
      (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 * ((Real.log (Q : ℝ)) ^ 2)⁻¹ with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hKbound : ∀ t : ℝ, ‖tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)‖
      ≤ Cb * (1 + t ^ 2)⁻¹ := by
    intro t
    have h := norm_tentK_line_two hK h2K hQ t
    rw [hlq]
    calc ‖tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
        ≤ Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
            (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 *
            (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := h
      _ = Cb * (1 + t ^ 2)⁻¹ := by
          rw [hCb, mul_inv]
          ring
  set G : ℕ → ℝ → ℂ := fun n t => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) *
      ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
        tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq) with hG
  have hGb : ∀ (n : ℕ) (t : ℝ), ‖G n t‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ))⁻¹ ^ 2 *
      Cb * (1 + t ^ 2)⁻¹ := by
    intro n t
    rw [hG, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [ArithmeticFunction.map_zero]; simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rw [norm_nat_cpow n hn1 t]
      have h1 : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (n : ZMod N)
      have h2 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have h3 : 0 ≤ (n : ℝ)⁻¹ ^ 2 := by positivity
      have ha : (ArithmeticFunction.vonMangoldt n : ℝ) * ‖(χ (n : ZMod N) : ℂ)‖ *
            ((n : ℝ)⁻¹ ^ 2) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * ((n : ℝ)⁻¹ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 h2) le_rfl h3 (mul_nonneg h2 zero_le_one)
      have hb : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * ((n : ℝ)⁻¹ ^ 2) :=
        mul_nonneg (mul_nonneg h2 zero_le_one) h3
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖(χ (n : ZMod N) : ℂ)‖ *
            ((n : ℝ)⁻¹ ^ 2) * ‖tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * ((n : ℝ)⁻¹ ^ 2) *
            (Cb * (1 + t ^ 2)⁻¹) := mul_le_mul ha (hKbound t) (norm_nonneg _) hb
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ))⁻¹ ^ 2 * Cb * (1 + t ^ 2)⁻¹ := by
            ring
  have hInt : ∀ n : ℕ, Integrable (G n) volume := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · have hzero : G 0 = fun _ => 0 := by
        funext t
        simp [hG, ArithmeticFunction.map_zero]
      rw [hzero]
      exact integrable_zero _ _ _
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hmeas : AEStronglyMeasurable (G n) volume := by
        apply Continuous.aestronglyMeasurable
        rw [hG]
        refine Continuous.mul ?_ ?_
        · refine Continuous.mul ?_ ?_
          · exact continuous_const
          · refine Continuous.cpow continuous_const (by fun_prop) ?_
            intro t
            exact Or.inl (by rw [Complex.natCast_re]; exact_mod_cast hn1)
        · exact (tentK_diff L K).continuous.comp (by fun_prop)
      refine Integrable.mono' (g := fun t : ℝ => ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((n : ℝ))⁻¹ ^ 2 * Cb) * (1 + t ^ 2)⁻¹)
        (integrable_inv_one_add_sq.const_mul _) hmeas ?_
      exact Filter.Eventually.of_forall (fun t => hGb n t)
  have hSum : Summable (fun n : ℕ => ∫ t : ℝ, ‖G n t‖) := by
    have hIint : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) volume := integrable_inv_one_add_sq
    have hVsum : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ))⁻¹ ^ 2) := by
      have hLsum := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) (by norm_num)
      rw [LSeriesSummable] at hLsum
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (by
        simpa using hLsum.norm)
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        rw [LSeries.term_def, if_neg hn0, norm_div,
          show (n : ℂ) = ((n:ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn1 : (0:ℝ) < n),
          Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have h2r : ((2 : ℂ)).re = 2 := by simp
        rw [h2r, show ((n:ℝ) ^ (2:ℝ)) = (n:ℝ)^2 by rw [Real.rpow_two],
          div_eq_mul_inv, inv_pow]
    have hIntb : ∀ n : ℕ, ∫ t : ℝ, ‖G n t‖ ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) *
        ((n : ℝ))⁻¹ ^ 2 * Cb) * (∫ t : ℝ, (1 + t ^ 2)⁻¹) := by
      intro n
      have hmono : ∫ t : ℝ, ‖G n t‖ ≤ ∫ t : ℝ, ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((n : ℝ))⁻¹ ^ 2 * Cb) * (1 + t ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
          (hIint.const_mul _) ?_
        exact Filter.Eventually.of_forall (fun t => hGb n t)
      rwa [integral_const_mul] at hmono
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) hIntb ?_
    simpa only [mul_assoc] using hVsum.mul_right (Cb * (∫ t : ℝ, (1 + t ^ 2)⁻¹))
  have hpt : ∀ t : ℝ, (- logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * Complex.I)) *
      tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq) = ∑' n : ℕ, G n t := by
    intro t
    have hre : (((2 : ℂ) + (t : ℂ) * Complex.I)).re = 2 := by simp
    have hld := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
      χ (s := ((2 : ℂ) + (t : ℂ) * Complex.I)) (by rw [hre]; norm_num)
    rw [hG,
      show (- logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * Complex.I))
        = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
            ((2 : ℂ) + (t : ℂ) * Complex.I) by rw [hld]; ring,
      LSeries, ← tsum_mul_right]
    apply tsum_congr
    intro n
    rw [LSeries.term_def]
    by_cases hn0 : n = 0
    · simp [hn0]
    · rw [if_neg hn0]
      beta_reduce
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [funext hpt, ← integral_tsum_of_summable_integral_norm hInt hSum]
  have hterm : ∀ n : ℕ, (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G n t
      = ((n : ℂ))⁻¹ * ((tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) := by
    intro n
    rw [hG]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [hG, ArithmeticFunction.map_zero, tentWeight_spec, h2K]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have h1 : (∫ t : ℝ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) *
            ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq))
          = ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) *
            ∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        ring
      rw [h1]
      have hs' : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
            ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)
          = ((n : ℂ))⁻¹ * ((tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ) / lq := by
        have hswap : (∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ)))
            = ∫ t : ℝ, tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (Q : ℝ) : ℝ) : ℂ)) *
              ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) := by
          apply integral_congr_ae
          filter_upwards with t
          ring
        rw [show lq = ((Real.log (Q : ℝ) : ℝ) : ℂ) from hlq, hswap]
        exact single_inversion (L := L) (K := K) hK h2K hQ hn1
      rw [show (1 / (2 * (Real.pi : ℂ))) *
            (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) *
              ∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
                tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq))
          = ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
                tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)) by ring,
        hs']
      ring
  rw [← tsum_mul_left,
    show (∑' n : ℕ, (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G n t)
      = ∑' n : ℕ, ((n : ℂ)⁻¹ *
        ((tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)))
      from tsum_congr (fun n => hterm n)]
  clear hterm hGb hKbound hInt hSum hpt
  have hzero : ∀ n : ℕ, X < n → ((n : ℂ))⁻¹ *
        ((tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) = 0 := by
    intro n hn
    have hnQ : (Q : ℝ) ^ L < (n : ℝ) := lt_of_le_of_lt hX (by exact_mod_cast hn)
    have hu : L < Real.log (n : ℝ) / Real.log (Q : ℝ) := by
      rw [lt_div_iff₀ hlogQ]
      calc L * Real.log (Q : ℝ) = Real.log ((Q : ℝ) ^ L) := by
            rw [Real.log_rpow (by positivity : (0 : ℝ) < (Q : ℝ))]
        _ < Real.log (n : ℝ) := Real.log_lt_log (Real.rpow_pos_of_pos (by positivity) _) hnQ
    have htw : tentWeight L K (Real.log (n : ℝ) / Real.log (Q : ℝ)) = 0 :=
      (tentWeight_bounds (le_of_lt hK) (le_of_lt h2K)).2.2.2 _ (le_of_lt hu)
    rw [htw]
    simp
  have hsupport : ∀ n ∉ Finset.Icc 1 X, ((n : ℂ))⁻¹ *
        ((tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) = 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    push_neg at hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · exact hzero n (hn (by omega))
  rw [tsum_eq_sum hsupport, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  field_simp


/-- Bound of the kernel on the line `Re s = -1/2`. -/
lemma norm_tentK_left {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q)
    (t : ℝ) :
    ‖tentK L K (((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) * ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
      ≤ 4 * Real.exp (-(3 / 2) * (L - 2 * K) * Real.log (Q : ℝ)) *
          (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  set lq : ℂ := ((Real.log (Q : ℝ) : ℝ) : ℂ) with hlq
  have hre_lq : lq.re = Real.log (Q : ℝ) := by rw [hlq, Complex.ofReal_re]
  have him_lq : lq.im = 0 := by rw [hlq, Complex.ofReal_im]
  have hlqne : lq ≠ 0 := by
    intro h
    have h' : lq.re = 0 := by simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [hre_lq] at h'
    exact hlogQ.ne' h'
  set z : ℂ := ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) * lq with hz_def
  have hre_z : z.re = (3 / 2) * Real.log (Q : ℝ) := by
    rw [hz_def, Complex.mul_re]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre_lq, him_lq,
      mul_zero, sub_zero]
    ring
  have hre_negz : (-z).re = -((3 / 2) * Real.log (Q : ℝ)) := by
    rw [hz_def, Complex.neg_re, Complex.mul_re]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre_lq, him_lq,
      mul_zero, sub_zero]
    ring
  have hz_ne : z ≠ 0 := by
    rw [hz_def]
    refine mul_ne_zero ?_ hlqne
    intro h
    have hre : ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I).re = 0 := by
      simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [Complex.sub_re, Complex.mul_re] at hre
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre
    norm_num at hre
  have hnormz : ((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2) ≤ Complex.normSq z := by
    rw [hz_def, Complex.normSq_mul]
    have hn1 : 1 + t ^ 2 ≤ Complex.normSq ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero]
      nlinarith [sq_nonneg t]
    have hn2 : Complex.normSq lq = (Real.log (Q : ℝ)) ^ 2 := by
      rw [Complex.normSq_apply, hre_lq, him_lq]; ring
    rw [hn2]
    exact mul_le_mul_of_nonneg_right hn1 (by positivity)
  rw [tentK_eq_closed _ _ _ hz_ne, norm_mul, Complex.norm_exp, Complex.norm_pow, norm_div]
  have hexp : (-(((L - 2 * K : ℝ) : ℂ) * z)).re
      = -((L - 2 * K) * ((3 / 2) * Real.log (Q : ℝ))) := by
    rw [Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, hre_z]
  rw [hexp]
  have hnum : ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ ≤ 2 := by
    have h1 : (-(((K : ℝ) : ℂ) * z)).re = -(K * ((3 / 2) * Real.log (Q : ℝ))) := by
      rw [Complex.neg_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, hre_z]
    calc ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-(((K : ℝ) : ℂ) * z))‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          rw [Complex.norm_exp, h1, norm_one]
          exact add_le_add le_rfl (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hK hlogQ]))
      _ = 2 := by norm_num
  have hnum2 : ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (1 - Complex.exp (-(((K : ℝ) : ℂ) * z))), hnum]
  have h2 : (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2
      ≤ 4 * (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by
    rw [div_pow, show ‖z‖ ^ 2 = Complex.normSq z from Complex.sq_norm z, div_eq_mul_inv]
    calc ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ ^ 2 * (Complex.normSq z)⁻¹
        ≤ 4 * (Complex.normSq z)⁻¹ := mul_le_mul_of_nonneg_right hnum2 (inv_nonneg.mpr (Complex.normSq_nonneg _))
      _ ≤ 4 * (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact (inv_le_inv₀ (Complex.normSq_pos.mpr hz_ne) (by positivity)).mpr hnormz
  calc Real.exp (-((L - 2 * K) * ((3 / 2) * Real.log (Q : ℝ)))) *
        (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2
      ≤ Real.exp (-((L - 2 * K) * ((3 / 2) * Real.log (Q : ℝ)))) *
          (4 * (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
    _ = 4 * Real.exp (-(3 / 2) * (L - 2 * K) * Real.log (Q : ℝ)) *
          (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by
        rw [show -((L - 2 * K) * ((3 / 2) * Real.log (Q : ℝ)))
            = -(3 / 2) * (L - 2 * K) * Real.log (Q : ℝ) by ring]
        ring

/-- The kernel at `0`. -/
lemma norm_tentK_zero {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q) :
    ‖tentK L K ((Real.log (Q : ℝ) : ℝ) : ℂ)‖ ≤
      4 * Real.exp (-(L - 2 * K) * Real.log (Q : ℝ)) *
        (((Real.log (Q : ℝ)) ^ 2))⁻¹ := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  set lq : ℂ := ((Real.log (Q : ℝ) : ℝ) : ℂ) with hlq
  have hre_lq : lq.re = Real.log (Q : ℝ) := by rw [hlq, Complex.ofReal_re]
  have him_lq : lq.im = 0 := by rw [hlq, Complex.ofReal_im]
  have hlqne : lq ≠ 0 := by
    intro h
    have h' : lq.re = 0 := by simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [hre_lq] at h'
    exact hlogQ.ne' h'
  rw [tentK_eq_closed _ _ _ hlqne, norm_mul, Complex.norm_exp, Complex.norm_pow, norm_div]
  have hexp : (-(((L - 2 * K : ℝ) : ℂ) * lq)).re = -(L - 2 * K) * Real.log (Q : ℝ) := by
    rw [Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hre_lq, him_lq, zero_mul, sub_zero]
    ring
  rw [hexp]
  have hnum : ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * lq))‖ ≤ 2 := by
    have h1 : (-(((K : ℝ) : ℂ) * lq)).re = -K * Real.log (Q : ℝ) := by
      rw [Complex.neg_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, hre_lq, him_lq, zero_mul, sub_zero]
      ring
    calc ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * lq))‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-(((K : ℝ) : ℂ) * lq))‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          rw [Complex.norm_exp, h1, norm_one]
          exact add_le_add le_rfl (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hK hlogQ]))
      _ = 2 := by norm_num
  have hnum2 : ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * lq))‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (1 - Complex.exp (-(((K : ℝ) : ℂ) * lq))), hnum]
  have hnormz : (Real.log (Q : ℝ)) ^ 2 ≤ Complex.normSq lq := by
    rw [Complex.normSq_apply, hre_lq, him_lq]; nlinarith [sq_nonneg (Real.log (Q : ℝ))]
  have h2 : (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * lq))‖ / ‖lq‖) ^ 2
      ≤ 4 * (((Real.log (Q : ℝ)) ^ 2))⁻¹ := by
    rw [div_pow, show ‖lq‖ ^ 2 = Complex.normSq lq from Complex.sq_norm lq, div_eq_mul_inv]
    calc ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * lq))‖ ^ 2 * (Complex.normSq lq)⁻¹
        ≤ 4 * (Complex.normSq lq)⁻¹ := mul_le_mul_of_nonneg_right hnum2 (inv_nonneg.mpr (Complex.normSq_nonneg _))
      _ ≤ 4 * (((Real.log (Q : ℝ)) ^ 2))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact (inv_le_inv₀ (Complex.normSq_pos.mpr hlqne) (by positivity)).mpr hnormz
  calc Real.exp (-(L - 2 * K) * Real.log (Q : ℝ)) *
        (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * lq))‖ / ‖lq‖) ^ 2
      ≤ Real.exp (-(L - 2 * K) * Real.log (Q : ℝ)) *
          (4 * (((Real.log (Q : ℝ)) ^ 2))⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
    _ = 4 * Real.exp (-(L - 2 * K) * Real.log (Q : ℝ)) *
          (((Real.log (Q : ℝ)) ^ 2))⁻¹ := by ring

/-! ## Bounds for the tent kernel on the divisor sum -/

/-- The tent kernel decays like `1/|z|²` in the right half-plane. -/
lemma norm_tentK_strip {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {z : ℂ} (hz : z ≠ 0)
    (hzre : 0 ≤ z.re) : ‖tentK L K z‖ ≤ 4 / ‖z‖ ^ 2 := by
  rw [tentK_eq_closed L K z hz, norm_mul, Complex.norm_exp]
  have h1 : (-(((L - 2 * K : ℝ) : ℂ) * z)).re = -(L - 2 * K) * z.re := by
    rw [Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [h1]
  have hLnn : 0 ≤ L - 2 * K := by linarith
  have he : Real.exp (-(L - 2 * K) * z.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hLnn hzre]
  have h2 : ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ ≤ 2 := by
    have hre : (-(((K : ℝ) : ℂ) * z)).re = -K * z.re := by
      rw [Complex.neg_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    have h1' := norm_sub_le (1 : ℂ) (Complex.exp (-(((K : ℝ) : ℂ) * z)))
    simp only [norm_one] at h1'
    refine h1'.trans ?_
    rw [Complex.norm_exp, hre]
    have hexp : Real.exp (-K * z.re) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg (le_of_lt hK) hzre]
    linarith
  rw [Complex.norm_pow, norm_div]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2' : (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2 ≤ (2 / ‖z‖) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff_of_pos_right hzpos]
    exact h2
  calc Real.exp (-(L - 2 * K) * z.re) * (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2
      ≤ 1 * (2 / ‖z‖) ^ 2 :=
        mul_le_mul he h2' (by positivity) (by norm_num)
    _ = 4 / ‖z‖ ^ 2 := by field_simp; ring

/-! ## The kernel evaluated at `(1 - u)·log Q` -/

/-- The tent kernel of the Perron/Mellin bridge, as a function of the contour variable `u`. -/
noncomputable def tentPhi (L K : ℝ) (Q : ℕ) (u : ℂ) : ℂ :=
  tentK L K ((1 - u) * ((Real.log (Q : ℝ) : ℝ) : ℂ))

lemma tentPhi_diff (L K : ℝ) (Q : ℕ) : Differentiable ℂ (tentPhi L K Q : ℂ → ℂ) := by
  unfold tentPhi
  exact (tentK_diff L K).comp (by fun_prop)

/-- Bound of the tent kernel when `Re z ≥ -log Q`. -/
lemma norm_tentK_of_re_ge {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q)
    {z : ℂ} (hz : z ≠ 0) (hzre : -(Real.log (Q : ℝ)) ≤ z.re) :
    ‖tentK L K z‖ ≤ Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
      (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 / ‖z‖ ^ 2 := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  have hLnn : 0 ≤ L - 2 * K := by linarith
  rw [tentK_eq_closed L K z hz, norm_mul, Complex.norm_exp, Complex.norm_pow, norm_div]
  have hexp : (-(((L - 2 * K : ℝ) : ℂ) * z)).re = -(L - 2 * K) * z.re := by
    rw [Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [hexp]
  have h1 : Real.exp (-(L - 2 * K) * z.re) ≤ Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) := by
    rw [Real.exp_le_exp]
    nlinarith [mul_nonneg hLnn (by linarith : 0 ≤ z.re + Real.log (Q : ℝ)), hlogQ]
  have h2 : ‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ ≤ 1 + Real.exp (K * Real.log (Q : ℝ)) := by
    have hre : (-(((K : ℝ) : ℂ) * z)).re = -K * z.re := by
      rw [Complex.neg_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    have hle : Real.exp (-K * z.re) ≤ Real.exp (K * Real.log (Q : ℝ)) := by
      rw [Real.exp_le_exp]
      nlinarith [mul_nonneg (le_of_lt hK) (by linarith : 0 ≤ z.re + Real.log (Q : ℝ)), hlogQ]
    have h1' := norm_sub_le (1 : ℂ) (Complex.exp (-(((K : ℝ) : ℂ) * z)))
    simp only [norm_one] at h1'
    rw [Complex.norm_exp, hre] at h1'
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2' : (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2 ≤
      ((1 + Real.exp (K * Real.log (Q : ℝ))) / ‖z‖) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff_of_pos_right hzpos]
    exact h2
  calc Real.exp (-(L - 2 * K) * z.re) * (‖1 - Complex.exp (-(((K : ℝ) : ℂ) * z))‖ / ‖z‖) ^ 2
      ≤ Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
          ((1 + Real.exp (K * Real.log (Q : ℝ))) / ‖z‖) ^ 2 :=
        mul_le_mul h1 h2' (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
          (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 / ‖z‖ ^ 2 := by
        rw [div_pow]; ring

/-- Uniform bound for the kernel of the bridge: `‖tentPhi u‖ ≤ M/(1+‖u‖²)` on `Re u ≤ 2`. -/
lemma exists_norm_tentPhi_bound {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : ℂ, u.re ≤ 2 → ‖tentPhi L K Q u‖ ≤ M / (1 + ‖u‖ ^ 2) := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  obtain ⟨A, hA⟩ := isCompact_closedBall (0 : ℂ) (2 : ℝ) |>.exists_bound_of_continuousOn
    (tentPhi_diff L K Q).continuous.continuousOn
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0 (by simp [Metric.mem_closedBall]))
  set E : ℝ := Real.exp ((L - 2 * K) * Real.log (Q : ℝ)) *
    (1 + Real.exp (K * Real.log (Q : ℝ))) ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  refine ⟨5 * A + 8 * (E / (Real.log (Q : ℝ)) ^ 2) + 1, by positivity, ?_⟩
  intro u hu
  set M : ℝ := 5 * A + 8 * (E / (Real.log (Q : ℝ)) ^ 2) + 1 with hM
  have hM5 : 5 * A ≤ M := by
    rw [hM]; nlinarith [hA0, div_nonneg hE0 (by positivity : (0:ℝ) ≤ (Real.log (Q : ℝ)) ^ 2)]
  have hM8 : 8 * (E / (Real.log (Q : ℝ)) ^ 2) ≤ M := by
    rw [hM]; nlinarith [hA0, div_nonneg hE0 (by positivity : (0:ℝ) ≤ (Real.log (Q : ℝ)) ^ 2)]
  have hMpos : 0 < M := by
    rw [hM]
    have h2 : (0:ℝ) ≤ 8 * (E / (Real.log (Q : ℝ)) ^ 2) :=
      mul_nonneg (by norm_num) (div_nonneg hE0 (by positivity))
    linarith [hA0]
  have hparts : E ≤ M * (Real.log (Q : ℝ)) ^ 2 / 8 := by
    have h2 : 0 < (Real.log (Q : ℝ)) ^ 2 := by positivity
    have h8 : (8 : ℝ) * (E / (Real.log (Q : ℝ)) ^ 2) = 8 * E / (Real.log (Q : ℝ)) ^ 2 := by ring
    rw [h8] at hM8
    rw [div_le_iff₀ h2] at hM8
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    linarith
  by_cases hu2 : ‖u‖ ≤ 2
  · have humem : u ∈ Metric.closedBall (0 : ℂ) (2 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hu2
    have h1 : ‖tentPhi L K Q u‖ ≤ A := hA u humem
    have h2 : A ≤ M / (1 + ‖u‖ ^ 2) := by
      rw [le_div_iff₀ (by positivity : 0 < 1 + ‖u‖ ^ 2)]
      have h5 : 1 + ‖u‖ ^ 2 ≤ 5 := by
        have hh := pow_le_pow_left₀ (norm_nonneg u) hu2 2
        linarith
      have hm := mul_le_mul_of_nonneg_left h5 hA0
      nlinarith [hm, hM5]
    linarith
  · have hnorm2 : 2 < ‖u‖ := not_le.mp hu2
    have h1u : ‖u‖ / 2 ≤ ‖1 - u‖ := by
      have h3 : ‖u‖ ≤ ‖u - 1‖ + 1 := by
        calc ‖u‖ = ‖(u - 1) + 1‖ := by congr 1; ring
          _ ≤ ‖u - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = ‖u - 1‖ + 1 := by rw [norm_one]
      have : ‖u - 1‖ = ‖1 - u‖ := by rw [show u - 1 = -(1 - u) by ring, norm_neg]
      rw [this] at h3
      linarith
    have h1upos : 0 < ‖1 - u‖ := by linarith
    have h1une : 1 - u ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt h1upos)
    set ql : ℂ := ((Real.log (Q : ℝ) : ℝ) : ℂ) with hql
    have hqlne : ql ≠ 0 := by
      intro h
      have : ql.re = 0 := by simpa only [Complex.zero_re] using congrArg Complex.re h
      rw [hql] at this
      simp only [Complex.ofReal_re] at this
      exact hlogQ.ne' this
    have hzre : -(Real.log (Q : ℝ)) ≤ ((1 - u) * ql).re := by
      rw [Complex.mul_re, hql]
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_im, Complex.one_im, mul_zero, sub_zero]
      nlinarith [hu, hlogQ]
    have hzne : (1 - u) * ql ≠ 0 := mul_ne_zero h1une hqlne
    have hb := norm_tentK_of_re_ge hK h2K hQ hzne hzre
    have hnormz : ‖(1 - u) * ql‖ = ‖1 - u‖ * Real.log (Q : ℝ) := by
      rw [norm_mul, hql, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogQ]
    rw [hnormz, ← hE] at hb
    have hden : 0 < (‖1 - u‖ * Real.log (Q : ℝ)) ^ 2 := by positivity
    have hu2sq : ‖u‖ ^ 2 ≤ 4 * ‖1 - u‖ ^ 2 := by nlinarith [h1u, norm_nonneg (1 - u)]
    refine le_trans hb ?_
    rw [div_le_div_iff₀ hden (by positivity : 0 < 1 + ‖u‖ ^ 2)]
    have h1' : 1 + ‖u‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 := by nlinarith [hnorm2, sq_nonneg ‖u‖]
    have hmul1 : E * (1 + ‖u‖ ^ 2) ≤ E * (2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left h1' hE0
    have hmul2 : E * (2 * ‖u‖ ^ 2) ≤ E * (2 * (4 * ‖1 - u‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith [hu2sq]) hE0
    have hstep : E * (1 + ‖u‖ ^ 2) ≤ 8 * E * ‖1 - u‖ ^ 2 := by nlinarith [hmul1, hmul2]
    have hstep2 : 8 * E * ‖1 - u‖ ^ 2 ≤ M * (‖1 - u‖ * Real.log (Q : ℝ)) ^ 2 := by
      rw [mul_pow]
      have h4 := mul_le_mul_of_nonneg_right hparts (show (0:ℝ) ≤ ‖1 - u‖ ^ 2 by positivity)
      nlinarith [h4]
    linarith [hstep, hstep2]
/-! ## Uniform bounds for the logarithmic derivatives on the left edge -/

/-- The gamma factor never vanishes on the line `Re s = -1/2`. -/
lemma gammaFactor_ne_zero_of_re_eq_neg_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s.re = -1 / 2) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]
    intro h0
    rw [Complex.Gammaℝ_eq_zero_iff] at h0
    obtain ⟨n, hn⟩ := h0
    have hre := congrArg Complex.re hn
    rw [hs] at hre
    simp at hre
    have h2 : (n : ℝ) = 1 / 4 := by linarith
    have h4 : ((4 * n : ℕ) : ℝ) = 1 := by push_cast; linarith
    have h4' : 4 * n = 1 := by exact_mod_cast h4
    omega
  · rw [hO.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by
      have : (s + 1).re = (1 / 2 : ℝ) := by rw [Complex.add_re, hs]; norm_num
      rw [this]; norm_num)

/-- On the vertical line `Re s = 3/2` the log-derivative of the gamma factor is
`O(log(2+|T|))`. -/
lemma norm_logDeriv_gammaFactor_at_three_halves {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : ℝ) :
    ‖logDeriv (gammaFactor χ) (((3 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)‖ ≤
      Real.log (2 + |T|) / 2 + 14 := by
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I with hsdef
  have hsre : s.re = (3 / 2 : ℝ) := by rw [hsdef]; simp [Complex.sub_re, Complex.mul_re]
  have hsim : s.im = -T := by rw [hsdef]; simp [Complex.sub_im, Complex.mul_im]
  have hsne : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this; simp at this
  have hsrel : (-1 : ℝ) < s.re := by rw [hsre]; norm_num
  have hnorm_logpi : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
    have hlogpi_nn : (0 : ℝ) ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [norm_div, norm_neg, ← Complex.ofReal_log (le_of_lt Real.pi_pos),
      Complex.norm_of_nonneg hlogpi_nn, norm_ofNat]
  have hlogpi : Real.log Real.pi / 2 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  have hlogT : Real.log (2 + |-(T / 2)|) ≤ Real.log (2 + |T|) := by
    apply Real.log_le_log (by positivity)
    have h2 : |-(T / 2)| = |T| / 2 := by rw [abs_neg, abs_div]; norm_num
    rw [h2]; linarith [abs_nonneg T]
  have hinv' : ‖(1 : ℂ) / s‖ ≤ 2 / 3 := by
    have hlow : (3 / 2 : ℝ) ≤ ‖s‖ := by
      have h := Complex.abs_re_le_norm s
      rw [hsre] at h
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)] at h
      exact h
    rw [norm_div, norm_one]
    refine le_trans (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3/2) hlow) ?_
    norm_num
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    rw [hfun]
    have hkey := Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_add_inv hsne hsrel
    have harg : s / 2 + 1 = ((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I := by
      rw [hsdef]
      apply Complex.ext <;>
        simp [Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im, Complex.sub_re,
          Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.normSq_apply] <;> ring
    rw [harg] at hkey
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound (7 / 4) (-(T / 2))
      (by norm_num) (by norm_num)
    have hbound : ‖Complex.digamma (((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I)‖ ≤
        Real.log (2 + |T|) + 8 := le_trans hdg (by linarith [hlogT])
    have hfinal : ‖-(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma (((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖ ≤
        Real.log (2 + |T|) / 2 + 13 := by
      calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
            Complex.digamma (((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖
          ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
            ‖Complex.digamma (((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖ :=
            norm_add_le _ _
        _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |T|) + 8) / 2 := by
            rw [hnorm_logpi, norm_div]
            have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
            rw [h2n]
            have h := hbound
            linarith
        _ ≤ Real.log (2 + |T|) / 2 + 13 := by linarith
    have hL : logDeriv Complex.Gammaℝ s =
        -1 / s + (-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2) := by
      rw [← hkey]; ring
    rw [hL]
    calc ‖-1 / s + (-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2)‖
        ≤ ‖-1 / s‖ +
          ‖-(Complex.log (Real.pi : ℂ)) / 2 +
            Complex.digamma (((7 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖ :=
          norm_add_le _ _
      _ ≤ 2 / 3 + (Real.log (2 + |T|) / 2 + 13) := by
          refine add_le_add ?_ hfinal
          rw [show (-1 : ℂ) / s = -(1 / s) by ring, norm_neg]
          exact hinv'
      _ ≤ Real.log (2 + |T|) / 2 + 14 := by linarith
  · have hfun : gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) := funext hO.gammaFactor_def
    rw [hfun]
    have hcomp : logDeriv (fun w : ℂ => Complex.Gammaℝ (w + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun w : ℂ => w + 1) (x := s)
        (Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ (s + 1) (by
          rw [Complex.add_re, hsre]; norm_num)) (by fun_prop)
      have hder : deriv (fun w : ℂ => w + 1) s = 1 := by simp
      simpa [Function.comp_def, hder] using h
    rw [hcomp]
    have hne1 : s + 1 ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      rw [Complex.add_re, hsre, Complex.one_re] at h'
      norm_num at h'
    have hre1 : (-1 : ℝ) < (s + 1).re := by rw [Complex.add_re, hsre]; norm_num
    have hkey := Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_add_inv hne1 hre1
    have harg : (s + 1) / 2 + 1 = ((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I := by
      rw [hsdef]
      apply Complex.ext <;>
        simp [Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im, Complex.sub_re,
          Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.normSq_apply] <;> ring
    rw [harg] at hkey
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound (9 / 4) (-(T / 2))
      (by norm_num) (by norm_num)
    have hbound : ‖Complex.digamma (((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I)‖ ≤
        Real.log (2 + |T|) + 8 := le_trans hdg (by linarith [hlogT])
    have hfinal : ‖-(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma (((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖ ≤
        Real.log (2 + |T|) / 2 + 13 := by
      calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
            Complex.digamma (((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖
          ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
            ‖Complex.digamma (((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖ :=
            norm_add_le _ _
        _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |T|) + 8) / 2 := by
            rw [hnorm_logpi, norm_div]
            have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
            rw [h2n]
            linarith [hbound]
        _ ≤ Real.log (2 + |T|) / 2 + 13 := by linarith
    have hL : logDeriv Complex.Gammaℝ (s + 1) =
        -1 / (s + 1) + (-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2) := by
      rw [← hkey]; ring
    rw [hL]
    have hinv2 : ‖-1 / (s + 1)‖ ≤ 2 / 3 := by
      have hlow : (5 / 2 : ℝ) ≤ ‖s + 1‖ := by
        have h := Complex.abs_re_le_norm (s + 1)
        rw [Complex.add_re, hsre, Complex.one_re] at h
        norm_num at h
        exact h
      rw [norm_div, norm_neg, norm_one]
      refine le_trans (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 5/2) hlow) ?_
      norm_num
    calc ‖-1 / (s + 1) + (-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2)‖
        ≤ ‖-1 / (s + 1)‖ +
          ‖-(Complex.log (Real.pi : ℂ)) / 2 +
            Complex.digamma (((9 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I) / 2‖ :=
          norm_add_le _ _
      _ ≤ 2 / 3 + (Real.log (2 + |T|) / 2 + 13) := add_le_add hinv2 hfinal
      _ ≤ Real.log (2 + |T|) / 2 + 14 := by linarith
/-- The gamma factor is complex-differentiable on the line `Re s = -1/2`. -/
lemma differentiableAt_gammaFactor_at_neg_half {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    DifferentiableAt ℂ (gammaFactor χ) (((-1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I) := by
  set z : ℂ := ((-1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I with hz
  have hz2 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre : (z / 2).re = -(1 / 4 : ℝ) := by
      rw [hz]
      norm_num [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.normSq_apply]
    have h2 : (m : ℝ) = 1 / 4 := by
      have := congrArg Complex.re hm
      rw [hre] at this
      simp at this
      linarith
    have h4 : ((4 * m : ℕ) : ℝ) = 1 := by
      have hc : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
      rw [hc, h2]; norm_num
    have h4' : 4 * m = 1 := by exact_mod_cast h4
    omega
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    rw [hfun]
    have hfun2 : Complex.Gammaℝ =
        (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) := by
      funext w; rw [Complex.Gammaℝ_def]
    rw [hfun2]
    exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -w / 2) z).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      ((Complex.differentiableAt_Gamma (z / 2) hz2).comp z (by fun_prop))
  · have hfun : gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) :=
      funext hO.gammaFactor_def
    rw [hfun]
    have hpos : 0 < (z + 1).re := by
      rw [hz]
      norm_num [Complex.add_re, Complex.mul_re]
    exact (Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ (z + 1) hpos).comp z
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w + 1) z)

/-- Uniform pointwise bound for `L'/L` on the line `Re s = -1/2`. -/
theorem logDeriv_LFunction_leftEdge_uniform {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    ‖logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      100 * (Real.log (N : ℝ) + Real.log (2 + |T|) + 1) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I with hsdef
  have hsre : s.re = (-1 / 2 : ℝ) := by rw [hsdef]; simp [Complex.add_re, Complex.mul_re]
  have hs1 : (1 - s).re = (3 / 2 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, hsre]; norm_num
  have hN1 : N ≠ 1 := by rintro rfl; exact hχ (Subsingleton.elim χ 1)
  have hN2 : 2 ≤ N := by have h1 : 1 ≤ N := NeZero.one_le; omega
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNge1
  have hlog2 : 0 ≤ Real.log (2 + |T|) := Real.log_nonneg (by linarith [abs_nonneg T])
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  have hχpinv : (χ⁻¹).IsPrimitive := Commons.NumberTheory.DirichletCharacter.isPrimitive_inv hχprim
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    rw [hsdef]
    exact Commons.NumberTheory.DirichletCharacter.LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim T
  have hγs : gammaFactor χ s ≠ 0 := by
    rw [hsdef]
    exact gammaFactor_ne_zero_of_re_eq_neg_half χ (by simp [Complex.add_re, Complex.mul_re])
  have hγdiff : DifferentiableAt ℂ (gammaFactor χ) s := by
    rw [hsdef]
    exact differentiableAt_gammaFactor_at_neg_half χ T
  have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro h
    exact hLs (by rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1),
      h, zero_div])
  have hΛcs : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
    intro h
    have hL : DirichletCharacter.LFunction (χ⁻¹) (1 - s) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (Or.inl hχinv) (by rw [hs1]; norm_num)
    exact hL (by rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ⁻¹) (1 - s)
      (Or.inr hN1), h, zero_div])
  have hLsplit : logDeriv (DirichletCharacter.LFunction χ) s =
      logDeriv (DirichletCharacter.completedLFunction χ) s - logDeriv (gammaFactor χ) s := by
    have hfun : DirichletCharacter.LFunction χ =
        (fun z => DirichletCharacter.completedLFunction χ z / gammaFactor χ z) :=
      funext (fun z => DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN1))
    rw [hfun]
    exact logDeriv_div s hΛs hγs ((DirichletCharacter.differentiable_completedLFunction hχ) s) hγdiff
  have hFE := Commons.NumberTheory.DirichletCharacter.logDeriv_completedL_fe_transfer χ hχ hχprim s
    hΛs hΛcs
  have hsplit := Commons.NumberTheory.DirichletCharacter.leftHalf_avg.logDeriv_completedL_eq_add_re_ge_one
    (χ⁻¹) hχinv hχpinv (1 - s) (by rw [hs1]; norm_num)
  have hL1 : ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s)‖ ≤ 20 :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_ge_three_halves_bound (χ⁻¹)
      (s := 1 - s) (by rw [hs1])
  have hγ1 : ‖logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖ ≤ Real.log (2 + |T|) / 2 + 14 := by
    have h := norm_logDeriv_gammaFactor_at_three_halves (χ := χ⁻¹) T
    have heq : (1 : ℂ) - s = ((3 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    rwa [heq]
  have hγ0 : ‖logDeriv (gammaFactor χ) s‖ ≤ Real.log (2 + |T|) / 2 + 14 := by
    have h := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_gammaFactor_leftEdge χ T
    have hbound : Real.log Real.pi / 2 + (Real.log (2 + |T|) + 8) / 2 + 2 ≤
        Real.log (2 + |T|) / 2 + 14 := by
      have hp : Real.log Real.pi / 2 ≤ 2 := by
        have h' := Real.log_le_sub_one_of_pos Real.pi_pos
        linarith [Real.pi_lt_four]
      linarith
    rw [hsdef]
    linarith [h, hbound]
  have hlogNeq : ‖-(Real.log (N : ℝ) : ℂ)‖ = Real.log (N : ℝ) := by
    rw [norm_neg, Complex.norm_of_nonneg hlogN]
  have hkey : ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      Real.log (N : ℝ) + 20 + (Real.log (2 + |T|) / 2 + 14) + (Real.log (2 + |T|) / 2 + 14) := by
    rw [hLsplit, hFE, hsplit]
    calc ‖(-(Real.log (N : ℝ) : ℂ) -
            (logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
              logDeriv (gammaFactor (χ⁻¹)) (1 - s))) - logDeriv (gammaFactor χ) s‖
        ≤ ‖-(Real.log (N : ℝ) : ℂ) -
            (logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
              logDeriv (gammaFactor (χ⁻¹)) (1 - s))‖ + ‖logDeriv (gammaFactor χ) s‖ :=
          norm_sub_le _ _
      _ ≤ (‖-(Real.log (N : ℝ) : ℂ)‖ +
            ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
              logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖) + ‖logDeriv (gammaFactor χ) s‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (Real.log (N : ℝ) + (20 + (Real.log (2 + |T|) / 2 + 14))) +
            (Real.log (2 + |T|) / 2 + 14) := by
          refine add_le_add (add_le_add ?_ ?_) hγ0
          · exact le_of_eq hlogNeq
          · calc ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
                  logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖
                ≤ ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s)‖ +
                  ‖logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖ := norm_add_le _ _
              _ ≤ 20 + (Real.log (2 + |T|) / 2 + 14) := add_le_add hL1 hγ1
      _ = Real.log (N : ℝ) + 20 + (Real.log (2 + |T|) / 2 + 14) +
            (Real.log (2 + |T|) / 2 + 14) := by ring
  have hfin : Real.log (N : ℝ) + 20 + (Real.log (2 + |T|) / 2 + 14) +
        (Real.log (2 + |T|) / 2 + 14) ≤
      100 * (Real.log (N : ℝ) + Real.log (2 + |T|) + 1) := by
    nlinarith [hlogN, hlog2]
  rw [hsdef] at hkey
  exact hkey.trans hfin
/-! ## The left-edge integral of the `L`-log-derivative -/

/-! ## The left-edge integral of the `L`-log-derivative -/

/-- `u · √u = u ^ (3/2)` for `u > 0`. -/
private lemma mul_sqrt_eq_rpow' (u : ℝ) (hu : 0 < u) : u * Real.sqrt u = u ^ ((3:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hu 1 (1/2),
    Real.rpow_one]

/-- `(u √u)^{-1} = u ^ (-3/2)` for `u > 0`. -/
private lemma inv_mul_sqrt_eq_rpow' (u : ℝ) (hu : 0 < u) :
    (u * Real.sqrt u)⁻¹ = u ^ (-((3:ℝ)/2)) := by
  rw [mul_sqrt_eq_rpow' u hu, Real.rpow_neg hu.le (3/2)]

lemma log_weight_le_rpow (t : ℝ) :
    (Real.log (2 + |t|) + 1) / (1 + t ^ 2) ≤ 8 * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
  have hlog1 : Real.log (2 + |t|) ≤ 2 * Real.sqrt (2 + |t|) := by
    have h := Real.log_le_rpow_div (by linarith [abs_nonneg t] : (0:ℝ) ≤ 2 + |t|)
      (by norm_num : (0:ℝ) < 1/2)
    have h2 : (2 + |t|) ^ ((1:ℝ)/2) / ((1:ℝ)/2) = 2 * Real.sqrt (2 + |t|) := by
      rw [Real.sqrt_eq_rpow]; ring
    rwa [h2] at h
  have hsq : Real.sqrt (2 + |t|) ≤ Real.sqrt 2 * Real.sqrt (1 + |t|) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith [abs_nonneg t])
  have h3 : (2:ℝ) * Real.sqrt 2 ≤ 3 := by
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 1)]
  have hs1 : (1:ℝ) ≤ Real.sqrt (1 + |t|) := by
    rw [Real.le_sqrt (by norm_num) (by linarith [abs_nonneg t])]; linarith [abs_nonneg t]
  have hs1nn : 0 ≤ Real.sqrt (1 + |t|) := Real.sqrt_nonneg _
  have hlog2 : Real.log (2 + |t|) + 1 ≤ 4 * Real.sqrt (1 + |t|) := by
    have hb : Real.log (2 + |t|) ≤ 2 * (Real.sqrt 2 * Real.sqrt (1 + |t|)) :=
      le_trans hlog1 (by linarith [hsq])
    nlinarith [hb, h3, hs1nn, hs1]
  have hden : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hu : (0:ℝ) < 1 + |t| := by positivity
  have hkey : 4 * Real.sqrt (1 + |t|) / (1 + t ^ 2) ≤
      8 / ((1 + |t|) * Real.sqrt (1 + |t|)) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hsu : Real.sqrt (1 + |t|) ^ 2 = 1 + |t| := Real.sq_sqrt hu.le
    have habs : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [sq_nonneg (|t| - 1), hsu, Real.sqrt_nonneg (1 + |t|), habs]
  calc (Real.log (2 + |t|) + 1) / (1 + t ^ 2)
      ≤ 4 * Real.sqrt (1 + |t|) / (1 + t ^ 2) := div_le_div_of_nonneg_right hlog2 hden.le
    _ ≤ 8 / ((1 + |t|) * Real.sqrt (1 + |t|)) := hkey
    _ = 8 * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, inv_mul_sqrt_eq_rpow' (1 + |t|) hu]

/-- `∫_0^∞ (1+x)^{-3/2} dx = 2`. -/
private lemma integral_one_add_rpow_Ioi' :
    (∫ x in Set.Ioi (0:ℝ), (1 + x) ^ (-((3:ℝ)/2))) = 2 := by
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun x : ℝ => -2 * (1 + x) ^ (-((1:ℝ)/2))) ((1 + x) ^ (-((3:ℝ)/2))) x := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx
    have hpos : (0:ℝ) < 1 + x := by linarith
    have hbase : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have hrp : HasDerivAt (fun y : ℝ => (1 + y) ^ (-((1:ℝ)/2)))
        (1 * (-((1:ℝ)/2)) * (1 + x) ^ (-((1:ℝ)/2) - 1)) x :=
      hbase.rpow_const (Or.inl hpos.ne')
    have h3 : HasDerivAt (fun y : ℝ => -2 * (1 + y) ^ (-((1:ℝ)/2)))
        (-2 * (1 * (-((1:ℝ)/2)) * (1 + x) ^ (-((1:ℝ)/2) - 1))) x :=
      hrp.const_mul (-2)
    convert h3 using 1
    rw [show -((1:ℝ)/2) - 1 = -((3:ℝ)/2) by norm_num]
    ring
  have hint : IntegrableOn (fun x : ℝ => (1 + x) ^ (-((3:ℝ)/2))) (Set.Ioi (0:ℝ)) volume := by
    have h := integrableOn_add_rpow_Ioi_of_lt (a := -((3:ℝ)/2)) (c := (0:ℝ)) (m := (1:ℝ))
      (by norm_num) (by norm_num)
    simpa [add_comm] using h
  have hlim : Tendsto (fun x : ℝ => -2 * (1 + x) ^ (-((1:ℝ)/2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (1 + x) ^ (-((1:ℝ)/2))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < (1:ℝ)/2)).comp
        (Filter.tendsto_atTop_add_const_right _ (1:ℝ) tendsto_id)
      simpa [Function.comp_def, add_comm] using h
    simpa using h1.const_mul (-2)
  have hval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hval]
  norm_num

/-- `t ↦ 8 (1+|t|)^{-3/2}` is integrable. -/
private lemma integrable_abs_rpow_neg :
    Integrable (fun t : ℝ => 8 * (1 + |t|) ^ (-((3:ℝ)/2))) volume := by
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-((3:ℝ)/2))) volume := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3:ℝ)/2)
      (by rw [Module.finrank_self]; norm_num)
    simpa [Real.norm_eq_abs] using h
  simpa using hbase.const_mul 8

/-- `∫_ℝ 8 (1+|t|)^{-3/2} dt = 32`. -/
private lemma integral_abs_rpow_neg :
    (∫ t : ℝ, 8 * (1 + |t|) ^ (-((3:ℝ)/2))) = 32 := by
  rw [MeasureTheory.integral_const_mul]
  have hB : (∫ t : ℝ, (1 + |t|) ^ (-((3:ℝ)/2))) =
      2 * ∫ x in Set.Ioi (0:ℝ), (1 + x) ^ (-((3:ℝ)/2)) :=
    integral_comp_abs (f := fun x : ℝ => (1 + x) ^ (-((3:ℝ)/2)))
  rw [hB, integral_one_add_rpow_Ioi']
  norm_num

/-- Bound of the left-edge integral of `L'/L` against the tent kernel. -/
lemma leftEdge_L_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q)
    (hNQ : N ≤ Q) :
    ‖(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          tentK L K ((1 - (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
            ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
      ≤ 4000 * ((Real.log (Q : ℝ))⁻¹ *
          (Real.exp (-(3 / 2) * (L - 2 * K) * Real.log (Q : ℝ)) *
            (Real.log (Q : ℝ))⁻¹ * (1 + Real.log (Q : ℝ)))) := by
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
  have hlogQnn : 0 ≤ Real.log (Q : ℝ) := le_of_lt hlogQ
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N from NeZero.one_le)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNge1
  have hlogNle : Real.log (N : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hNQ)
  set E : ℝ := Real.exp (-(3 / 2) * (L - 2 * K) * Real.log (Q : ℝ)) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hcoef : 0 ≤ 400 * E / (Real.log (Q : ℝ)) ^ 2 := by positivity
  -- pointwise bound on the integrand
  have hpt : ∀ t : ℝ,
      ‖logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        tentK L K ((1 - (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
        ≤ (400 * E / (Real.log (Q : ℝ)) ^ 2) *
          ((Real.log (N : ℝ) + Real.log (2 + |t|) + 1) / (1 + t ^ 2)) := by
    intro t
    rw [norm_mul]
    have harg : (1 - (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          ((Real.log (Q : ℝ) : ℝ) : ℂ)
        = ((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) * ((Real.log (Q : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [harg]
    have h1 : ‖logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        100 * (Real.log (N : ℝ) + Real.log (2 + |t|) + 1) :=
      logDeriv_LFunction_leftEdge_uniform χ hχ hχprim t
    have h2 := norm_tentK_left hK h2K hQ t
    have h2' : ‖tentK L K (((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
          ((Real.log (Q : ℝ) : ℝ) : ℂ))‖ ≤
        4 * E * (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹ := by
      rw [hE]; exact h2
    have hb : 0 ≤ 100 * (Real.log (N : ℝ) + Real.log (2 + |t|) + 1) := by
      have h := Real.log_nonneg (by linarith [abs_nonneg t] : (1:ℝ) ≤ 2 + |t|)
      linarith [hlogN, h]
    calc ‖logDeriv (DirichletCharacter.LFunction χ)
            (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
          ‖tentK L K (((((3 : ℝ) / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
            ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
        ≤ (100 * (Real.log (N : ℝ) + Real.log (2 + |t|) + 1)) *
            (4 * E * (((1 + t ^ 2) * (Real.log (Q : ℝ)) ^ 2))⁻¹) :=
          mul_le_mul h1 h2' (norm_nonneg _) hb
      _ = (400 * E / (Real.log (Q : ℝ)) ^ 2) *
            ((Real.log (N : ℝ) + Real.log (2 + |t|) + 1) / (1 + t ^ 2)) := by
          field_simp; ring
  -- the dominating function
  have hdom : Integrable (fun t : ℝ =>
      (400 * E / (Real.log (Q : ℝ)) ^ 2) * ((Real.log (Q : ℝ) + 1) *
        (8 * (1 + |t|) ^ (-((3:ℝ)/2))))) volume :=
    (integrable_abs_rpow_neg.const_mul ((Real.log (Q : ℝ) + 1))).const_mul
      (400 * E / (Real.log (Q : ℝ)) ^ 2)
  have hpoint : ∀ t : ℝ,
      (400 * E / (Real.log (Q : ℝ)) ^ 2) *
        ((Real.log (N : ℝ) + Real.log (2 + |t|) + 1) / (1 + t ^ 2))
      ≤ (400 * E / (Real.log (Q : ℝ)) ^ 2) * ((Real.log (Q : ℝ) + 1) *
        (8 * (1 + |t|) ^ (-((3:ℝ)/2)))) := by
    intro t
    have hlog2nn : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    have hnum : Real.log (N : ℝ) + Real.log (2 + |t|) + 1 ≤
        (Real.log (Q : ℝ) + 1) * (Real.log (2 + |t|) + 1) := by
      have hprod : 0 ≤ Real.log (Q : ℝ) * Real.log (2 + |t|) := mul_nonneg hlogQnn hlog2nn
      have hlogNnn : 0 ≤ Real.log (N : ℝ) := hlogN
      have h1 : Real.log (N : ℝ) ≤ Real.log (Q : ℝ) + Real.log (Q : ℝ) * Real.log (2 + |t|) := by
        linarith [hlogNle, hprod]
      nlinarith [h1, hlog2nn]
    have hdenpos : (0:ℝ) < 1 + t ^ 2 := by positivity
    have hdiv : (Real.log (N : ℝ) + Real.log (2 + |t|) + 1) / (1 + t ^ 2) ≤
        (Real.log (Q : ℝ) + 1) * ((Real.log (2 + |t|) + 1) / (1 + t ^ 2)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hdenpos.le)
    have hlogwl := log_weight_le_rpow t
    have hQ1nn : (0:ℝ) ≤ Real.log (Q : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_left (le_trans hdiv (mul_le_mul_of_nonneg_left hlogwl hQ1nn))
      hcoef
  have hmain : ‖(1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          tentK L K ((1 - (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
            ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
      ≤ (1 / (2 * Real.pi)) * ((400 * E / (Real.log (Q : ℝ)) ^ 2) *
          ((Real.log (Q : ℝ) + 1) * 32)) := by
    have hcst : ‖((1:ℂ) / ((2:ℂ) * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
      have h : (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
      rw [norm_div, h, norm_one, Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    have h1 : ‖(1 / ((2:ℂ) * (Real.pi : ℂ))) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          tentK L K ((1 - (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
            ((Real.log (Q : ℝ) : ℝ) : ℂ))‖
        = (1 / (2 * Real.pi)) * ‖∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          tentK L K ((1 - (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
            ((Real.log (Q : ℝ) : ℝ) : ℂ))‖ := by
      rw [norm_mul, hcst]
    have h2 : (1 / (2 * (Real.pi : ℂ))) = (1:ℂ) / ((2:ℂ) * (Real.pi : ℂ)) := by ring
    rw [h2, h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t =>
      norm_nonneg _)) hdom (Filter.Eventually.of_forall (fun t =>
      le_trans (hpt t) (hpoint t)))) ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_abs_rpow_neg]
  refine le_trans hmain ?_
  rw [hE]
  have htarget : (1 / (2 * Real.pi)) * ((400 * E / (Real.log (Q : ℝ)) ^ 2) *
        ((Real.log (Q : ℝ) + 1) * 32))
      ≤ 4000 * ((Real.log (Q : ℝ))⁻¹ *
          (E * (Real.log (Q : ℝ))⁻¹ * (1 + Real.log (Q : ℝ)))) := by
    have heq1 : (1 / (2 * Real.pi)) * ((400 * E / (Real.log (Q : ℝ)) ^ 2) *
          ((Real.log (Q : ℝ) + 1) * 32))
        = (6400 / Real.pi) * (E * (1 + Real.log (Q : ℝ)) / (Real.log (Q : ℝ)) ^ 2) := by
      field_simp
      try ring
    have heq2 : 4000 * ((Real.log (Q : ℝ))⁻¹ *
          (E * (Real.log (Q : ℝ))⁻¹ * (1 + Real.log (Q : ℝ))))
        = 4000 * (E * (1 + Real.log (Q : ℝ)) / (Real.log (Q : ℝ)) ^ 2) := by
      field_simp
      try ring
    rw [heq1, heq2]
    have hle : 6400 / Real.pi ≤ 4000 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi)]
      nlinarith [Real.pi_gt_three]
    have hE1 : 0 ≤ E * (1 + Real.log (Q : ℝ)) / (Real.log (Q : ℝ)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hle hE1
  linarith [htarget]
/-! ## The limit of the rectangle integral along a vertical strip -/

/-- As `T → ∞`, the rectangle integral over `[-1/2 - iT, 2 + iT]` tends to the difference of the
two vertical-line integrals. -/
lemma rectInt_tendsto_vertical {F : ℂ → ℂ}
    (h2 : Integrable (fun t : ℝ => F ((2 : ℂ) + (t : ℂ) * Complex.I)))
    (hl : Integrable (fun t : ℝ => F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
    (hu : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) + (T : ℂ) * Complex.I))
      atTop (nhds 0))
    (hd : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) - (T : ℂ) * Complex.I))
      atTop (nhds 0)) :
    Tendsto (fun T : ℝ =>
        (∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-T)..T, F ((2 : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ in (-T)..T, F (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
      atTop (nhds (Complex.I * ((∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))))) := by
  have hnegtop : Tendsto (fun T : ℝ => -T) atTop atBot := by
    rw [Filter.tendsto_atBot]
    intro a
    filter_upwards [Filter.eventually_ge_atTop (-a)] with T hT
    linarith
  have hC : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, F ((2 : ℂ) + (y : ℂ) * Complex.I)) atTop
      (nhds (∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral h2 hnegtop tendsto_id
  have hD : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T,
      F (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) atTop
      (nhds (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hl hnegtop tendsto_id
  have hcomb := ((hd.sub hu).add (hC.const_mul Complex.I)).sub (hD.const_mul Complex.I)
  simp only [sub_zero, zero_add] at hcomb
  have hlim : Complex.I * ((∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      = Complex.I * (∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I * (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by ring
  rw [hlim]
  exact hcomb.congr' (by filter_upwards with T; ring)

/-- The rectangle integral of `logDeriv Λ · Φ` over `[-1/2 - iT, 2 + iT]`. -/
lemma rectInt_strip_eq (T : ℝ) (F : ℂ → ℂ) :
    Commons.NumberTheory.Zeta.rectInt (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
        ((2 : ℂ) + (T : ℂ) * Complex.I) F =
      (∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) - (T : ℂ) * Complex.I)) -
      (∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-T)..T, F ((2 : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-T)..T, F (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
  have hzre : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = (-1 / 2 : ℝ) := by
    simp [Complex.sub_re, Complex.mul_re]
  have hzim : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T := by
    simp [Complex.sub_im, Complex.mul_im]
  have hwre : (((2 : ℂ) + (T : ℂ) * Complex.I)).re = (2 : ℝ) := by
    simp [Complex.add_re, Complex.mul_re]
  have hwim : (((2 : ℂ) + (T : ℂ) * Complex.I)).im = T := by
    simp [Complex.add_im, Complex.mul_im]
  unfold Commons.NumberTheory.Zeta.rectInt
  rw [hzre, hwre, hzim, hwim]
  simp only [Complex.ofReal_neg, Complex.ofReal_ofNat, neg_mul, sub_eq_add_neg, smul_eq_mul]

/-- The rectangle integral along the strip, with the limit taken as `T → ∞`. -/
lemma rectInt_tendsto_vertical' {F : ℂ → ℂ}
    (h2 : Integrable (fun t : ℝ => F ((2 : ℂ) + (t : ℂ) * Complex.I)))
    (hl : Integrable (fun t : ℝ => F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
    (hu : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) + (T : ℂ) * Complex.I))
      atTop (nhds 0))
    (hd : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 / 2)..(2 : ℝ), F ((x : ℂ) - (T : ℂ) * Complex.I))
      atTop (nhds 0)) :
    Tendsto (fun T : ℝ => Commons.NumberTheory.Zeta.rectInt (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
        ((2 : ℂ) + (T : ℂ) * Complex.I) F) atTop
      (nhds (Complex.I * ((∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))))) := by
  refine (rectInt_tendsto_vertical h2 hl hu hd).congr' ?_
  filter_upwards with T
  exact (rectInt_strip_eq T F).symm

/-! ## Integrability of the integrands on the two vertical lines -/

/-- The gamma factor of a Dirichlet character is a measurable function. -/
lemma measurable_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Measurable (gammaFactor χ) := by
  have hGammaℝ : Measurable Complex.Gammaℝ := by
    have h1 : Continuous (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) :=
      Continuous.const_cpow (by fun_prop)
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have h2 : Measurable (fun w : ℂ => Complex.Gamma (w / 2)) :=
      Meromorphic.Gamma.measurable.comp (by fun_prop)
    have hmul : Measurable (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) :=
      h1.measurable.mul h2
    rw [show Complex.Gammaℝ =
        (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) from
      funext (fun w => Complex.Gammaℝ_def w)]
    exact hmul
  rcases χ.even_or_odd with hE | hO
  · rw [show gammaFactor χ = Complex.Gammaℝ from funext hE.gammaFactor_def]
    exact hGammaℝ
  · rw [show gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) from funext hO.gammaFactor_def]
    exact hGammaℝ.comp (by fun_prop)

/-- The log-derivative of the gamma factor is measurable along a vertical line. -/
lemma measurable_logDeriv_gammaFactor_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => logDeriv (gammaFactor χ) ((σ : ℂ) + (t : ℂ) * Complex.I))
      volume := by
  have h : Measurable (fun t : ℝ => logDeriv (gammaFactor χ) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have heq : (fun t : ℝ => logDeriv (gammaFactor χ) ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        (fun t : ℝ => deriv (gammaFactor χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          gammaFactor χ ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      funext t; rw [logDeriv_apply]
    rw [heq]
    exact ((measurable_deriv (gammaFactor χ)).comp (by fun_prop)).div
      ((measurable_gammaFactor χ).comp (by fun_prop))
  exact h.aestronglyMeasurable

/-- The completed `L`-function is measurable, hence its log-derivative along a vertical line. -/
lemma measurable_logDeriv_completedL_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ : ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I))
      volume := by
  have hΛc : Continuous (DirichletCharacter.completedLFunction χ) :=
    (DirichletCharacter.differentiable_completedLFunction hχ).continuous
  have h : Measurable
      (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have heq : (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        (fun t : ℝ => deriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.completedLFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      funext t; rw [logDeriv_apply]
    rw [heq]
    exact ((measurable_deriv (DirichletCharacter.completedLFunction χ)).comp
      (by fun_prop)).div (hΛc.measurable.comp (by fun_prop))
  exact h.aestronglyMeasurable

/-- Integrability from a logarithmic pointwise bound. -/
lemma integrable_of_log_bound {g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable g volume)
    (hb : ∀ t : ℝ, ‖g t‖ ≤ C * (Real.log (2 + |t|) + 1) / (1 + t ^ 2)) :
    Integrable g volume := by
  have hdom : Integrable (fun t : ℝ => C * (8 * (1 + |t|) ^ (-((3:ℝ)/2)))) volume :=
    integrable_abs_rpow_neg.const_mul C
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall (fun t => ?_))
  have hden : (0:ℝ) < 1 + t ^ 2 := by positivity
  have h1 : (Real.log (2 + |t|) + 1) / (1 + t ^ 2) ≤ 8 * (1 + |t|) ^ (-((3:ℝ)/2)) :=
    log_weight_le_rpow t
  calc ‖g t‖ ≤ C * ((Real.log (2 + |t|) + 1) / (1 + t ^ 2)) := by
        rw [← mul_div_assoc]; exact hb t
    _ ≤ C * (8 * (1 + |t|) ^ (-((3:ℝ)/2))) := mul_le_mul_of_nonneg_left h1 hC

/-- Integrability of `F(σ+it)·Φ(σ+it)` from a logarithmic bound on `F`. -/
lemma integrable_mul_tentPhi_of_bound {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {Q : ℕ} (hQ : 2 ≤ Q) {F : ℂ → ℂ} (σ : ℝ) (hσ2 : σ ≤ 2)
    (hmeas : AEStronglyMeasurable (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I)) volume)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log (2 + |t|) + 1)) :
    Integrable (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I) *
      tentPhi L K Q ((σ : ℂ) + (t : ℂ) * Complex.I)) volume := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_tentPhi_bound hK h2K hQ
  have hMnn : 0 ≤ M := le_of_lt hM0
  refine integrable_of_log_bound (C := C * M) (mul_nonneg hC hMnn) ?_ ?_
  · refine hmeas.mul ?_
    exact ((tentPhi_diff L K Q).continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
  · intro t
    rw [norm_mul]
    have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ 2 := by
      have hre' : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by
        simp [Complex.add_re, Complex.mul_re]
      rw [hre']; exact hσ2
    have hΦ : ‖tentPhi L K Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M / (1 + t ^ 2) := by
      have h := hM ((σ : ℂ) + (t : ℂ) * Complex.I) hre
      have hnorm : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = σ ^ 2 + t ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        ring
      rw [hnorm] at h
      refine le_trans h ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg σ]
    calc ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * ‖tentPhi L K Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (C * (Real.log (2 + |t|) + 1)) * (M / (1 + t ^ 2)) :=
          mul_le_mul (hb t) hΦ (norm_nonneg _)
            (mul_nonneg hC (by
              have h := Real.log_nonneg (show (1:ℝ) ≤ 2 + |t| by linarith [abs_nonneg t])
              linarith))
      _ = (C * M) * (Real.log (2 + |t|) + 1) / (1 + t ^ 2) := by ring

/-- The logarithmic bound for `logDeriv γ` on `Re s = 2`. -/
lemma norm_logDeriv_gammaFactor_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) :
    ‖logDeriv (gammaFactor χ) ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      13 * (Real.log (2 + |t|) + 1) := by
  have h := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_gammaFactor_le χ t
  rw [show (2 : ℂ) + (t : ℂ) * Complex.I = (2 : ℂ) + Complex.I * (t : ℂ) by ring]
  have hlog : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hpi : Real.log Real.pi / 2 ≤ 2 := by
    have h' := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  linarith [h, hlog, hpi]

/-- The logarithmic bound for `logDeriv γ` on `Re s = -1/2`. -/
lemma norm_logDeriv_gammaFactor_left {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) :
    ‖logDeriv (gammaFactor χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      13 * (Real.log (2 + |t|) + 1) := by
  have h := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_gammaFactor_leftEdge χ t
  have hlog : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hpi : Real.log Real.pi / 2 ≤ 2 := by
    have h' := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  linarith [h, hlog, hpi]

/-- Integrability of `logDeriv γ · Φ` on `Re s = 2`. -/
lemma integrable_logDeriv_gammaFactor_mul_tentPhi_two {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {Q : ℕ} (hQ : 2 ≤ Q) :
    Integrable (fun t : ℝ => logDeriv (gammaFactor χ) ((2 : ℂ) + (t : ℂ) * Complex.I) *
      tentPhi L K Q ((2 : ℂ) + (t : ℂ) * Complex.I)) volume := by
  refine integrable_mul_tentPhi_of_bound hK h2K hQ (σ := 2) (by norm_num)
    (measurable_logDeriv_gammaFactor_line χ 2) (C := 13) (by norm_num) ?_
  intro t
  exact norm_logDeriv_gammaFactor_two χ t

/-- Integrability of `logDeriv γ · Φ` on `Re s = -1/2`. -/
lemma integrable_logDeriv_gammaFactor_mul_tentPhi_left {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {Q : ℕ} (hQ : 2 ≤ Q) :
    Integrable (fun t : ℝ => logDeriv (gammaFactor χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
      tentPhi L K Q (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) volume := by
  refine integrable_mul_tentPhi_of_bound hK h2K hQ (σ := -1 / 2) (by norm_num)
    (measurable_logDeriv_gammaFactor_line χ (-1 / 2)) (C := 13) (by norm_num) ?_
  intro t
  exact norm_logDeriv_gammaFactor_left χ t
/-- The logarithmic bound for `logDeriv Λ` on `Re s = 2`. -/
lemma norm_logDeriv_completedL_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      21 * (Real.log (N : ℝ) + 1) * (Real.log (2 + |t|) + 1) := by
  have h := Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le χ hχ t
  have hlog : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le (n := N)))
  rw [show (2 : ℂ) + (t : ℂ) * Complex.I = (2 : ℂ) + Complex.I * (t : ℂ) by ring]
  nlinarith [h, hlog, hlogN, mul_nonneg hlogN hlog]

/-- The logarithmic bound for `logDeriv Λ` on `Re s = -1/2`. -/
lemma norm_logDeriv_completedL_left {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (t : ℝ) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      300 * (Real.log (N : ℝ) + 1) * (Real.log (2 + |t|) + 1) := by
  set s : ℂ := (((-1 / 2 : ℝ) : ℂ)) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = (-1 / 2 : ℝ) := by rw [hsdef]; simp [Complex.add_re, Complex.mul_re]
  have hN1 : N ≠ 1 := by rintro rfl; exact hχ (Subsingleton.elim χ 1)
  have hγ := norm_logDeriv_gammaFactor_left χ t
  have hL := logDeriv_LFunction_leftEdge_uniform χ hχ hχprim t
  have hγ' : ‖logDeriv (gammaFactor χ) s‖ ≤ 13 * (Real.log (2 + |t|) + 1) := by
    rw [hsdef]; exact hγ
  have hL' : ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      100 * (Real.log (N : ℝ) + Real.log (2 + |t|) + 1) := by
    rw [hsdef]; exact hL
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hγne : gammaFactor χ s ≠ 0 := by
    rw [hsdef]
    exact gammaFactor_ne_zero_of_re_eq_neg_half χ (by simp [Complex.add_re, Complex.mul_re])
  have hLne : DirichletCharacter.LFunction χ s ≠ 0 := by
    rw [hsdef]
    exact Commons.NumberTheory.DirichletCharacter.LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
  have hΛeq : gammaFactor χ s * DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1)]
    field_simp
  have hΛne : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    rw [← hΛeq]; exact mul_ne_zero hγne hLne
  have hsplit : logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s + logDeriv (gammaFactor χ) s := by
    have hfun : DirichletCharacter.LFunction χ =
        (fun z => DirichletCharacter.completedLFunction χ z / gammaFactor χ z) :=
      funext (fun z => DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN1))
    have h1 : logDeriv (DirichletCharacter.LFunction χ) s =
        logDeriv (DirichletCharacter.completedLFunction χ) s - logDeriv (gammaFactor χ) s := by
      rw [hfun]
      exact logDeriv_div (f := DirichletCharacter.completedLFunction χ) (g := gammaFactor χ) s
        hΛne hγne ((DirichletCharacter.differentiable_completedLFunction hχ) s)
        (by rw [hsdef]; exact differentiableAt_gammaFactor_at_neg_half χ t)
    rw [h1]; ring
  have hlog2nn : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlogNnn : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le (n := N)))
  have hlogN1 : 1 ≤ Real.log (N : ℝ) + 1 := by linarith
  rw [hsplit]
  calc ‖logDeriv (DirichletCharacter.LFunction χ) s + logDeriv (gammaFactor χ) s‖
      ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ + ‖logDeriv (gammaFactor χ) s‖ :=
        norm_add_le _ _
    _ ≤ 100 * (Real.log (N : ℝ) + Real.log (2 + |t|) + 1) +
          13 * (Real.log (2 + |t|) + 1) := add_le_add hL' hγ'
    _ ≤ 300 * (Real.log (N : ℝ) + 1) * (Real.log (2 + |t|) + 1) := by
        nlinarith [hlog2nn, hlogN1, hlogNnn,
          mul_nonneg (by linarith : (0:ℝ) ≤ Real.log (N : ℝ) + 1) hlog2nn,
          mul_nonneg hlogNnn hlog2nn]

/-- Integrability of `logDeriv Λ · Φ` on `Re s = 2`. -/
lemma integrable_logDeriv_completedL_mul_tentPhi_two {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {Q : ℕ} (hQ : 2 ≤ Q) :
    Integrable (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (t : ℂ) * Complex.I) * tentPhi L K Q ((2 : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hlogN : 0 ≤ (Real.log (N : ℝ) + 1) := by
    have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
    have h2 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg h
    linarith
  refine integrable_mul_tentPhi_of_bound hK h2K hQ (σ := 2) (by norm_num)
    (measurable_logDeriv_completedL_line χ hχ 2) (C := 21 * (Real.log (N : ℝ) + 1))
    (by positivity) ?_
  intro t
  exact norm_logDeriv_completedL_two χ hχ t

/-- Integrability of `logDeriv Λ · Φ` on `Re s = -1/2`. -/
lemma integrable_logDeriv_completedL_mul_tentPhi_left {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {Q : ℕ} (hQ : 2 ≤ Q) :
    Integrable (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
      tentPhi L K Q (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hlogN : 0 ≤ (Real.log (N : ℝ) + 1) := by
    have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
    have h2 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg h
    linarith
  refine integrable_mul_tentPhi_of_bound hK h2K hQ (σ := -1 / 2) (by norm_num)
    (measurable_logDeriv_completedL_line χ hχ (-1 / 2)) (C := 300 * (Real.log (N : ℝ) + 1))
    (by positivity) ?_
  intro t
  exact norm_logDeriv_completedL_left χ hχ hχprim t
/-! ## Elementary limits -/

/-- `log (a (T+3)) / (1 + T²) → 0` as `T → ∞`, for `a ≥ 1`. -/
lemma tendsto_log_mul_div_sq {a : ℝ} (ha : 1 ≤ a) :
    Tendsto (fun T : ℝ => Real.log (a * (T + 3)) / (1 + T ^ 2)) atTop (nhds 0) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hbdd : Tendsto (fun T : ℝ => (Real.log a + 3) * T⁻¹) atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (Real.log a + 3)
  refine squeeze_zero' ?_ ?_ hbdd
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have h1 : 1 ≤ a * (T + 3) := by nlinarith
    have h2 : 0 < 1 + T ^ 2 := by nlinarith
    exact div_nonneg (Real.log_nonneg h1) h2.le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have h3 : 0 < 1 + T ^ 2 := by nlinarith
    have hT3 : 0 < T + 3 := by linarith
    have hTpos : 0 < T := by linarith
    have hlog : Real.log (a * (T + 3)) = Real.log a + Real.log (T + 3) :=
      Real.log_mul ha0.ne' hT3.ne'
    have hsub : Real.log (T + 3) ≤ T + 2 := by
      have := Real.log_le_sub_one_of_pos hT3; linarith
    have hA : Real.log (a * (T + 3)) ≤ Real.log a + (T + 2) := by rw [hlog]; linarith
    have hla : 0 ≤ Real.log a := Real.log_nonneg ha
    have hTle : T ≤ T ^ 2 := by nlinarith
    have hmain : (Real.log a + (T + 2)) * T ≤ (Real.log a + 3) * (1 + T ^ 2) := by
      have h1 : Real.log a * T ≤ Real.log a * T ^ 2 := mul_le_mul_of_nonneg_left hTle hla
      have h2 : T ^ 2 + 2 * T ≤ 3 * T ^ 2 := by nlinarith
      nlinarith [h1, h2, hla, sq_nonneg T]
    calc Real.log (a * (T + 3)) / (1 + T ^ 2)
        ≤ (Real.log a + (T + 2)) / (1 + T ^ 2) :=
          div_le_div_of_nonneg_right hA h3.le
      _ ≤ (Real.log a + 3) * T⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ h3]
          rw [show (Real.log a + 3) / T * (1 + T ^ 2)
              = (Real.log a + 3) * (1 + T ^ 2) / T by ring]
          rw [le_div_iff₀ hTpos]
          exact hmain

/-- `log (T + b) / √(1 + T²) → 0` as `T → ∞`. -/
lemma tendsto_log_add_div_sqrt (b : ℝ) :
    Tendsto (fun T : ℝ => Real.log (T + b) / Real.sqrt (1 + T ^ 2)) atTop (nhds 0) := by
  have hlim : Tendsto (fun T : ℝ => (4 * (2:ℝ) ^ ((1:ℝ)/4)) * T ^ (-((3:ℝ)/4)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (3:ℝ)/4) (by norm_num)).const_mul
      (4 * (2:ℝ) ^ ((1:ℝ)/4))
    simpa only [mul_zero] using h
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (max 1 (|b| + 2))] with T hT
    have hbT2 : |b| + 2 ≤ T := le_trans (le_max_right (1:ℝ) (|b| + 2)) hT
    have h2 : 0 < Real.sqrt (1 + T ^ 2) := Real.sqrt_pos.mpr (by positivity)
    exact div_nonneg (Real.log_nonneg (by linarith [neg_le_abs b, hbT2])) h2.le
  · filter_upwards [eventually_ge_atTop (max 1 (|b| + 2))] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hT0 : 0 < T := by linarith
    have hbT2 : |b| + 2 ≤ T := le_trans (le_max_right (1:ℝ) (|b| + 2)) hT
    have hb : 0 ≤ T + b := by linarith [neg_le_abs b]
    have hTb1 : 1 ≤ T + b := by linarith [neg_le_abs b]
    have hlog : Real.log (T + b) ≤ 4 * (T + b) ^ ((1:ℝ)/4) := by
      have h := Real.log_le_rpow_div hb (by norm_num : (0:ℝ) < (1:ℝ)/4)
      rw [div_eq_mul_inv, show ((1:ℝ)/4)⁻¹ = (4:ℝ) by norm_num] at h
      linarith
    have hb2 : T + b ≤ 2 * T := by linarith [le_abs_self b]
    have hpow : (T + b) ^ ((1:ℝ)/4) ≤ (2 * T) ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow hb hb2 (by norm_num)
    have h2T : (2 * T) ^ ((1:ℝ)/4) = 2 ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4) :=
      Real.mul_rpow (by norm_num) hT0.le
    have hsqrt : T ≤ Real.sqrt (1 + T ^ 2) := by
      rw [Real.le_sqrt hT0.le (by positivity)]
      nlinarith
    have hstep : Real.log (T + b) / Real.sqrt (1 + T ^ 2)
        ≤ 4 * (2 ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) / T := by
      apply div_le_div₀ ?_ ?_ hT0 hsqrt
      · positivity
      · calc Real.log (T + b) ≤ 4 * (T + b) ^ ((1:ℝ)/4) := hlog
          _ ≤ 4 * (2 * T) ^ ((1:ℝ)/4) := by linarith
          _ = 4 * (2 ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) := by rw [h2T]
    have hTp : T ^ ((1:ℝ)/4) / T = T ^ (-((3:ℝ)/4)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one T, ← Real.rpow_add hT0]
      norm_num
    calc Real.log (T + b) / Real.sqrt (1 + T ^ 2)
        ≤ 4 * (2 ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) / T := hstep
      _ = (4 * 2 ^ ((1:ℝ)/4)) * (T ^ ((1:ℝ)/4) / T) := by ring
      _ = (4 * 2 ^ ((1:ℝ)/4)) * T ^ (-((3:ℝ)/4)) := by rw [hTp]

/-- `(1 + log (T + b))² / (1 + T²) → 0` as `T → ∞`. -/
lemma tendsto_one_add_log_sq_div (b : ℝ) :
    Tendsto (fun T : ℝ => (1 + Real.log (T + b)) ^ 2 / (1 + T ^ 2)) atTop (nhds 0) := by
  have h1 : Tendsto (fun T : ℝ => Real.log (T + b) / Real.sqrt (1 + T ^ 2)) atTop (nhds 0) :=
    tendsto_log_add_div_sqrt b
  have h2 : Tendsto (fun T : ℝ => (1:ℝ) / Real.sqrt (1 + T ^ 2)) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun T : ℝ => Real.sqrt (1 + T ^ 2)) atTop atTop := by
      apply tendsto_atTop_mono (f := fun T : ℝ => T) ?_ tendsto_id
      intro T
      have h1 : T ≤ |T| := le_abs_self T
      have h2 : |T| = Real.sqrt (T ^ 2) := (Real.sqrt_sq_eq_abs T).symm
      rw [h2] at h1
      exact le_trans h1 (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg T]))
    have hinv := tendsto_inv_atTop_zero.comp hsqrt
    simpa [one_div, Function.comp_def] using hinv
  have h3 : Tendsto (fun T : ℝ => (1 + Real.log (T + b)) / Real.sqrt (1 + T ^ 2))
      atTop (nhds 0) := by
    have heq : (fun T : ℝ => (1 + Real.log (T + b)) / Real.sqrt (1 + T ^ 2))
        = fun T => (Real.log (T + b) / Real.sqrt (1 + T ^ 2)) + 1 / Real.sqrt (1 + T ^ 2) := by
      funext T; ring
    rw [heq]; simpa using h1.add h2
  have h4 := h3.pow 2
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h4
  refine h4.congr' ?_
  filter_upwards with T
  rw [div_pow, sq, Real.sq_sqrt (by positivity)]

/-! ## Horizontal vanishing of the contour edges -/

/-- `tentPhi` at the origin. -/
lemma tentPhi_apply_zero (L K : ℝ) (Q : ℕ) :
    tentPhi L K Q 0 = tentK L K ((Real.log (Q : ℝ) : ℝ) : ℂ) := by
  simp [tentPhi]

section Horizontal

variable {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)

/-- Continuity of `logDeriv (gammaFactor χ)` along a horizontal segment of height `|v| ≥ 1`. -/
lemma continuousOn_logDeriv_gammaFactor_segment {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {v : ℝ} (hv : 1 ≤ |v|) :
    ContinuousOn (fun x : ℝ => logDeriv (DirichletCharacter.gammaFactor χ)
      ((x : ℂ) + (v : ℂ) * Complex.I)) (Set.uIcc (-1/2 : ℝ) 2) := by
  have h := ContinuousOn.comp (continuousOn_logDeriv_gammaFactor χ)
    (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (v : ℂ) * Complex.I)
      (Set.uIcc (-1/2 : ℝ) 2))
    (by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (-1/2 : ℝ) ≤ 2)] at hx
      have hre : (((x : ℂ) + (v : ℂ) * Complex.I)).re = x := by simp
      have him : (((x : ℂ) + (v : ℂ) * Complex.I)).im = v := by simp
      refine ⟨by rw [hre]; linarith [hx.1], ?_⟩
      intro h0
      have h2 : (((x : ℂ) + (v : ℂ) * Complex.I)).im = (0 : ℂ).im := by
        simpa only using congrArg Complex.im h0
      rw [him, Complex.zero_im] at h2
      rw [h2, abs_zero] at hv
      linarith)
  simpa [Function.comp_def] using h

/-- Interval integrability of `‖logDeriv (gammaFactor χ)‖` along a horizontal segment. -/
lemma intervalIntegrable_norm_logDeriv_gammaFactor_segment {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {v : ℝ} (hv : 1 ≤ |v|) :
    IntervalIntegrable (fun x : ℝ => ‖logDeriv (DirichletCharacter.gammaFactor χ)
      ((x : ℂ) + (v : ℂ) * Complex.I)‖) volume (-1/2) 2 :=
  (continuousOn_logDeriv_gammaFactor_segment χ hv).norm.intervalIntegrable

/-- Interval integrability of `logDeriv (gammaFactor χ) · Φ` along a horizontal segment. -/
lemma intervalIntegrable_gammaFactor_mul_tentPhi_segment {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {Q : ℕ} {v : ℝ} (hv : 1 ≤ |v|) :
    IntervalIntegrable (fun x : ℝ => logDeriv (DirichletCharacter.gammaFactor χ)
      ((x : ℂ) + (v : ℂ) * Complex.I) * tentPhi L K Q ((x : ℂ) + (v : ℂ) * Complex.I))
      volume (-1/2) 2 := by
  refine ContinuousOn.intervalIntegrable ?_
  exact (continuousOn_logDeriv_gammaFactor_segment χ hv).mul
    ((tentPhi_diff L K Q).continuous.comp_continuousOn (by fun_prop :
      ContinuousOn (fun x : ℝ => (x : ℂ) + (v : ℂ) * Complex.I) (Set.uIcc (-1/2 : ℝ) 2)))

end Horizontal

/-- The horizontal edges vanish in the limit, for the gamma factor. -/
lemma horizontal_gamma_vanishing {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {Q : ℕ} (hQ : 2 ≤ Q) :
    (Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (T : ℂ) * Complex.I) *
          tentPhi L K Q ((x : ℂ) + (T : ℂ) * Complex.I)) atTop (nhds 0)) ∧
    (Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) - (T : ℂ) * Complex.I) *
          tentPhi L K Q ((x : ℂ) - (T : ℂ) * Complex.I)) atTop (nhds 0)) := by
  obtain ⟨M, hM0, hMb⟩ := exists_norm_tentPhi_bound (L := L) (K := K) hK h2K (Q := Q) hQ
  obtain ⟨C, hC0, hCb⟩ := horizontalGamma_logDeriv_bound χ
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
  have hkey : ∀ v : ℝ, 2 ≤ |v| →
      ‖(∫ x : ℝ in (-1/2)..2, logDeriv (DirichletCharacter.gammaFactor χ)
          ((x : ℂ) + (v : ℂ) * Complex.I) * tentPhi L K Q ((x : ℂ) + (v : ℂ) * Complex.I))‖
        ≤ (M * C) * (Real.log ((N:ℝ) * (|v| + 3)) / (1 + v ^ 2)) := by
    intro v hv
    have hnorm : (∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) ≤ C * Real.log ((N:ℝ) * (|v| + 3)) := by
      by_cases hv0 : 0 ≤ v
      · have h := (hCb |v| hv).1
        simpa [abs_of_nonneg hv0] using h
      · have hvneg : v < 0 := not_le.mp hv0
        have h := (hCb |v| hv).2
        simpa [abs_of_neg hvneg, Complex.ofReal_neg, neg_mul, neg_neg] using h
    have hv1 : 1 ≤ |v| := le_trans (by norm_num : (1:ℝ) ≤ 2) hv
    have hb := Commons.Analysis.Integral.norm_intervalIntegral_mul_le
      (F := fun u : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) u)
      (Φ := tentPhi L K Q) hM0 hMb hv1
      (intervalIntegrable_norm_logDeriv_gammaFactor_segment χ hv1)
      (intervalIntegrable_gammaFactor_mul_tentPhi_segment (N := N) χ (Q := Q) hv1)
    calc ‖(∫ x : ℝ in (-1/2)..2, logDeriv (DirichletCharacter.gammaFactor χ)
            ((x : ℂ) + (v : ℂ) * Complex.I) * tentPhi L K Q ((x : ℂ) + (v : ℂ) * Complex.I))‖
        ≤ (M / (1 + v ^ 2)) * (∫ x : ℝ in (-1/2)..2,
            ‖logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖) := hb
      _ ≤ (M / (1 + v ^ 2)) * (C * Real.log ((N:ℝ) * (|v| + 3))) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = (M * C) * (Real.log ((N:ℝ) * (|v| + 3)) / (1 + v ^ 2)) := by ring
  have hlim : Tendsto (fun T : ℝ => (M * C) * (Real.log ((N:ℝ) * (T + 3)) / (1 + T ^ 2)))
      atTop (nhds 0) := by
    simpa using (tendsto_log_mul_div_sq hN1).const_mul (M * C)
  constructor
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
    filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT
    have h0 : (0:ℝ) ≤ T := by linarith
    simpa [abs_of_nonneg h0] using hkey T (by rw [abs_of_nonneg h0]; linarith)
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
    filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT
    have h0 : (0:ℝ) ≤ T := by linarith
    have h := hkey (-T) (by rw [abs_neg, abs_of_nonneg h0]; linarith)
    simpa [abs_neg, abs_of_nonneg h0, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, neg_sq] using h

/-- Continuity of `logDeriv Λ` along a horizontal segment avoiding the zeros of `Λ`. -/
lemma continuousOn_logDeriv_completedL_segment {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {v : ℝ}
    (hnz : ∀ x : ℝ, x ∈ Set.uIcc (-1/2 : ℝ) 2 →
      completedLFunction χ ((x : ℂ) + (v : ℂ) * Complex.I) ≠ 0) :
    ContinuousOn (fun x : ℝ => logDeriv (completedLFunction χ)
      ((x : ℂ) + (v : ℂ) * Complex.I)) (Set.uIcc (-1/2 : ℝ) 2) :=
  (continuousOn_logDeriv_completedL χ hχ).comp (by fun_prop) hnz

/-- `log (N (s+3))² / (1 + s²) → 0`. -/
lemma tendsto_log_N_sq_div {N : ℕ} [NeZero N] :
    Tendsto (fun s : ℝ => (Real.log ((N:ℝ) * (s + 3)))^2 / (1 + s^2)) atTop (nhds 0) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
  have hNpos : 0 < (N:ℝ) := by linarith
  have hb : Tendsto (fun s : ℝ => (1 + Real.log (N:ℝ))^2 *
      ((1 + Real.log (s + 3))^2 / (1 + s^2))) atTop (nhds 0) := by
    simpa using (tendsto_one_add_log_sq_div 3).const_mul ((1 + Real.log (N:ℝ))^2)
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards with s
    exact div_nonneg (sq_nonneg _) (by positivity)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    have hs3 : 0 < s + 3 := by linarith
    have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
    have hlog3 : 0 ≤ Real.log (s+3) := Real.log_nonneg (by linarith)
    have hlog : Real.log ((N:ℝ)*(s+3)) = Real.log (N:ℝ) + Real.log (s+3) :=
      Real.log_mul hNpos.ne' hs3.ne'
    rw [hlog]
    have hle : Real.log (N:ℝ) + Real.log (s+3) ≤ (1 + Real.log (N:ℝ)) * (1 + Real.log (s+3)) := by
      nlinarith
    have h2 : 0 ≤ Real.log (N:ℝ) + Real.log (s+3) := by linarith
    have hp := pow_le_pow_left₀ h2 hle 2
    have h4 : 0 < 1 + s^2 := by positivity
    calc (Real.log (N:ℝ) + Real.log (s+3))^2 / (1 + s^2)
        ≤ ((1 + Real.log (N:ℝ)) * (1 + Real.log (s+3)))^2 / (1 + s^2) :=
          div_le_div_of_nonneg_right hp h4.le
      _ = (1 + Real.log (N:ℝ))^2 * ((1 + Real.log (s + 3))^2 / (1 + s^2)) := by ring

/-- The horizontal edges vanish along the good heights, for the completed `L`-function. -/
lemma horizontal_completedL_tendsto {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {Q : ℕ} (hQ : 2 ≤ Q) {c : ℝ} (hc : 0 < c) {T' : ℝ → ℝ}
    (hT' : ∀ T : ℝ, 1 ≤ T → T + 1 ≤ T' T)
    (hsep : ∀ T : ℝ, 1 ≤ T → ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
      c / Real.log ((N : ℝ) * (T' T + 3)) ≤ |ρ.im - T' T|)
    (hsep' : ∀ T : ℝ, 1 ≤ T → ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
      c / Real.log ((N : ℝ) * (T' T + 3)) ≤ |ρ.im + T' T|) :
    (Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv (completedLFunction χ) ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
          tentPhi L K Q ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0)) ∧
    (Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv (completedLFunction χ) ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
          tentPhi L K Q ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0)) := by
  obtain ⟨M, hM0, hMb⟩ := exists_norm_tentPhi_bound (L := L) (K := K) hK h2K (Q := Q) hQ
  obtain ⟨C, hC0, hCb⟩ := exists_bound_integral_logDeriv_completedL_horizontal χ hχ hχprim
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
  have hNpos : 0 < (N:ℝ) := by linarith
  have hT'tend : Tendsto T' atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (b - 1)] with T h1 h2
    exact le_trans (by linarith) (hT' T h1)
  have hlim : Tendsto (fun T : ℝ => (M * C * (2 + |Real.log c|)) *
      ((Real.log ((N:ℝ) * (T' T + 3)))^2 / (1 + (T' T)^2))) atTop (nhds 0) := by
    simpa using ((tendsto_log_N_sq_div (N := N)).comp hT'tend).const_mul
      (M * C * (2 + |Real.log c|))
  have hlarge : ∀ᶠ T : ℝ in atTop, c ≤ Real.log ((N:ℝ) * (T' T + 3)) := by
    have hlogtend : Tendsto (fun T : ℝ => Real.log ((N:ℝ) * (T + 4))) atTop atTop := by
      have h1 : Tendsto (fun T : ℝ => (N:ℝ) * (T + 4)) atTop atTop := by
        have h2 : Tendsto (fun T : ℝ => T + 4) atTop atTop := by
          simpa [add_comm] using Filter.tendsto_atTop_add_const_left atTop (4:ℝ) tendsto_id
        exact h2.const_mul_atTop hNpos
      exact Real.tendsto_log_atTop.comp h1
    filter_upwards [hlogtend.eventually (eventually_ge_atTop c), eventually_ge_atTop (1:ℝ)]
      with T h1 h2
    refine le_trans h1 (Real.log_le_log (by positivity) ?_)
    have h3 : T + 4 ≤ T' T + 3 := by have := hT' T h2; linarith
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hkey : ∀ v : ℝ, 2 ≤ |v| → c ≤ Real.log ((N:ℝ) * (|v| + 3)) →
      (∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|v| + 3)) ≤ |ρ.im - (|v|)|) →
      (∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|v| + 3)) ≤ |ρ.im + (|v|)|) →
      ‖(∫ x : ℝ in (-1/2)..2, logDeriv (completedLFunction χ)
          ((x : ℂ) + (v : ℂ) * Complex.I) * tentPhi L K Q ((x : ℂ) + (v : ℂ) * Complex.I))‖
        ≤ (M * C * (2 + |Real.log c|)) *
            ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := by
    intro v hv hcl hs1 hs2
    have hLpos : 0 < Real.log ((N:ℝ) * (|v| + 3)) := by
      apply Real.log_pos
      nlinarith [hN1, abs_nonneg v]
    have hδ0 : 0 < c / Real.log ((N:ℝ) * (|v| + 3)) := div_pos hc hLpos
    have hδ1 : c / Real.log ((N:ℝ) * (|v| + 3)) ≤ 1 := by
      rw [div_le_one hLpos]; exact hcl
    -- nonvanishing on the segment, from the separation
    have hnz : ∀ x : ℝ, x ∈ Set.uIcc (-1/2 : ℝ) 2 →
        completedLFunction χ ((x : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
      intro x hx h0
      have him : (((x : ℂ) + (v : ℂ) * Complex.I)).im = v := by simp
      by_cases hv0 : 0 ≤ v
      · have h1 := hs1 _ h0
        rw [him] at h1
        have hz : |v - (|v|)| = 0 := by rw [abs_of_nonneg hv0, sub_self, abs_zero]
        rw [hz] at h1
        linarith
      · have hvneg : v < 0 := not_le.mp hv0
        have h1 := hs2 _ h0
        rw [him] at h1
        have hz : |v + (|v|)| = 0 := by rw [abs_of_neg hvneg, add_neg_cancel, abs_zero]
        rw [hz] at h1
        linarith
    -- the norm-integral bound on the line `Im = v`
    have hIb : (∫ x : ℝ in (-1/2)..2, ‖logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) ≤
        C * Real.log ((N:ℝ) * (|v| + 3)) *
          (Real.log ((N:ℝ) * (|v| + 3)) + Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3))))) := by
      by_cases hv0 : 0 ≤ v
      · have h := (hCb |v| hv (c / Real.log ((N:ℝ) * (|v| + 3))) hδ0 hδ1 hs1 hs2).1
        simpa [abs_of_nonneg hv0] using h
      · have hvneg : v < 0 := not_le.mp hv0
        have h := (hCb |v| hv (c / Real.log ((N:ℝ) * (|v| + 3))) hδ0 hδ1 hs1 hs2).2
        simpa [abs_of_neg hvneg, Complex.ofReal_neg, neg_mul, neg_neg] using h
    have hb := Commons.Analysis.Integral.norm_intervalIntegral_mul_le
      (F := fun u : ℂ => logDeriv (completedLFunction χ) u) (Φ := tentPhi L K Q)
      hM0 hMb (le_trans (by norm_num : (1:ℝ) ≤ 2) hv)
      ((continuousOn_logDeriv_completedL_segment χ hχ hnz).norm.intervalIntegrable)
      (((continuousOn_logDeriv_completedL_segment χ hχ hnz).mul
        ((tentPhi_diff L K Q).continuous.comp_continuousOn (by fun_prop :
          ContinuousOn (fun x : ℝ => (x : ℂ) + (v : ℂ) * Complex.I)
            (Set.uIcc (-1/2 : ℝ) 2)))).intervalIntegrable)
    have hLv1 : 1 ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
      have h5 : (5:ℝ) ≤ (N:ℝ) * (|v| + 3) := by nlinarith [hN1, abs_nonneg v]
      have he : Real.exp 1 ≤ 5 := by linarith [Real.exp_one_lt_d9]
      calc (1:ℝ) ≤ Real.log 5 := by
            rw [Real.le_log_iff_exp_le (by norm_num)]; exact he
        _ ≤ Real.log ((N:ℝ) * (|v| + 3)) := Real.log_le_log (by norm_num) h5
    have hlogδ : Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))) ≤
        Real.log ((N:ℝ) * (|v| + 3)) + |Real.log c| := by
      have hLne : Real.log ((N:ℝ) * (|v| + 3)) ≠ 0 := ne_of_gt hLpos
      have h1 : 1 / (c / Real.log ((N:ℝ) * (|v| + 3))) =
          Real.log ((N:ℝ) * (|v| + 3)) / c := by
        rw [one_div_div]
      rw [h1, Real.log_div hLne hc.ne']
      have h2 : Real.log (Real.log ((N:ℝ) * (|v| + 3))) ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
        have := Real.log_le_sub_one_of_pos hLpos
        linarith
      have h3 : - Real.log c ≤ |Real.log c| := neg_le_abs _
      linarith
    have hD : 0 < 1 + v ^ 2 := by positivity
    have hstep : (M / (1 + v ^ 2)) * (C * Real.log ((N:ℝ) * (|v| + 3)) *
        (Real.log ((N:ℝ) * (|v| + 3)) +
          Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3))))))
        ≤ (M * C * (2 + |Real.log c|)) *
            ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := by
      have hD : (0:ℝ) < 1 + v ^ 2 := by positivity
      have hZ : Real.log ((N:ℝ) * (|v| + 3)) * (Real.log ((N:ℝ) * (|v| + 3)) +
          Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))
          ≤ (2 + |Real.log c|) * (Real.log ((N:ℝ) * (|v| + 3)))^2 := by
        have h2 : Real.log ((N:ℝ) * (|v| + 3)) ≤ (Real.log ((N:ℝ) * (|v| + 3)))^2 := by
          nlinarith [hLv1]
        have h4 : 0 ≤ |Real.log c| := abs_nonneg _
        nlinarith [hlogδ, h2, h4, hLv1, hLpos]
      have hmain := mul_le_mul_of_nonneg_left hZ (le_of_lt (mul_pos hM0 hC0))
      have hkey2 : M * (C * Real.log ((N:ℝ) * (|v| + 3)) * (Real.log ((N:ℝ) * (|v| + 3)) +
            Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))) / (1 + v ^ 2)
          ≤ (M * C * (2 + |Real.log c|) * (Real.log ((N:ℝ) * (|v| + 3)))^2) / (1 + v ^ 2) :=
        (div_le_div_iff_of_pos_right hD).mpr (by linarith [hmain])
      calc (M / (1 + v ^ 2)) * (C * Real.log ((N:ℝ) * (|v| + 3)) *
              (Real.log ((N:ℝ) * (|v| + 3)) +
                Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3))))))
          = M * (C * Real.log ((N:ℝ) * (|v| + 3)) * (Real.log ((N:ℝ) * (|v| + 3)) +
                Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))) / (1 + v ^ 2) := by ring
        _ ≤ (M * C * (2 + |Real.log c|) * (Real.log ((N:ℝ) * (|v| + 3)))^2) / (1 + v ^ 2) := hkey2
        _ = (M * C * (2 + |Real.log c|)) *
              ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := by ring
    calc ‖(∫ x : ℝ in (-1/2)..2, logDeriv (completedLFunction χ)
            ((x : ℂ) + (v : ℂ) * Complex.I) * tentPhi L K Q ((x : ℂ) + (v : ℂ) * Complex.I))‖
        ≤ (M / (1 + v ^ 2)) * (∫ x : ℝ in (-1/2)..2,
            ‖logDeriv (completedLFunction χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖) := hb
      _ ≤ (M / (1 + v ^ 2)) * (C * Real.log ((N:ℝ) * (|v| + 3)) *
            (Real.log ((N:ℝ) * (|v| + 3)) +
              Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))) :=
          mul_le_mul_of_nonneg_left hIb (by positivity)
      _ ≤ (M * C * (2 + |Real.log c|)) *
            ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := hstep
  have hT'2 : ∀ T : ℝ, 1 ≤ T → 2 ≤ |T' T| := by
    intro T hT
    rw [abs_of_nonneg (by linarith [hT' T hT])]
    linarith [hT' T hT]
  constructor
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ), hlarge] with T h1 h2
    have habs : |T' T| = T' T := abs_of_nonneg (by linarith [hT' T h1])
    have hs1 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|T' T| + 3)) ≤ |ρ.im - (|T' T|)| := by
      intro ρ hρ; rw [habs]; exact hsep T h1 ρ hρ
    have hs2 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|T' T| + 3)) ≤ |ρ.im + (|T' T|)| := by
      intro ρ hρ; rw [habs]; exact hsep' T h1 ρ hρ
    have hcl : c ≤ Real.log ((N:ℝ) * (|T' T| + 3)) := by rw [habs]; exact h2
    simpa [habs, neg_sq] using hkey (T' T) (hT'2 T h1) hcl hs1 hs2
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ), hlarge] with T h1 h2
    have habs : |T' T| = T' T := abs_of_nonneg (by linarith [hT' T h1])
    have habs2 : |-(T' T)| = T' T := by rw [abs_neg, habs]
    have hs1 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|-(T' T)| + 3)) ≤ |ρ.im - (|-(T' T)|)| := by
      intro ρ hρ; rw [habs2]; exact hsep T h1 ρ hρ
    have hs2 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|-(T' T)| + 3)) ≤ |ρ.im + (|-(T' T)|)| := by
      intro ρ hρ; rw [habs2]; exact hsep' T h1 ρ hρ
    have hcl : c ≤ Real.log ((N:ℝ) * (|-(T' T)| + 3)) := by rw [habs2]; exact h2
    have h := hkey (-(T' T)) (by rw [abs_neg]; exact hT'2 T h1) hcl hs1 hs2
    simpa [habs2, habs, neg_sq, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using h

/-- Contour integral of `logDeriv γ · G` for an odd character: the logarithmic derivative of the
gamma factor is holomorphic on the rectangle, so the integral vanishes. -/
lemma rectInt_logDeriv_gammaFactor_mul_eq_odd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im) (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) (hO : χ.Odd) :
    rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * G s) = 0 := by
  have hre_ge : ∀ s ∈ rectSet z w, -(1 : ℝ) < s.re := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    linarith [hre.1, hz1]
  have hgf : DirichletCharacter.gammaFactor χ = fun s => Complex.Gammaℝ (s + 1) :=
    funext hO.gammaFactor_def
  rw [hgf]
  have hdig : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + 1) / 2)) (rectSet z w) :=
    differentiableOn_digamma_shift (c := 1) (fun s hs => digamma_re_shift_one (hre_ge s hs))
  have hGd : DifferentiableOn ℂ (fun s : ℂ =>
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) * G s)
      (rectSet z w) :=
    (DifferentiableOn.add (differentiableOn_const _) (hdig.div_const 2)).mul hG.differentiableOn
  rw [rectInt_congr_boundary' (f := fun s => logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s * G s)
    (g := fun s => (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) * G s)
    ?_]
  · exact rectInt_eq_zero_of_differentiableOn hGd
  · intro s hs
    have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
    have h1 : 0 < (s + 1).re := by
      have h2 : (s + 1).re = s.re + 1 := by simp
      rw [h2]; linarith
    have hcomp : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + 1) (x := s)
        (differentiableAt_Gammaℝ (s + 1) h1) (by fun_prop)
      simpa [Function.comp_def] using h
    rw [hcomp, logDeriv_Gammaℝ_formula (s + 1) h1]

/-- The residue identity for the gamma factor: the difference of the two vertical integrals of
`logDeriv γ · Φ`, normalised by `1/(2π)`, equals `-(if χ.Even then Φ 0 else 0)`. -/
lemma gammaFactor_shift_identity {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {Q : ℕ} (hQ : 2 ≤ Q) :
    (1 / (2 * (Real.pi : ℂ))) * ((∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ)
        ((2 : ℂ) + (t : ℂ) * Complex.I) * tentPhi L K Q ((2 : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          tentPhi L K Q (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      = -(if χ.Even then tentPhi L K Q 0 else 0) := by
  set F : ℂ → ℂ := fun u => logDeriv (DirichletCharacter.gammaFactor χ) u * tentPhi L K Q u
    with hF
  obtain ⟨hu, hd⟩ := horizontal_gamma_vanishing (L := L) (K := K) hK h2K (χ := χ) (Q := Q) hQ
  have h2int : Integrable (fun t : ℝ => F ((2 : ℂ) + (t : ℂ) * Complex.I)) volume := by
    have h := integrable_logDeriv_gammaFactor_mul_tentPhi_two (L := L) (K := K) hK h2K
      (χ := χ) (Q := Q) hQ
    simpa [hF] using h
  have hlint : Integrable (fun t : ℝ => F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) volume := by
    have h := integrable_logDeriv_gammaFactor_mul_tentPhi_left (L := L) (K := K) hK h2K
      (χ := χ) (Q := Q) hQ
    simpa [hF] using h
  have hlim1 : Tendsto (fun T : ℝ => rectInt (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
      ((2 : ℂ) + (T : ℂ) * Complex.I) F) atTop
      (nhds (Complex.I * ((∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))))) :=
    rectInt_tendsto_vertical' (F := F) h2int hlint (by simpa [hF] using hu) (by simpa [hF] using hd)
  have hgoal : (∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = -(if χ.Even then 2 * (Real.pi : ℂ) * tentPhi L K Q 0 else 0) := by
    rcases χ.even_or_odd with hE | hO
    · rw [if_pos hE]
      have hconst : ∀ T : ℝ, 0 < T → rectInt (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((2 : ℂ) + (T : ℂ) * Complex.I) F = -(2 * (Real.pi : ℂ) * Complex.I) * tentPhi L K Q 0 := by
        intro T hT
        have hzre : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re <
            (((2 : ℂ) + (T : ℂ) * Complex.I)).re := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).re = 2 by simp]
          norm_num
        have hzim : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im <
            (((2 : ℂ) + (T : ℂ) * Complex.I)).im := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).im = T by simp]
          linarith
        have hz1 : -(1 : ℝ) < (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp]
          norm_num
        have h0in : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re < 0 ∧
            0 < (((2 : ℂ) + (T : ℂ) * Complex.I)).re ∧
            (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im < 0 ∧
            0 < (((2 : ℂ) + (T : ℂ) * Complex.I)).im := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).re = 2 by simp,
            show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).im = T by simp]
          exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
        have h := rectInt_logDeriv_gammaFactor_mul_eq (N := N) χ (G := tentPhi L K Q)
          (hG := tentPhi_diff L K Q) (z := (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I))
          (w := ((2 : ℂ) + (T : ℂ) * Complex.I)) hzre hzim hz1 h0in hE
        simpa [hF] using h
      have hlim2 : Tendsto (fun T : ℝ => rectInt (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((2 : ℂ) + (T : ℂ) * Complex.I) F) atTop
          (nhds (-(2 * (Real.pi : ℂ) * Complex.I) * tentPhi L K Q 0)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
        exact (hconst T (by linarith)).symm
      have huniq := tendsto_nhds_unique hlim1 hlim2
      apply mul_left_cancel₀ Complex.I_ne_zero
      rw [huniq]
      ring
    · rw [if_neg hO.not_even, neg_zero]
      have hconst : ∀ T : ℝ, 0 < T → rectInt (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((2 : ℂ) + (T : ℂ) * Complex.I) F = 0 := by
        intro T hT
        have hzre : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re <
            (((2 : ℂ) + (T : ℂ) * Complex.I)).re := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).re = 2 by simp]
          norm_num
        have hzim : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im <
            (((2 : ℂ) + (T : ℂ) * Complex.I)).im := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).im = T by simp]
          linarith
        have hz1 : -(1 : ℝ) < (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp]
          norm_num
        have h0in : (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re < 0 ∧
            0 < (((2 : ℂ) + (T : ℂ) * Complex.I)).re ∧
            (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im < 0 ∧
            0 < (((2 : ℂ) + (T : ℂ) * Complex.I)).im := by
          rw [show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).re = -1/2 by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).re = 2 by simp,
            show (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I).im = -T by simp,
            show (((2 : ℂ) + (T : ℂ) * Complex.I)).im = T by simp]
          exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
        have h := rectInt_logDeriv_gammaFactor_mul_eq_odd (N := N) χ (G := tentPhi L K Q)
          (hG := tentPhi_diff L K Q) (z := (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I))
          (w := ((2 : ℂ) + (T : ℂ) * Complex.I)) hzre hzim hz1 h0in hO
        simpa [hF] using h
      have hlim2 : Tendsto (fun T : ℝ => rectInt (((-1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I)
          ((2 : ℂ) + (T : ℂ) * Complex.I) F) atTop (nhds 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
        exact (hconst T (by linarith)).symm
      have huniq := tendsto_nhds_unique hlim1 hlim2
      exact mul_left_cancel₀ Complex.I_ne_zero (by rw [huniq, mul_zero])
  change (1 / (2 * (Real.pi : ℂ))) * ((∫ t : ℝ, F ((2 : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, F (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      = -(if χ.Even then tentPhi L K Q 0 else 0)
  rw [hgoal]
  by_cases hE : χ.Even
  · rw [if_pos hE, if_pos hE]
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      refine mul_ne_zero two_ne_zero ?_
      exact_mod_cast Real.pi_ne_zero
    field_simp
  · rw [if_neg hE, if_neg hE]
    ring

/-- The tent kernel evaluated on a zero of `Λ` (so `‖u‖ ≥ 2`) is `O(1/‖u‖²)`. -/
lemma norm_tentPhi_zero_le {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {Q : ℕ} (hQ : 2 ≤ Q)
    {u : ℂ} (h1 : 0 < u.re) (h2 : u.re < 1) (h3 : 2 ≤ ‖u‖) :
    ‖tentPhi L K Q u‖ ≤ (16 / (Real.log (Q : ℝ)) ^ 2) / ‖u‖ ^ 2 := by
  have hQ1 : (1:ℝ) < (Q:ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlqpos : 0 < Real.log (Q:ℝ) := Real.log_pos hQ1
  have hne1 : u ≠ 1 := by
    intro hh; rw [hh] at h2; simp at h2
  have hz : (1 - u) * ((Real.log (Q:ℝ) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (fun hh => hne1 hh.symm))
      (Complex.ofReal_ne_zero.mpr hlqpos.ne')
  have hzre : 0 ≤ ((1 - u) * ((Real.log (Q:ℝ) : ℝ) : ℂ)).re := by
    have hres : ((1 - u) * ((Real.log (Q:ℝ) : ℝ) : ℂ)).re = (1 - u.re) * Real.log (Q:ℝ) := by
      rw [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_im, Complex.one_im]
      ring
    rw [hres]
    have hh : 0 ≤ 1 - u.re := by linarith
    positivity
  have hb := norm_tentK_strip (L := L) (K := K) hK h2K hz hzre
  have hnormz : ‖(1 - u) * ((Real.log (Q:ℝ) : ℝ) : ℂ)‖ = ‖1 - u‖ * Real.log (Q:ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlqpos]
  have h1u : ‖u‖ ≤ 2 * ‖1 - u‖ := by
    have h : ‖u‖ ≤ ‖1 - u‖ + 1 := by
      calc ‖u‖ = ‖(u - 1) + 1‖ := by ring_nf
        _ ≤ ‖u - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ = ‖1 - u‖ + 1 := by rw [show (1:ℂ) - u = -(u - 1) by ring, norm_neg, norm_one]
    linarith
  have hnormu : 0 < ‖u‖ := by linarith
  have h1upos : 0 < ‖1 - u‖ := by nlinarith [h1u, hnormu]
  calc ‖tentPhi L K Q u‖ = ‖tentK L K ((1 - u) * ((Real.log (Q:ℝ) : ℝ) : ℂ))‖ := rfl
    _ ≤ 4 / (‖1 - u‖ * Real.log (Q:ℝ)) ^ 2 := by rw [← hnormz]; exact hb
    _ = 4 / (‖1 - u‖ ^ 2 * (Real.log (Q:ℝ)) ^ 2) := by ring
    _ ≤ 16 / ((Real.log (Q:ℝ)) ^ 2 * ‖u‖ ^ 2) := by
        have h4 : ‖u‖ ^ 2 ≤ 4 * ‖1 - u‖ ^ 2 := by
          have := pow_le_pow_left₀ (norm_nonneg u) h1u 2
          nlinarith [this]
        rw [div_le_iff₀ (by positivity : 0 < ‖1 - u‖ ^ 2 * (Real.log (Q:ℝ)) ^ 2),
          div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < (Real.log (Q:ℝ)) ^ 2 * ‖u‖ ^ 2)]
        nlinarith [h4, sq_nonneg (Real.log (Q:ℝ))]
    _ = (16 / (Real.log (Q:ℝ)) ^ 2) / ‖u‖ ^ 2 := by
        rw [div_div]

/-- The divisor sum against the literal kernel of the target statement equals the divisor sum
against `tentPhi`. -/
lemma divisorSum_eq_target {L K : ℝ} {Q : ℕ} (hQ : 2 ≤ Q) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (R : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) *
        (Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * ((1 - u) * ((Real.log (Q : ℝ) : ℂ))))) *
          (((1 - Complex.exp (-(((K : ℝ) : ℂ) * ((1 - u) * ((Real.log (Q : ℝ) : ℂ)))))) /
              ((1 - u) * ((Real.log (Q : ℝ) : ℂ)))) ^ 2)))
      = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) * tentPhi L K Q u) := by
  have hQ1 : (1:ℝ) < (Q:ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlqpos : 0 < Real.log (Q:ℝ) := Real.log_pos hQ1
  refine finsum_congr (fun u => ?_)
  by_cases hu : u = 1
  · subst hu
    have h1 : DirichletCharacter.completedLFunction χ 1 ≠ 0 := completedLFunction_one_ne_zero χ hχ
    have hzero : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) R) (1:ℂ) = 0 := by
      by_cases hmem : (1:ℂ) ∈ Metric.closedBall (0:ℂ) R
      · exact divisor_zero_of_analytic_ne_zero (completedLFunction_analyticOnNhd χ hχ _) hmem h1
      · rw [MeromorphicOn.divisor_def]
        rw [if_neg]
        intro h; exact hmem h.2
    have hz : (1 - (1:ℂ)) * ((Real.log (Q : ℝ) : ℝ) : ℂ) = 0 := by simp
    rw [hzero]
    simp
  · have hz : (1 - u) * ((Real.log (Q : ℝ) : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr (fun hh => hu hh.symm))
        (Complex.ofReal_ne_zero.mpr hlqpos.ne')
    rw [tentPhi, tentK_eq_closed L K _ hz]
/-- The explicit-formula identity for the contour integral of `logDeriv Λ · Φ`. -/
lemma completedL_shift_identity {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {Q : ℕ} (hQ : 2 ≤ Q) {Z : ℂ}
    (hstrip : Tendsto (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) *
          tentPhi L K Q u) else 0)) atTop (nhds Z)) :
    (1 / (2 * (Real.pi : ℂ))) * ((∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (t : ℂ) * Complex.I) * tentPhi L K Q ((2 : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          tentPhi L K Q (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      = Z := by
  obtain ⟨c, hc0, hgood⟩ := goodHeight_separated χ hχ hχprim
  have hex : ∀ T : ℝ, ∃ T' : ℝ, 1 ≤ T → T + 1 ≤ T' ∧ T' ≤ T + 2 ∧
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        c / Real.log ((N : ℝ) * (T' + 3)) ≤ |ρ.im - T'|) ∧
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        c / Real.log ((N : ℝ) * (T' + 3)) ≤ |ρ.im + T'|) := by
    intro T
    by_cases hT : 1 ≤ T
    · obtain ⟨T', h1, h2, h3, h4⟩ := hgood T hT
      exact ⟨T', fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, fun hh => absurd hh hT⟩
  choose T' hT' using hex
  have hT'tend : Tendsto T' atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (b - 1)] with T h1 h2
    exact le_trans (by linarith) ((hT' T h1).1)
  set F : ℂ → ℂ := fun u => logDeriv (DirichletCharacter.completedLFunction χ) u *
    tentPhi L K Q u with hF
  have h2int : Integrable (fun t : ℝ => F ((2:ℂ) + (t:ℂ)*Complex.I)) volume := by
    have h := integrable_logDeriv_completedL_mul_tentPhi_two (L:=L) (K:=K) hK h2K
      (χ:=χ) hχ (Q:=Q) hQ
    simpa [hF] using h
  have hlint : Integrable (fun t : ℝ => F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)) volume := by
    have h := integrable_logDeriv_completedL_mul_tentPhi_left (L:=L) (K:=K) hK h2K
      (χ:=χ) hχ hχprim (Q:=Q) hQ
    simpa [hF] using h
  obtain ⟨hhu, hhd⟩ := horizontal_completedL_tendsto (L:=L) (K:=K) hK h2K χ hχ hχprim hQ hc0
    (fun T hT => (hT' T hT).1) (fun T hT => (hT' T hT).2.2.1) (fun T hT => (hT' T hT).2.2.2)
  have hright : Tendsto (fun T : ℝ => ∫ y : ℝ in (-(T' T))..(T' T), F ((2:ℂ) + (y:ℂ)*Complex.I))
      atTop (nhds (∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I))) :=
    (intervalIntegral_tendsto_integral h2int tendsto_neg_atTop_atBot tendsto_id).comp hT'tend
  have hleft : Tendsto (fun T : ℝ => ∫ y : ℝ in (-(T' T))..(T' T), F (((-1/2:ℝ):ℂ) + (y:ℂ)*Complex.I))
      atTop (nhds (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))) :=
    (intervalIntegral_tendsto_integral hlint tendsto_neg_atTop_atBot tendsto_id).comp hT'tend
  -- the residue identity at the good heights
  have hres : ∀ T : ℝ, 1 ≤ T → rectInt (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I)
      ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I) (fun u => logDeriv (DirichletCharacter.completedLFunction χ) u *
        tentPhi L K Q u)
      = 2 * (Real.pi : ℂ) * Complex.I * (∑ᶠ ρ : ℂ, (if |ρ.im| < T' T then
          (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
            tentPhi L K Q ρ) else 0)) := by
    intro T hT
    have hT'1 : T + 1 ≤ T' T := (hT' T hT).1
    have hsep1 := (hT' T hT).2.2.1
    have hsep2 := (hT' T hT).2.2.2
    have hpos : 0 < T' T := by linarith
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
    have hlogNpos : 0 < Real.log ((N : ℝ) * (T' T + 3)) := by
      apply Real.log_pos
      nlinarith
    have hδpos : 0 < c / Real.log ((N : ℝ) * (T' T + 3)) := div_pos hc0 hlogNpos
    obtain ⟨M0, hM00, hMb0⟩ := exists_norm_tentPhi_bound (L:=L) (K:=K) hK h2K (Q:=Q) hQ
    have hM0 : ∀ s ∈ rectSet (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I)
        ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I), ‖tentPhi L K Q s‖ ≤ M0 := by
      intro s hs
      obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
      rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re = -1/2 by simp,
        show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re = 2 by simp,
        Set.uIcc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)] at hre
      have h2s : s.re ≤ 2 := hre.2
      calc ‖tentPhi L K Q s‖ ≤ M0 / (1 + ‖s‖ ^ 2) := hMb0 s h2s
        _ ≤ M0 := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + ‖s‖ ^ 2)]
            nlinarith [hM00, norm_nonneg s]
    have hzre : (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re <
        (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re := by
      rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re = -1/2 by simp,
        show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re = 2 by simp]
      norm_num
    have hzim : (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).im <
        (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).im := by
      rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).im = -T' T by simp,
        show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).im = T' T by simp]
      linarith
    have h0in : (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re < 0 ∧
        0 < (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re ∧
        (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).im < 0 ∧
        0 < (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).im := by
      rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re = -1/2 by simp,
        show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re = 2 by simp,
        show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).im = -T' T by simp,
        show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).im = T' T by simp]
      exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
    have hins : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re < ρ.re ∧
        ρ.re < (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re := by
      intro ρ hρ
      have hs := completedL_zero_strip χ hχ hχprim hρ
      rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re = -1/2 by simp,
        show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re = 2 by simp]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hnz : ∀ s ∈ rectBoundary (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I)
        ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I),
        DirichletCharacter.completedLFunction χ s ≠ 0 := by
      intro s hs h0
      rcases hs with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
      · have h2 := hsep2 s h0
        rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).im = -T' T by simp] at him
        rw [him] at h2
        have hz0 : |-(T' T) + T' T| = 0 := by rw [neg_add_cancel, abs_zero]
        rw [hz0] at h2
        linarith
      · have h2 := hsep1 s h0
        rw [show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).im = T' T by simp] at him
        rw [him] at h2
        have hz0 : |T' T - T' T| = 0 := by rw [sub_self, abs_zero]
        rw [hz0] at h2
        linarith
      · have hre' : s.re = -1/2 := by
          rw [hre]; simp
        have hsform : s = (((-1/2 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) := by
          apply Complex.ext
          · rw [hre']; simp
          · simp
        rw [hsform] at h0
        have hs0 : (((-1/2:ℝ):ℂ) + (s.im:ℂ)*Complex.I) ≠ 0 := by
          intro hh
          have h2 := congrArg Complex.re hh
          simp at h2
        have hγ : DirichletCharacter.gammaFactor χ (((-1/2:ℝ):ℂ) + (s.im:ℂ)*Complex.I) ≠ 0 :=
          gammaFactor_ne_zero_of_re_gt_neg_one χ (by norm_num) hs0
        have hmul := completedL_eq_gammaFactor_mul_L χ
          (s := (((-1/2:ℝ):ℂ) + (s.im:ℂ)*Complex.I)) hs0 (by norm_num)
        rw [hmul] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · exact hγ h
        · exact LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim s.im h
      · have hre' : s.re = 2 := by
          rw [hre]; simp
        exact absurd h0 (completedLFunction_ne_zero_of_one_lt_re χ (by rw [hre']; norm_num))
    have h := rectInt_logDeriv_completed_entire_mul_eq χ hχ hχprim (tentPhi_diff L K Q)
      hzre hzim h0in hins hnz hM0
    rw [h]
    congr 1
    refine finsum_congr (fun ρ => ?_)
    by_cases hz : DirichletCharacter.completedLFunction χ ρ = 0
    · have hcond : ((((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re < ρ.re ∧
          ρ.re < (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re ∧
          (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).im < ρ.im ∧
          ρ.im < (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).im) ↔ |ρ.im| < T' T := by
        rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re = -1/2 by simp,
          show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re = 2 by simp,
          show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).im = -T' T by simp,
          show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).im = T' T by simp]
        have hzw := hins ρ hz
        rw [show (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I).re = -1/2 by simp,
          show (((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)).re = 2 by simp] at hzw
        constructor
        · intro hc
          exact abs_lt.mpr ⟨by linarith [hc.2.2.1], by linarith [hc.2.2.2]⟩
        · intro hc
          exact ⟨by linarith [hzw.1], by linarith [hzw.2],
            by linarith [(abs_lt.mp hc).1], by linarith [(abs_lt.mp hc).2]⟩
      exact if_congr hcond rfl rfl
    · have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ = 0 := by
        simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
      rw [hord]
      simp
  -- the two limits
  have hcomb : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in (-1/2)..2, F ((x:ℂ) - ((T' T:ℝ):ℂ)*Complex.I)) -
      (∫ x : ℝ in (-1/2)..2, F ((x:ℂ) + ((T' T:ℝ):ℂ)*Complex.I)) +
      Complex.I * (∫ y : ℝ in (-(T' T))..(T' T), F ((2:ℂ) + (y:ℂ)*Complex.I)) -
      Complex.I * (∫ y : ℝ in (-(T' T))..(T' T), F (((-1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)))
      atTop (nhds (Complex.I * ((∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
        (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))))) := by
    have h4 : Tendsto (fun T : ℝ =>
        ((∫ x : ℝ in (-1/2)..2, F ((x:ℂ) - ((T' T:ℝ):ℂ)*Complex.I)) -
          (∫ x : ℝ in (-1/2)..2, F ((x:ℂ) + ((T' T:ℝ):ℂ)*Complex.I))) +
        (Complex.I * (∫ y : ℝ in (-(T' T))..(T' T), F ((2:ℂ) + (y:ℂ)*Complex.I)) -
          Complex.I * (∫ y : ℝ in (-(T' T))..(T' T), F (((-1/2:ℝ):ℂ) + (y:ℂ)*Complex.I))))
        atTop (nhds ((0 - 0) + (Complex.I * (∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
          Complex.I * (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))))) :=
      (hhd.sub hhu).add (hright.const_mul Complex.I |>.sub (hleft.const_mul Complex.I))
    have hv : (0 - 0) + (Complex.I * (∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
        Complex.I * (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)))
        = Complex.I * ((∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
          (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))) := by ring
    rw [hv] at h4
    refine Tendsto.congr' (Filter.Eventually.of_forall (fun T => ?_)) h4
    ring
  have hlimrect : Tendsto (fun T : ℝ => rectInt (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I)
      ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I) F) atTop
      (nhds (Complex.I * ((∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
        (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))))) := by
    refine Tendsto.congr' (Filter.Eventually.of_forall (fun T => ?_)) hcomb
    exact (rectInt_strip_eq (T' T) F).symm
  have hreslim : Tendsto (fun T : ℝ => rectInt (((-1/2:ℝ):ℂ) - ((T' T:ℝ):ℂ)*Complex.I)
      ((2:ℂ) + ((T' T:ℝ):ℂ)*Complex.I) F) atTop
      (nhds (2 * (Real.pi : ℂ) * Complex.I * Z)) := by
    have h1 : Tendsto (fun T : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (∑ᶠ ρ : ℂ,
        (if |ρ.im| < T' T then (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
          tentPhi L K Q ρ) else 0))) atTop (nhds (2 * (Real.pi : ℂ) * Complex.I * Z)) :=
      (hstrip.comp hT'tend).const_mul (2 * (Real.pi : ℂ) * Complex.I)
    refine Tendsto.congr' ?_ h1
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    simpa [hF] using (hres T hT).symm
  have huniq : Complex.I * ((∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
      (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))) = 2 * (Real.pi : ℂ) * Complex.I * Z :=
    tendsto_nhds_unique hlimrect hreslim
  have hAB : (∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
      (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)) = 2 * (Real.pi : ℂ) * Z := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [huniq]
    ring
  change (1 / (2 * (Real.pi : ℂ))) * ((∫ t : ℝ, F ((2:ℂ) + (t:ℂ)*Complex.I)) -
      (∫ t : ℝ, F (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))) = Z
  rw [hAB]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  field_simp


/-! ## Strip sums tend to the limit of the ball sums (private copy) -/


/-- A zero of the completed L-function with `|Im u| < T` and `T ≥ 0` lies in the ball of
radius `T+1` (its real part is in `(0,1)`). -/
private lemma norm_le_of_zero_im_lt_priv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hu : DirichletCharacter.completedLFunction χ u = 0)
    (him : |u.im| < T) :
    ‖u‖ ≤ T + 1 := by
  have hstrip := completedL_zero_strip χ hχ hχprim hu
  have hre2 : u.re ^ 2 < 1 := by nlinarith [hstrip.1, hstrip.2]
  have him2 : u.im ^ 2 < T ^ 2 := by
    rw [sq_lt_sq]
    rwa [abs_of_nonneg hT]
  have hns : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsu : ‖u‖ ^ 2 < (T + 1) ^ 2 := by
    rw [hns]; nlinarith
  have h1 : 0 ≤ ‖u‖ := norm_nonneg u
  have h2 : 0 ≤ T + 1 := by linarith
  exact le_of_lt ((sq_lt_sq₀ h1 h2).mp hsu)

private theorem stripSum_tendsto_ball_private {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {Φ : ℂ → ℂ} {A : ℝ} (hA : 0 < A)
    (hΦ : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → ‖Φ u‖ ≤ A / ‖u‖ ^ 2)
    {Z : ℂ}
    (hZ : Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u) Filter.atTop (nhds Z)) :
    Filter.Tendsto (fun T : ℝ => ∑ᶠ u : ℂ,
        (if |u.im| < T then
          (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ u)
        else 0)) Filter.atTop (nhds Z) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by
    simpa [Λ] using DirichletCharacter.differentiable_completedLFunction hχ
  have hΛne : Λ ≠ 0 := by
    intro hzero
    have h0 : Λ 0 ≠ 0 := by
      simpa [Λ] using completedLFunction_zero_ne_zero χ hχ hχprim
    exact h0 (by rw [hzero]; rfl)
  have hfan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := fun U z _ => hΛdiff.analyticAt z
  let D : ℝ → Finset ℂ := fun R => (pf_divisor_support_finite χ hχ R).toFinset
  let g : ℂ → ℂ := fun u => ((analyticOrderNatAt Λ u : ℕ) : ℂ) * Φ u
  let B : ℝ → ℂ := fun R => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u
  let W : ℝ → ℂ := fun T => ∑ᶠ u : ℂ,
      (if |u.im| < T then (((analyticOrderNatAt Λ u : ℕ) : ℂ) * Φ u) else 0)
  have hZ' : Filter.Tendsto B Filter.atTop (nhds Z) := by
    simpa [B, Λ] using hZ
  have hDmem : ∀ (R : ℝ) (u : ℂ),
      u ∈ D R ↔ MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 := by
    intro R u
    simp only [D, Λ]
    rw [Set.Finite.mem_toFinset, Function.mem_support]
  have hΛzero_of_order_ne : ∀ u : ℂ, analyticOrderNatAt Λ u ≠ 0 → Λ u = 0 := by
    intro u hne
    by_contra hfz
    apply hne
    simp only [analyticOrderNatAt]
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hfz)]
    simp
  have hdivU : ∀ (R : ℝ) (u : ℂ), u ∈ D R →
      MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u = (analyticOrderNatAt Λ u : ℤ) := by
    intro R u hu
    have hdu : MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 := (hDmem R u).mp hu
    have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
      by_contra hout
      exact hdu (divisor_eq_zero_of_nmem hout)
    exact Commons.NumberTheory.DirichletCharacter.divisor_eq_analyticOrderNatAt (hfan _) huB
  -- Ball sum rewritten as a finite sum over the divisor support
  have hBR : ∀ R : ℝ, B R = ∑ u ∈ D R, g u := by
    intro R
    have hsupp : Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u) ⊆ ↑(D R) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hdu : MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 := by
        intro h0; exact hu (by simp [h0])
      exact (hDmem R u).mpr hdu
    calc B R = ∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u := rfl
      _ = ∑ u ∈ D R, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u :=
            finsum_eq_sum_of_support_subset _ hsupp
      _ = ∑ u ∈ D R, g u := by
            apply Finset.sum_congr rfl
            intro u hu
            simp only [g]
            rw [hdivU R u hu, Int.cast_natCast]
  -- Zero count in the ball as a finite sum over the divisor support
  obtain ⟨c0, hc0⟩ := completedL_zeroCount χ hχ hχprim
  set Cc : ℝ := max c0 1 with hCcdef
  have hCc_pos : 0 < Cc := lt_of_lt_of_le zero_lt_one (le_max_right c0 1)
  have hfinsumD : ∀ R : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℝ))
        = ∑ u ∈ D R, ((analyticOrderNatAt Λ u : ℕ) : ℝ) := by
    intro R
    have hsupp : Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℝ)) ⊆ ↑(D R) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hdu : MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 := by
        intro h0; exact hu (by simp [h0])
      exact (hDmem R u).mpr hdu
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hdivU R u hu, Int.cast_natCast]
  have hcountD : ∀ R : ℝ, 2 ≤ R →
      ∑ u ∈ D R, ((analyticOrderNatAt Λ u : ℕ) : ℝ)
        ≤ Cc * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
    intro R hR
    have h1 : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℝ))
        ≤ c0 * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
      simpa [Λ] using hc0 R hR
    rw [hfinsumD R] at h1
    have hR0 : 0 ≤ R := by linarith
    have hlog0 : 0 ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
      have h2 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      have h3 : 0 ≤ Real.log (N : ℝ) := logN_nonneg
      linarith
    have h2 : c0 * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)
        ≤ Cc * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
      have hc0le : c0 ≤ Cc := le_max_left c0 1
      have hfac : 0 ≤ R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by positivity
      calc c0 * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)
          = c0 * (R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) := by ring
        _ ≤ Cc * (R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_right hc0le hfac
        _ = Cc * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by ring
    linarith
  -- Strip sum rewritten as a finite sum over the divisor support filtered by `|Im| < T`
  have hW1 : ∀ T : ℝ, 0 ≤ T → W T = ∑ u ∈ (D (T + 1)).filter (fun u => |u.im| < T), g u := by
    intro T hT
    have hsupp : Function.support (fun u : ℂ =>
        (if |u.im| < T then (((analyticOrderNatAt Λ u : ℕ) : ℂ) * Φ u) else 0)) ⊆
        ↑((D (T + 1)).filter (fun u => |u.im| < T)) := by
      intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe, Finset.mem_filter]
      have hp : |u.im| < T := by
        by_contra h; rw [if_neg h] at hu; exact hu rfl
      refine ⟨?_, hp⟩
      rw [hDmem]
      have hmu : analyticOrderNatAt Λ u ≠ 0 := by
        intro h0
        apply hu
        rw [if_pos hp]
        simp [h0]
      have hLu : Λ u = 0 := hΛzero_of_order_ne u hmu
      have hb : u ∈ Metric.closedBall (0 : ℂ) (T + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_zero_im_lt_priv χ hχ hχprim hT hLu hp
      exact divisor_ne_zero_of_apply_eq_zero hΛdiff hΛne hb hLu
    calc W T = ∑ᶠ u : ℂ,
            (if |u.im| < T then (((analyticOrderNatAt Λ u : ℕ) : ℂ) * Φ u) else 0) := rfl
      _ = ∑ u ∈ (D (T + 1)).filter (fun u => |u.im| < T),
            (if |u.im| < T then (((analyticOrderNatAt Λ u : ℕ) : ℂ) * Φ u) else 0) :=
            finsum_eq_sum_of_support_subset _ hsupp
      _ = ∑ u ∈ (D (T + 1)).filter (fun u => |u.im| < T), g u := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [if_pos (Finset.mem_filter.mp hu).2]
  -- Main estimate: the strip sum is the ball sum minus a small "far" contribution.
  have hstep : ∀ T : ℝ, 2 ≤ T → ‖W T - B (T + 1)‖
      ≤ Cc * A * (T + 1) * (Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2) / T ^ 2 := by
    intro T hT
    have hTpos : 0 < T := by linarith
    have hT0 : 0 ≤ T := le_of_lt hTpos
    have hpart := Finset.sum_filter_add_sum_filter_not (D (T + 1)) (fun u => |u.im| < T) g
    have hWB : W T - B (T + 1)
        = - ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)), g u := by
      rw [hBR (T + 1), hW1 T hT0, ← hpart]; ring
    have hAT2 : 0 ≤ A / T ^ 2 := le_of_lt (div_pos hA (by positivity))
    have hkey : ‖W T - B (T + 1)‖
        ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
            ((analyticOrderNatAt Λ u : ℕ) : ℝ) * (A / T ^ 2) := by
      rw [hWB, norm_neg]
      calc ‖∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)), g u‖
          ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)), ‖g u‖ := norm_sum_le _ _
        _ ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt Λ u : ℕ) : ℝ) * (A / T ^ 2) := by
            apply Finset.sum_le_sum
            intro u hu
            have hmem := Finset.mem_filter.mp hu
            have huD : u ∈ D (T + 1) := hmem.1
            have hnp : ¬ (|u.im| < T) := hmem.2
            have hdu : MeromorphicOn.divisor Λ (Metric.closedBall 0 (T + 1)) u ≠ 0 :=
              (hDmem (T + 1) u).mp huD
            have hLu : Λ u = 0 := by
              have := pf_divisor_ne_zero_is_zero χ hχ (by simpa [Λ] using hdu)
              simpa [Λ] using this
            have hstrip := completedL_zero_strip χ hχ hχprim (by simpa [Λ] using hLu)
            have himT : T ≤ |u.im| := le_of_not_gt hnp
            have hu_norm : T ≤ ‖u‖ := le_trans himT (Complex.abs_im_le_norm u)
            have h2u : 2 ≤ ‖u‖ := le_trans hT hu_norm
            have hΦu : ‖Φ u‖ ≤ A / ‖u‖ ^ 2 := hΦ u hstrip.1 hstrip.2 h2u
            rw [norm_mul, Complex.norm_natCast]
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            refine le_trans hΦu ?_
            exact div_le_div_of_nonneg_left (le_of_lt hA) (by positivity)
              (pow_le_pow_left₀ hT0 hu_norm 2)
    have hsum_le : ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
          ((analyticOrderNatAt Λ u : ℕ) : ℝ) * (A / T ^ 2)
        ≤ (A / T ^ 2) * ∑ u ∈ D (T + 1), ((analyticOrderNatAt Λ u : ℕ) : ℝ) := by
      have hsub : (D (T + 1)).filter (fun u => ¬ (|u.im| < T)) ⊆ D (T + 1) :=
        Finset.filter_subset _ _
      calc ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt Λ u : ℕ) : ℝ) * (A / T ^ 2)
          = (∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt Λ u : ℕ) : ℝ)) * (A / T ^ 2) := (Finset.sum_mul _ _ _).symm
        _ = (A / T ^ 2) * (∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt Λ u : ℕ) : ℝ)) := by ring
        _ ≤ (A / T ^ 2) * (∑ u ∈ D (T + 1), ((analyticOrderNatAt Λ u : ℕ) : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hAT2
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun u _ _ => Nat.cast_nonneg _)
    have hfin : ∑ u ∈ D (T + 1), ((analyticOrderNatAt Λ u : ℕ) : ℝ)
        ≤ Cc * (T + 1) * (Real.log ((T + 1) + 2) + Real.log (N : ℝ) + 2) :=
      hcountD (T + 1) (by linarith)
    calc ‖W T - B (T + 1)‖
        ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
            ((analyticOrderNatAt Λ u : ℕ) : ℝ) * (A / T ^ 2) := hkey
      _ ≤ (A / T ^ 2) * (∑ u ∈ D (T + 1), ((analyticOrderNatAt Λ u : ℕ) : ℝ)) := hsum_le
      _ ≤ (A / T ^ 2) * (Cc * (T + 1) * (Real.log ((T + 1) + 2) + Real.log (N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hfin hAT2
      _ = Cc * A * (T + 1) * (Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2) / T ^ 2 := by ring
  -- The far contribution tends to zero.
  have hEtend : Tendsto (fun T : ℝ => Cc * A * (T + 1) *
      (Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2) / T ^ 2) atTop (nhds 0) := by
    have hg : Tendsto (fun T : ℝ => 2 * (Cc * A) *
        ((Real.log (T + 2) + (Real.log (N : ℝ) + 2 + Real.log 2)) / T)) atTop (nhds 0) := by
      have h := log_add_two_add_const_div_self_tendsto_zero (Real.log (N : ℝ) + 2 + Real.log 2)
      have hc : Tendsto (fun _ : ℝ => 2 * (Cc * A)) atTop (nhds (2 * (Cc * A))) :=
        tendsto_const_nhds
      simpa using hc.mul h
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hnum : 0 ≤ Cc * A * (T + 1) * (Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2) := by
        have h1 : 0 ≤ Real.log (T + 1 + 2) := Real.log_nonneg (by linarith)
        have h2 : 0 ≤ Real.log (N : ℝ) := logN_nonneg
        have h3 : 0 ≤ Cc * A := mul_nonneg (le_of_lt hCc_pos) (le_of_lt hA)
        have h4 : 0 ≤ T + 1 := by linarith
        have h5 : 0 ≤ Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2 := by linarith
        positivity
      exact div_nonneg hnum (sq_nonneg T)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hTpos : 0 < T := by linarith
      have hCcA : 0 ≤ Cc * A := mul_nonneg (le_of_lt hCc_pos) (le_of_lt hA)
      have hlog_ge : 0 ≤ Real.log (T + 3) + Real.log (N : ℝ) + 2 := by
        have h1 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
        have h2 : 0 ≤ Real.log (N : ℝ) := logN_nonneg
        linarith
      have hlog_le : Real.log (T + 3) ≤ Real.log (T + 2) + Real.log 2 := by
        have hle : T + 3 ≤ 2 * (T + 2) := by linarith
        have h := Real.log_le_log (by linarith : 0 < T + 3) hle
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : (T + 2) ≠ 0)] at h
        linarith
      have hcore : (T + 1) * (Real.log (T + 3) + Real.log (N : ℝ) + 2)
          ≤ 2 * T * (Real.log (T + 2) + (Real.log (N : ℝ) + 2 + Real.log 2)) := by
        have hT1 : T + 1 ≤ 2 * T := by linarith
        have hL : Real.log (T + 3) + Real.log (N : ℝ) + 2
            ≤ Real.log (T + 2) + (Real.log (N : ℝ) + 2 + Real.log 2) := by linarith
        calc (T + 1) * (Real.log (T + 3) + Real.log (N : ℝ) + 2)
            ≤ (2 * T) * (Real.log (T + 3) + Real.log (N : ℝ) + 2) :=
              mul_le_mul_of_nonneg_right hT1 hlog_ge
          _ ≤ (2 * T) * (Real.log (T + 2) + (Real.log (N : ℝ) + 2 + Real.log 2)) :=
              mul_le_mul_of_nonneg_left hL (by linarith)
      have hb : Cc * A * (T + 1) * (Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2) / T ^ 2
          ≤ 2 * (Cc * A) * ((Real.log (T + 2) + (Real.log (N : ℝ) + 2 + Real.log 2)) / T) := by
        rw [div_le_iff₀ (by positivity : 0 < T ^ 2)]
        have hmul := mul_le_mul_of_nonneg_left hcore hCcA
        have e1 : Cc * A * (T + 1) * (Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2)
            = Cc * A * ((T + 1) * (Real.log (T + 3) + Real.log (N : ℝ) + 2)) := by
          ring_nf
        have e2 : 2 * (Cc * A) * ((Real.log (T + 2) + (Real.log (N : ℝ) + 2 + Real.log 2)) / T)
              * T ^ 2
            = Cc * A * (2 * T * (Real.log (T + 2) + (Real.log (N : ℝ) + 2 + Real.log 2))) := by
          field_simp
        rw [e1, e2]
        exact hmul
      exact hb
  -- Conclude.
  have hWtend : Tendsto W atTop (nhds Z) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → dist (B R) Z < ε / 2 := by
      obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hZ') (ε / 2) hε2)
      exact ⟨R₀, hR₀⟩
    obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
        Cc * A * (T + 1) * (Real.log (T + 1 + 2) + Real.log (N : ℝ) + 2) / T ^ 2 < ε / 2 := by
      obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp ((tendsto_order.mp hEtend).2 (ε / 2) hε2)
      exact ⟨T₁, hT₁⟩
    refine ⟨max (max 2 T₁) (R₀ - 1), ?_⟩
    intro T hT
    have hT2 : 2 ≤ T :=
      le_trans (le_trans (le_max_left 2 T₁) (le_max_left (max 2 T₁) (R₀ - 1))) hT
    have hTT₁ : T₁ ≤ T :=
      le_trans (le_trans (le_max_right 2 T₁) (le_max_left (max 2 T₁) (R₀ - 1))) hT
    have hTR₀ : R₀ ≤ T + 1 := by
      have hle : R₀ - 1 ≤ T := le_trans (le_max_right (max 2 T₁) (R₀ - 1)) hT
      linarith
    rw [dist_eq_norm]
    have htri : ‖W T - Z‖ ≤ ‖W T - B (T + 1)‖ + ‖B (T + 1) - Z‖ := by
      calc ‖W T - Z‖ = ‖(W T - B (T + 1)) + (B (T + 1) - Z)‖ := by ring_nf
        _ ≤ ‖W T - B (T + 1)‖ + ‖B (T + 1) - Z‖ := norm_add_le _ _
    have hbad := hstep T hT2
    have hgood := hR₀ (T + 1) hTR₀
    rw [dist_eq_norm] at hgood
    have hbad' := hT₁ T hTT₁
    linarith
  simpa [W, Λ] using hWtend


/-! ## The target theorem (statement only; proof pending) -/

set_option linter.unusedVariables false in
theorem tentMellin_bridge_scale {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive) {Q : ℕ} [NeZero Q], N ≤ Q → ∀ Z : ℂ,
        Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
              (Complex.exp (-(((L - 2 * K : ℝ) : ℂ) * ((1 - u) * ((Real.log (Q : ℝ) : ℂ))))) *
                (((1 - Complex.exp (-(((K : ℝ) : ℂ) * ((1 - u) * ((Real.log (Q : ℝ) : ℂ)))))) /
                    ((1 - u) * ((Real.log (Q : ℝ) : ℂ)))) ^ 2)))
          Filter.atTop (nhds Z) →
        ∀ X : ℕ, (Q : ℝ) ^ L ≤ (X : ℝ) →
          ‖((Real.log (Q : ℝ) : ℂ))⁻¹ * (∑ n ∈ Finset.Icc 1 X,
              (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) *
                ((Commons.NumberTheory.Linnik.tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ)) + Z‖
          ≤ C * (((Q : ℝ) ^ (-(L - 2 * K))) +
              (Real.log (Q : ℝ))⁻¹ * ((Q : ℝ) ^ (-(3 / 2 : ℝ) * (L - 2 * K))) * (1 + Real.log (Q : ℝ))) := by
  refine ⟨20000, by norm_num, ?_⟩
  intro N _ χ hχ hχprim Q _ hNQ Z hZ X hX
  have hN2 : 2 ≤ N := by
    have hne : N ≠ 1 := by
      intro h
      apply hχ
      haveI : Subsingleton (DirichletCharacter ℂ N) := by rw [h]; infer_instance
      exact Subsingleton.elim χ 1
    have h1 : 1 ≤ N := NeZero.one_le
    omega
  have hQ2 : 2 ≤ Q := le_trans hN2 hNQ
  have hQ1 : (1:ℝ) < (Q:ℝ) := by exact_mod_cast (by omega : 1 < Q)
  have hlqpos : 0 < Real.log (Q:ℝ) := Real.log_pos hQ1
  have hApos : 0 < 16 / (Real.log (Q:ℝ)) ^ 2 := by positivity
  have hΦbound : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ →
      ‖tentPhi L K Q u‖ ≤ (16 / (Real.log (Q:ℝ)) ^ 2) / ‖u‖ ^ 2 :=
    fun u h1 h2 h3 => norm_tentPhi_zero_le hK h2K hQ2 h1 h2 h3
  have hZ' : Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) * tentPhi L K Q u) atTop (nhds Z) :=
    Tendsto.congr' (Filter.Eventually.of_forall (fun R => divisorSum_eq_target hQ2 χ hχ R)) hZ
  have hstrip := stripSum_tendsto_ball_private χ hχ hχprim hApos hΦbound hZ'
  have hAP := completedL_shift_identity (L:=L) (K:=K) hK h2K χ hχ hχprim (Q:=Q) hQ2 hstrip
  have hGS := gammaFactor_shift_identity (L:=L) (K:=K) hK h2K (χ:=χ) (Q:=Q) hQ2
  have hmel := mellin_sum (N:=N) χ hχ hχprim (L:=L) (K:=K) hK h2K (Q:=Q) hQ2 (X:=X) hX
  -- integrability of the four pieces
  have hIΛ2 := integrable_logDeriv_completedL_mul_tentPhi_two (L:=L) (K:=K) hK h2K (χ:=χ) hχ (Q:=Q) hQ2
  have hIγ2 := integrable_logDeriv_gammaFactor_mul_tentPhi_two (L:=L) (K:=K) hK h2K (χ:=χ) (Q:=Q) hQ2
  have hIΛl := integrable_logDeriv_completedL_mul_tentPhi_left (L:=L) (K:=K) hK h2K (χ:=χ) hχ hχprim (Q:=Q) hQ2
  have hIγl := integrable_logDeriv_gammaFactor_mul_tentPhi_left (L:=L) (K:=K) hK h2K (χ:=χ) (Q:=Q) hQ2
  -- pointwise splitting of `logDeriv Λ` on the two lines
  have hpt2 : ∀ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ)
      ((2:ℂ) + (t:ℂ)*Complex.I) = logDeriv (DirichletCharacter.gammaFactor χ)
      ((2:ℂ) + (t:ℂ)*Complex.I) + logDeriv (DirichletCharacter.LFunction χ)
      ((2:ℂ) + (t:ℂ)*Complex.I) := by
    intro t
    refine logDeriv_completedL_eq_add χ hχ ?_ ?_ ?_
    · intro hh
      have h2 := congrArg Complex.re hh
      simp at h2
    · rw [show ((2:ℂ) + (t:ℂ)*Complex.I).re = 2 by simp]
      norm_num
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ)
        (s := ((2:ℂ) + (t:ℂ)*Complex.I)) (Or.inl hχ) (by simp)
  have hptl : ∀ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ)
      (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) = logDeriv (DirichletCharacter.gammaFactor χ)
      (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) + logDeriv (DirichletCharacter.LFunction χ)
      (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) := by
    intro t
    refine logDeriv_completedL_eq_add χ hχ ?_ ?_ ?_
    · intro hh
      have h2 := congrArg Complex.re hh
      simp at h2
    · rw [show (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I).re = -1/2 by simp]
      norm_num
    · exact LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
  -- the `L`-integrals expressed through the others
  have hJL2 : (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
        tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I))
      = (∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
          tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I))
        - (∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
          tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I)) := by
    rw [← MeasureTheory.integral_sub hIΛ2 hIγ2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [hpt2 t]
    ring
  have hJLl : (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) *
        tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))
      = (∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) *
          tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))
        - (∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) *
          tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)) := by
    rw [← MeasureTheory.integral_sub hIΛl hIγl]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [hptl t]
    ring
  have hJA : (∫ t : ℝ, (- logDeriv (DirichletCharacter.LFunction χ) ((2:ℂ) + (t:ℂ)*Complex.I)) *
        tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I))
      = - (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
        tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I)) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  -- the unnormalised forms of the GS and AP identities
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  have hcancel : ∀ W : ℂ, (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * W) = W := by
    intro W
    rw [← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have hGS' : (∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
        tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I))
      - (∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) *
        tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))
      = -(if χ.Even then 2 * (Real.pi : ℂ) * tentPhi L K Q 0 else 0) := by
    have h := congrArg (fun w : ℂ => (2 * (Real.pi : ℂ)) * w) hGS
    rw [hcancel] at h
    by_cases hE : χ.Even
    · rw [if_pos hE] at h ⊢
      exact h.trans (by ring)
    · rw [if_neg hE] at h ⊢
      rw [h]
      ring
  have hAP' : (∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
        tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I))
      - (∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) *
        tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))
      = 2 * (Real.pi : ℂ) * Z := by
    have h := congrArg (fun w : ℂ => (2 * (Real.pi : ℂ)) * w) hAP
    rw [hcancel] at h
    exact h
  -- the key identity
  have hAZ : ((Real.log (Q:ℝ) : ℂ))⁻¹ * (∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log n / Real.log Q) : ℝ) : ℂ)) + Z
      = -(if χ.Even then tentPhi L K Q 0 else 0)
        - (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
            (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) * tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)) := by
    have hZeq : Z = (1 / (2 * (Real.pi : ℂ))) *
        ((∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
            tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I))
          - (∫ t : ℝ, logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) *
            tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))) := by
      rw [hAP']
      field_simp
    have hGSeq : -(if χ.Even then tentPhi L K Q 0 else 0) = (1 / (2 * (Real.pi : ℂ))) *
        ((∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) ((2:ℂ) + (t:ℂ)*Complex.I) *
            tentPhi L K Q ((2:ℂ) + (t:ℂ)*Complex.I))
          - (∫ t : ℝ, logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) *
            tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))) := by
      have h := congrArg (fun w : ℂ => (1 / (2 * (Real.pi : ℂ))) * w) hGS'
      rw [h]
      by_cases hE : χ.Even
      · rw [if_pos hE, if_pos hE]
        field_simp
      · rw [if_neg hE, if_neg hE]
        ring
    simp only [tentPhi] at hmel hJA hZeq hGSeq hJL2 hJLl ⊢
    rw [hmel, hJA, hZeq, hGSeq, hJL2, hJLl]
    ring
  -- the two numerical bounds
  have h1 : ‖-(if χ.Even then tentPhi L K Q 0 else 0)‖
      ≤ 4 * Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) * ((Real.log (Q:ℝ)) ^ 2)⁻¹ := by
    by_cases hE : χ.Even
    · rw [if_pos hE, norm_neg, tentPhi_apply_zero]
      exact norm_tentK_zero (L:=L) (K:=K) hK h2K (Q:=Q) hQ2
    · rw [if_neg hE, neg_zero, norm_zero]
      positivity
  have h2 : ‖(1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
        (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) * tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))‖
      ≤ 4000 * ((Real.log (Q:ℝ))⁻¹ * (Real.exp (-(3/2) * (L - 2 * K) * Real.log (Q:ℝ)) *
          (Real.log (Q:ℝ))⁻¹ * (1 + Real.log (Q:ℝ)))) :=
    leftEdge_L_bound (N:=N) χ hχ hχprim (L:=L) (K:=K) hK h2K (Q:=Q) hQ2 hNQ
  -- powers rewritten as exponentials
  have hrpow1 : (Q:ℝ) ^ (-(L - 2*K)) = Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < (Q:ℝ))]
    congr 1
    ring
  have hrpow2 : (Q:ℝ) ^ (-(3/2:ℝ) * (L - 2*K))
      = Real.exp (-(3/2) * (L - 2*K) * Real.log (Q:ℝ)) := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < (Q:ℝ))]
    congr 1
    ring
  have hlq5 : (1:ℝ) / 5 ≤ Real.log (Q:ℝ) := by
    have h2' : (1:ℝ) / 5 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    exact le_trans h2' (Real.log_le_log (by norm_num) (by exact_mod_cast hQ2))
  have hlqinv : (Real.log (Q:ℝ))⁻¹ ≤ 5 := by
    rw [inv_le_comm₀ hlqpos (by norm_num : (0:ℝ) < 5)]
    simpa using hlq5
  have hE1nn : 0 ≤ Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) := Real.exp_nonneg _
  have hE2nn : 0 ≤ Real.exp (-(3/2) * (L - 2*K) * Real.log (Q:ℝ)) := Real.exp_nonneg _
  have h1lq : 0 ≤ 1 + Real.log (Q:ℝ) := by linarith
  have hnum : 4 * Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) * ((Real.log (Q:ℝ)) ^ 2)⁻¹ +
        4000 * ((Real.log (Q:ℝ))⁻¹ * (Real.exp (-(3/2) * (L - 2 * K) * Real.log (Q:ℝ)) *
          (Real.log (Q:ℝ))⁻¹ * (1 + Real.log (Q:ℝ))))
      ≤ 20000 * (Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) +
        (Real.log (Q:ℝ))⁻¹ * Real.exp (-(3/2) * (L - 2*K) * Real.log (Q:ℝ)) *
          (1 + Real.log (Q:ℝ))) := by
    have hb1 : 4 * Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) * ((Real.log (Q:ℝ)) ^ 2)⁻¹
        ≤ 20000 * Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) := by
      have hsq : ((Real.log (Q:ℝ)) ^ 2)⁻¹ ≤ 25 := by
        rw [inv_le_comm₀ (by positivity : (0:ℝ) < (Real.log (Q:ℝ))^2) (by norm_num : (0:ℝ) < 25)]
        nlinarith [hlq5]
      nlinarith [hE1nn, hsq]
    have hb2 : 4000 * ((Real.log (Q:ℝ))⁻¹ * (Real.exp (-(3/2) * (L - 2 * K) * Real.log (Q:ℝ)) *
          (Real.log (Q:ℝ))⁻¹ * (1 + Real.log (Q:ℝ))))
        ≤ 20000 * ((Real.log (Q:ℝ))⁻¹ * Real.exp (-(3/2) * (L - 2*K) * Real.log (Q:ℝ)) *
          (1 + Real.log (Q:ℝ))) := by
      have hposinv : 0 < (Real.log (Q:ℝ))⁻¹ := inv_pos.mpr hlqpos
      have hstep : 4000 * ((Real.log (Q:ℝ))⁻¹ * (Real.log (Q:ℝ))⁻¹)
          ≤ 20000 * (Real.log (Q:ℝ))⁻¹ := by
        nlinarith [hlqinv, hlqpos, hposinv]
      have hfac : 0 ≤ Real.exp (-(3/2) * (L - 2*K) * Real.log (Q:ℝ)) * (1 + Real.log (Q:ℝ)) :=
        mul_nonneg hE2nn h1lq
      calc 4000 * ((Real.log (Q:ℝ))⁻¹ * (Real.exp (-(3/2) * (L - 2 * K) * Real.log (Q:ℝ)) *
              (Real.log (Q:ℝ))⁻¹ * (1 + Real.log (Q:ℝ))))
          = (4000 * ((Real.log (Q:ℝ))⁻¹ * (Real.log (Q:ℝ))⁻¹)) *
              (Real.exp (-(3/2) * (L - 2 * K) * Real.log (Q:ℝ)) * (1 + Real.log (Q:ℝ))) := by ring
        _ ≤ (20000 * (Real.log (Q:ℝ))⁻¹) *
              (Real.exp (-(3/2) * (L - 2 * K) * Real.log (Q:ℝ)) * (1 + Real.log (Q:ℝ))) :=
            mul_le_mul_of_nonneg_right hstep hfac
        _ = 20000 * ((Real.log (Q:ℝ))⁻¹ * Real.exp (-(3/2) * (L - 2*K) * Real.log (Q:ℝ)) *
              (1 + Real.log (Q:ℝ))) := by ring
    linarith [hb1, hb2]
  rw [hAZ]
  calc ‖-(if χ.Even then tentPhi L K Q 0 else 0)
        - (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
            (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) * tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))‖
      ≤ ‖-(if χ.Even then tentPhi L K Q 0 else 0)‖ +
        ‖(1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
            (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) * tentPhi L K Q (((-1/2:ℝ):ℂ) + (t:ℂ)*Complex.I))‖ :=
        norm_sub_le _ _
    _ ≤ 4 * Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) * ((Real.log (Q:ℝ)) ^ 2)⁻¹ +
        4000 * ((Real.log (Q:ℝ))⁻¹ * (Real.exp (-(3/2) * (L - 2 * K) * Real.log (Q:ℝ)) *
          (Real.log (Q:ℝ))⁻¹ * (1 + Real.log (Q:ℝ)))) := add_le_add h1 h2
    _ ≤ 20000 * (Real.exp (-(L - 2*K) * Real.log (Q:ℝ)) +
        (Real.log (Q:ℝ))⁻¹ * Real.exp (-(3/2) * (L - 2*K) * Real.log (Q:ℝ)) *
          (1 + Real.log (Q:ℝ))) := hnum
    _ = 20000 * ((Q:ℝ) ^ (-(L - 2 * K)) +
        (Real.log (Q : ℝ))⁻¹ * ((Q : ℝ) ^ (-(3 / 2 : ℝ) * (L - 2 * K))) *
          (1 + Real.log (Q : ℝ))) := by
        rw [hrpow1, hrpow2]


end Commons.NumberTheory.Linnik
