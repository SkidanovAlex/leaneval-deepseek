import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.first_mertens_bounded
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges
import Submission.Commons.NumberTheory.Mertens.prime_euler_constant_identity
import Submission.Commons.Analysis.Real.tail_integral_log10
import Submission.Commons.Analysis.Real.integrableOn_log10_div_sqrt
import Submission.Commons.NumberTheory.Zeta.theta_sub_id_integrableOn_Ioi
import Submission.Commons.NumberTheory.Mertens.logDiv_measurable
import Submission.Commons.NumberTheory.Mertens.corr_sum_tail_bound
import Submission.Commons.NumberTheory.Mertens.primeRecips_limit_rate

open Filter Finset Real MeasureTheory
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- `θ(x) − x`. -/
private def smE (t : ℝ) : ℝ := Chebyshev.theta t - t

/-- `logDiv x − log x` (first-Mertens remainder). -/
private def smh (x : ℝ) : ℝ := logDiv x - Real.log x

/-- `∑_{p ≤ x} 1/p − log log x`. -/
private def smf (x : ℝ) : ℝ := primeRecips x - Real.log (Real.log x)

/-- `(log x)^j ≤ (log x)^12` for `1 ≤ log x` and `j ≤ 12`. -/
private lemma log_pow_le_log12 {x : ℝ} (hlog : (1 : ℝ) ≤ Real.log x) {j : ℕ} (hj : j ≤ 12) :
    (Real.log x) ^ j ≤ (Real.log x) ^ 12 := pow_le_pow_right₀ hlog hj

/-- `∫_2^x 1/t dt = log x − log 2` for `2 ≤ x`. -/
private lemma integral_one_div_two {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (1 : ℝ) / t) = Real.log x - Real.log 2 := by
  have hxpos : 0 < x := by linarith
  have hi := integral_inv_of_pos (by norm_num : 0 < (2 : ℝ)) hxpos
  have hEq : (∫ t in (2 : ℝ)..x, (1 : ℝ) / t) = ∫ t in (2 : ℝ)..x, t⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIcc_of_le hx] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith
    field_simp [ht0]
  rw [hEq, hi]
  rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)]

/-- Decomposition `logDiv x − log x = (1 − log 2) + (θ x − x)/x + ∫_2^x (θ t − t)/t² dt`. -/
private lemma smh_decomp {x : ℝ} (hx : 2 ≤ x) :
    smh x = (1 - Real.log 2) + smE x / x +
      ∫ t in (2 : ℝ)..x, smE t / (t * t) := by
  have h1 := logDiv_eq_theta_div_add_integral hx
  have hθI : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * t)) volume 2 x :=
    intervalIntegrable_theta_div_id_sq hx
  have h1tI : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    intro z hz
    have hz2 : (2 : ℝ) ≤ z := by
      rw [Set.uIcc_of_le hx] at hz
      exact hz.1
    have hz0 : z ≠ 0 := by linarith
    fun_prop (disch := positivity)
  have hgI : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * t) - (1 : ℝ) / t) volume 2 x :=
    hθI.sub h1tI
  have hIntE : IntervalIntegrable (fun t : ℝ => smE t / (t * t)) volume 2 x := by
    unfold smE
    refine hgI.congr_uIoo ?_
    intro t ht
    have htI : t ∈ Set.Ioo (min (2 : ℝ) x) (max (2 : ℝ) x) := by simpa [Set.uIoo] using ht
    have hmin : min (2 : ℝ) x = 2 := min_eq_left hx
    have hmax : max (2 : ℝ) x = x := max_eq_right hx
    rw [hmin, hmax] at htI
    have htpos : 0 < t := lt_trans (by norm_num : 0 < (2 : ℝ)) htI.1
    field_simp [htpos.ne']
  have hcong : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * t)) =
      ∫ t in (2 : ℝ)..x, ((1 : ℝ) / t + smE t / (t * t)) := by
    unfold smE
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIcc_of_le hx] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith
    field_simp [ht0]
    ring
  have hsplit : (∫ t in (2 : ℝ)..x, ((1 : ℝ) / t + smE t / (t * t))) =
      (∫ t in (2 : ℝ)..x, (1 : ℝ) / t) + (∫ t in (2 : ℝ)..x, smE t / (t * t)) := by
    rw [intervalIntegral.integral_add h1tI hIntE]
  calc
    smh x = logDiv x - Real.log x := rfl
    _ = (Chebyshev.theta x / x + (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * t))) - Real.log x := by
        rw [h1]
    _ = (Chebyshev.theta x / x + (∫ t in (2 : ℝ)..x, ((1 : ℝ) / t + smE t / (t * t)))) - Real.log x := by
        rw [hcong]
    _ = (Chebyshev.theta x / x + ((∫ t in (2 : ℝ)..x, (1 : ℝ) / t) + (∫ t in (2 : ℝ)..x, smE t / (t * t)))) - Real.log x := by
        rw [hsplit]
    _ = (Chebyshev.theta x / x + ((Real.log x - Real.log 2) + (∫ t in (2 : ℝ)..x, smE t / (t * t)))) - Real.log x := by
        rw [integral_one_div_two hx]
    _ = (1 - Real.log 2) + smE x / x + (∫ t in (2 : ℝ)..x, smE t / (t * t)) := by
        have hx0 : x ≠ 0 := by linarith
        unfold smE
        field_simp [hx0]
        ring

/-- Improper integral `∫_x^∞ 1/(t log²t) dt = 1/log x` for `1 < x`. -/
private lemma mlr_integral_Ioi_inv_log_sq {x : ℝ} (hx : 1 < x) :
    (∫ t in Set.Ioi x, (1 : ℝ) / (t * (Real.log t) ^ 2)) = 1 / Real.log x := by
  have hEq : (∫ t in Set.Ioi x, (1 : ℝ) / (t * (Real.log t) ^ 2)) =
      ∫ t in Set.Ioi x, t⁻¹ / (Real.log t) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_trans hx (Set.mem_Ioi.mp ht)
    have ht0 : t ≠ 0 := by linarith
    field_simp [ht0]
  rw [hEq, integral_inv_div_log_sq_Ioi hx]
  exact inv_eq_one_div (Real.log x)

/-- `∫_Y^x 1/(t log²t) dt = 1/log Y − 1/log x` for `2 ≤ Y ≤ x`. -/
private lemma integral_one_div_log_sq_gen {Y x : ℝ} (hY : 2 ≤ Y) (hYx : Y ≤ x) :
    (∫ t in Y..x, (1 : ℝ) / (t * (Real.log t) ^ 2)) =
      (1 / Real.log Y - 1 / Real.log x) := by
  have hEq : (∫ t in Y..x, (1 : ℝ) / (t * (Real.log t) ^ 2)) =
      ∫ t in Y..x, t⁻¹ / (Real.log t) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htY : Y ≤ t := by
      rw [Set.uIcc_of_le hYx] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith [hY, htY]
    field_simp [ht0]
  have hY1 : (1 : ℝ) < Y := by linarith
  have hx1 : 1 < x := lt_of_lt_of_le hY1 hYx
  rw [hEq, integral_inv_div_log_sq hY1 hx1]
  simp [one_div]

/-- `logDiv t/(t log²t)` is interval-integrable on `[2,x]`. -/
private lemma intervalIntegrable_logDiv_div_id_log_sq_smh {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => smh t / (t * (Real.log t) ^ 2)) volume 2 x := by
  have h1tI : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (t * Real.log t)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    intro z hz
    have hz2 : (2 : ℝ) ≤ z := by
      rw [Set.uIcc_of_le hx] at hz
      exact hz.1
    have hz0 : z ≠ 0 := by linarith
    have hlogz : Real.log z ≠ 0 := by
      have h1z : (1 : ℝ) < z := by linarith
      exact ne_of_gt (Real.log_pos h1z)
    fun_prop (disch := positivity)
  have hdivI := intervalIntegrable_logDiv_div_id_log_sq hx
  refine (hdivI.sub h1tI).congr_uIoo ?_
  intro t ht
  have htI : t ∈ Set.Ioo (min (2 : ℝ) x) (max (2 : ℝ) x) := by simpa [Set.uIoo] using ht
  have hmin : min (2 : ℝ) x = 2 := min_eq_left hx
  have hmax : max (2 : ℝ) x = x := max_eq_right hx
  rw [hmin, hmax] at htI
  have ht2 : (2 : ℝ) < t := htI.1
  have htpos : 0 < t := lt_trans (by norm_num : 0 < (2 : ℝ)) ht2
  have h1t : (1 : ℝ) < t := lt_trans (by norm_num : (1 : ℝ) < 2) ht2
  have hlogpos : 0 < Real.log t := Real.log_pos h1t
  unfold smh
  field_simp [htpos.ne', hlogpos.ne']

/-- Decomposition of `smf x = ∑_{p≤x} 1/p − log log x`. -/
private lemma smf_decomp {x : ℝ} (hx : 2 ≤ x) :
    smf x = (1 - Real.log (Real.log 2)) + smh x / Real.log x +
      ∫ t in (2 : ℝ)..x, smh t / (t * (Real.log t) ^ 2) := by
  have h1 := primeRecips_eq_logDiv_div_log_add_integral hx
  have hlogx : Real.log x ≠ 0 := by
    have h1x : (1 : ℝ) < x := by linarith
    exact ne_of_gt (Real.log_pos h1x)
  have h1tI : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (t * Real.log t)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    intro z hz
    have hz2 : (2 : ℝ) ≤ z := by
      rw [Set.uIcc_of_le hx] at hz
      exact hz.1
    have hz0 : z ≠ 0 := by linarith
    have hlogz : Real.log z ≠ 0 := by
      have h1z : (1 : ℝ) < z := by linarith
      exact ne_of_gt (Real.log_pos h1z)
    fun_prop (disch := positivity)
  have hloglog : (∫ t in (2 : ℝ)..x, (1 : ℝ) / (t * Real.log t)) =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
    have hEq2 : (∫ t in (2 : ℝ)..x, (1 : ℝ) / (t * Real.log t)) =
        ∫ t in (2 : ℝ)..x, t⁻¹ / Real.log t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := by
        rw [Set.uIcc_of_le hx] at ht
        exact ht.1
      have ht0 : t ≠ 0 := by linarith
      field_simp [ht0]
    have hx1 : 1 < x := by linarith
    rw [hEq2, integral_inv_div_log (by norm_num : (1 : ℝ) < (2 : ℝ)) hx1]
  have hsplit0 : logDiv x / Real.log x = 1 + smh x / Real.log x := by
    unfold smh
    field_simp [hlogx]
    ring
  have hcongDiv : (∫ t in (2 : ℝ)..x, logDiv t / (t * (Real.log t) ^ 2)) =
      ∫ t in (2 : ℝ)..x, ((1 : ℝ) / (t * Real.log t) + smh t / (t * (Real.log t) ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIcc_of_le hx] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlogt : Real.log t ≠ 0 := by
      have h1t : (1 : ℝ) < t := by linarith
      exact ne_of_gt (Real.log_pos h1t)
    unfold smh
    field_simp [ht0, hlogt]
    ring
  have hIntE := intervalIntegrable_logDiv_div_id_log_sq_smh hx
  have hsplit : (∫ t in (2 : ℝ)..x, ((1 : ℝ) / (t * Real.log t) + smh t / (t * (Real.log t) ^ 2))) =
      (∫ t in (2 : ℝ)..x, (1 : ℝ) / (t * Real.log t)) +
        (∫ t in (2 : ℝ)..x, smh t / (t * (Real.log t) ^ 2)) := by
    rw [intervalIntegral.integral_add h1tI hIntE]
  calc
    smf x = primeRecips x - Real.log (Real.log x) := rfl
    _ = (logDiv x / Real.log x +
          (∫ t in (2 : ℝ)..x, logDiv t / (t * (Real.log t) ^ 2))) - Real.log (Real.log x) := by
        rw [h1]
    _ = (logDiv x / Real.log x +
          (∫ t in (2 : ℝ)..x, ((1 : ℝ) / (t * Real.log t) + smh t / (t * (Real.log t) ^ 2)))) - Real.log (Real.log x) := by
        rw [hcongDiv]
    _ = (logDiv x / Real.log x +
          ((∫ t in (2 : ℝ)..x, (1 : ℝ) / (t * Real.log t)) +
            (∫ t in (2 : ℝ)..x, smh t / (t * (Real.log t) ^ 2)))) - Real.log (Real.log x) := by
        rw [hsplit]
    _ = (1 + smh x / Real.log x + ((Real.log (Real.log x) - Real.log (Real.log 2)) +
          (∫ t in (2 : ℝ)..x, smh t / (t * (Real.log t) ^ 2)))) - Real.log (Real.log x) := by
        rw [hsplit0, hloglog]
    _ = (1 - Real.log (Real.log 2)) + smh x / Real.log x +
          (∫ t in (2 : ℝ)..x, smh t / (t * (Real.log t) ^ 2)) := by
        ring

/-- `(θ t − t)/(t*t)` is integrable on `[a,b]` for `2 ≤ a ≤ b`. -/
private lemma smE_integrableOn_Icc_gen {a b : ℝ} (h2a : 2 ≤ a) (hab : a ≤ b) :
    IntegrableOn (fun t : ℝ => smE t / (t * t)) (Set.Icc a b) volume := by
  have hθI : IntegrableOn (fun t : ℝ => Chebyshev.theta t / (t * t)) (Set.Icc a b) volume := by
    refine (integrableOn_theta_div_id_sq b).mono_set ?_
    intro t ht
    exact ⟨le_trans h2a ht.1, ht.2⟩
  have h1I : IntegrableOn (fun t : ℝ => (1 : ℝ) / t) (Set.Icc a b) volume := by
    refine ContinuousOn.integrableOn_Icc ?_
    intro z hz
    have hz0 : z ≠ 0 := by linarith [h2a, hz.1]
    fun_prop (disch := positivity)
  have hsub : IntegrableOn (fun t : ℝ => Chebyshev.theta t / (t * t) - (1 : ℝ) / t)
      (Set.Icc a b) volume := hθI.sub h1I
  have hEq : (fun t : ℝ => Chebyshev.theta t / (t * t) - (1 : ℝ) / t) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t : ℝ => smE t / (t * t) := by
    refine (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc) ?_
    intro t ht
    have ht0 : t ≠ 0 := by linarith [h2a, ht.1]
    unfold smE
    field_simp [ht0]
  exact hsub.congr_fun_ae hEq

/-- `smE t/(t*t)` is interval-integrable on `[a,b]` for `2 ≤ a ≤ b`. -/
private lemma smE_intervalIntegrable_gen {a b : ℝ} (h2a : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => smE t / (t * t)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine (smE_integrableOn_Icc_gen h2a hab).mono_set ?_
  intro t ht
  exact ⟨le_of_lt ht.1, ht.2⟩

/-- `logDiv t/(t log²t)` is integrable on `[a,b]` for `2 ≤ a ≤ b`. -/
private lemma logDiv_logsq_integrableOn_Icc_gen {a b : ℝ} (h2a : 2 ≤ a) (hab : a ≤ b) :
    IntegrableOn (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2)) (Set.Icc a b) volume := by
  have hb : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2)) volume 2 b :=
    intervalIntegrable_logDiv_div_id_log_sq (by linarith : 2 ≤ b)
  have hI : IntegrableOn (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2)) (Set.Icc 2 b) volume := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : 2 ≤ b)] at hb
  refine hI.mono_set ?_
  intro t ht
  exact ⟨le_trans h2a ht.1, ht.2⟩

/-- `smh t/(t log²t)` is integrable on `[a,b]` for `2 ≤ a ≤ b`. -/
private lemma smh_logsq_integrableOn_Icc_gen {a b : ℝ} (h2a : 2 ≤ a) (hab : a ≤ b) :
    IntegrableOn (fun t : ℝ => smh t / (t * (Real.log t) ^ 2)) (Set.Icc a b) volume := by
  have h1I : IntegrableOn (fun t : ℝ => (1 : ℝ) / (t * Real.log t)) (Set.Icc a b) volume := by
    refine ContinuousOn.integrableOn_Icc ?_
    intro z hz
    have hz0 : z ≠ 0 := by linarith [h2a, hz.1]
    have hlogz : Real.log z ≠ 0 := by
      have h1z : (1 : ℝ) < z := by linarith [h2a, hz.1]
      exact ne_of_gt (Real.log_pos h1z)
    fun_prop (disch := positivity)
  have hdivI := logDiv_logsq_integrableOn_Icc_gen h2a hab
  have hsub : IntegrableOn (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2) - (1 : ℝ) / (t * Real.log t))
      (Set.Icc a b) volume := hdivI.sub h1I
  have hEq : (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2) - (1 : ℝ) / (t * Real.log t)) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t : ℝ => smh t / (t * (Real.log t) ^ 2) := by
    refine (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc) ?_
    intro t ht
    have ht0 : t ≠ 0 := by linarith [h2a, ht.1]
    have hlogt : Real.log t ≠ 0 := by
      have h1t : (1 : ℝ) < t := by linarith [h2a, ht.1]
      exact ne_of_gt (Real.log_pos h1t)
    unfold smh
    field_simp [ht0, hlogt]
  exact hsub.congr_fun_ae hEq

/-- `smh t/(t log²t)` is interval-integrable on `[a,b]` for `2 ≤ a ≤ b`. -/
private lemma smh_logsq_intervalIntegrable_gen {a b : ℝ} (h2a : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => smh t / (t * (Real.log t) ^ 2)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine (smh_logsq_integrableOn_Icc_gen h2a hab).mono_set ?_
  intro t ht
  exact ⟨le_of_lt ht.1, ht.2⟩

/-- Improper integrability of `smE t/(t·t)` over `(Y, ∞)` from the RH pointwise bound. -/
private lemma smE_integrableOn_Ioi_of_rate {a₀ : ℝ} (ha0 : 2 ≤ a₀) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, a₀ ≤ t → |Chebyshev.theta t - t| ≤ C * Real.sqrt t * (Real.log t) ^ 10) :
    ∀ a : ℝ, a₀ ≤ a → IntegrableOn (fun t : ℝ => smE t / (t * t)) (Set.Ioi a) volume := by
  intro a haa0
  have h₁ : IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / (t * t)) (Set.Ioi a) volume :=
    Commons.NumberTheory.Zeta.theta_sub_id_integrableOn_Ioi ha0 hC hb a haa0
  have hEq : (fun t : ℝ => (Chebyshev.theta t - t) / (t * t)) =ᵐ[volume.restrict (Set.Ioi a)]
      fun t : ℝ => smE t / (t * t) := by
    refine (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi) ?_
    intro t ht
    unfold smE
    rfl
  exact h₁.congr_fun_ae hEq


/-- `a·√t/(t·t) = a/(t·√t)` for `0 < t`. -/
private lemma mul_sqrt_div_sq {a t : ℝ} (ht : 0 < t) :
    a * Real.sqrt t / (t * t) = a / (t * Real.sqrt t) := by
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsq : Real.sqrt t * Real.sqrt t = t := by simpa [pow_two] using Real.sq_sqrt (le_of_lt ht)
  rw [div_eq_div_iff (mul_ne_zero ht0 ht0) (mul_ne_zero ht0 hs)]
  calc
    a * Real.sqrt t * (t * Real.sqrt t) = a * (Real.sqrt t * (t * Real.sqrt t)) := by ring
    _ = a * (t * (Real.sqrt t * Real.sqrt t)) := by
          congr 1
          exact mul_left_comm (Real.sqrt t) t (Real.sqrt t)
    _ = a * (t * t) := by
          congr 1
          rw [hsq]

/-- `a·√t/(t·t) = a/(t·√t)` (other direction). -/
private lemma mul_sqrt_div_sq' {a t : ℝ} (ht : 0 < t) :
    a / (t * Real.sqrt t) = a * Real.sqrt t / (t * t) := (mul_sqrt_div_sq ht).symm

/-- `a·√x/x = a/√x` for `0 < x`. -/
private lemma mul_sqrt_div {a x : ℝ} (hx : 0 < x) :
    a * Real.sqrt x / x = a / Real.sqrt x := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := by simpa [pow_two] using Real.sq_sqrt (le_of_lt hx)
  rw [div_eq_div_iff hx0 hs]
  calc
    a * Real.sqrt x * Real.sqrt x = a * (Real.sqrt x * Real.sqrt x) := by ring
    _ = a * x := by rw [hsq]

/-- Under RH: `|logDiv x − log x − B₁| = O((log x)^10/√x)` for some constant `B₁`. -/
private lemma rate_logDiv_rh (h : RiemannHypothesis) :
    ∃ (B₁ : ℝ) (C : ℝ) (y₀ : ℝ), 0 < C ∧ Real.exp 400 ≤ y₀ ∧
      (∀ x : ℝ, y₀ ≤ x → |smh x - B₁| ≤ C * (Real.log x) ^ 10 / Real.sqrt x) := by
  obtain ⟨Cθ, hCθ0, xθ, hCθ⟩ := Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound h
  let Y : ℝ := max xθ (Real.exp 400)
  have hYge : Real.exp 400 ≤ Y := le_max_right xθ (Real.exp 400)
  have hxθY : xθ ≤ Y := le_max_left xθ (Real.exp 400)
  have hY2 : (2 : ℝ) ≤ Y := by
    have h1 : (2 : ℝ) < Real.exp 1 := by exact Real.exp_one_gt_two
    have h2 : Real.exp 1 ≤ Real.exp 400 := Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 400)
    have h3 : Real.exp 1 ≤ Y := le_trans h2 hYge
    exact le_trans (le_of_lt h1) h3
  have hCθnon : 0 ≤ Cθ := le_of_lt hCθ0
  have hbnd : ∀ x : ℝ, Y ≤ x → |Chebyshev.theta x - x| ≤ Cθ * Real.sqrt x * (Real.log x) ^ 10 := by
    intro x hx
    exact hCθ x (le_trans hxθY hx)
  have hInt := smE_integrableOn_Ioi_of_rate (a₀ := Y) hY2 hCθnon hbnd
  obtain ⟨K, hK0, hK⟩ := Commons.Analysis.Real.tail_integral_log10
  let B₁ : ℝ := smh Y - smE Y / Y + ∫ t in Set.Ioi Y, smE t / (t * t)
  let Cbig : ℝ := Cθ * (1 + K)
  have hCbig : 0 < Cbig := by
    dsimp [Cbig]
    positivity
  refine ⟨B₁, Cbig, Y, hCbig, hYge, ?_⟩
  intro x hxY
  have hx2 : (2 : ℝ) ≤ x := le_trans hY2 hxY
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 400) (le_trans hYge hxY)
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hex1 : Real.exp 1 ≤ x := by
    have h2 : Real.exp 1 ≤ Real.exp 400 := Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 400)
    exact le_trans h2 (le_trans hYge hxY)
  -- identity: smh x − B₁ = smE x / x − ∫_{Ioi x} smE/(t·t)
  have hI2Yx : (∫ t in (2 : ℝ)..Y, smE t / (t * t)) + (∫ t in Y..x, smE t / (t * t)) =
      ∫ t in (2 : ℝ)..x, smE t / (t * t) := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (smE_intervalIntegrable_gen (by norm_num) hY2)
      (smE_intervalIntegrable_gen hY2 hxY)
  have hIoi : (∫ t in Y..x, smE t / (t * t)) + (∫ t in Set.Ioi x, smE t / (t * t)) =
      ∫ t in Set.Ioi Y, smE t / (t * t) := by
    have h1 : IntegrableOn (fun t : ℝ => smE t / (t * t)) (Set.Ioi Y) volume := hInt Y le_rfl
    have h2 : IntegrableOn (fun t : ℝ => smE t / (t * t)) (Set.Ioi x) volume := hInt x hxY
    exact intervalIntegral.integral_interval_add_Ioi h1 h2
  have hdecomp_x := smh_decomp hx2
  have hdecomp_Y := smh_decomp hY2
  have hid : smh x - B₁ = smE x / x - ∫ t in Set.Ioi x, smE t / (t * t) := by
    dsimp [B₁]
    rw [hdecomp_x, hdecomp_Y]
    rw [← hI2Yx]
    rw [← hIoi]
    ring
  -- tail estimate: |∫_{Ioi x} smE/(t·t)| ≤ Cθ·K·(logx)^10/√x
  have hpt : ∀ t ∈ Set.Ioi x, |smE t / (t * t)| ≤ Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) := by
    intro t ht
    have htY : Y ≤ t := le_trans hxY (le_of_lt (Set.mem_Ioi.mp ht))
    have htb := hbnd t htY
    have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos 400) (le_trans hYge htY)
    rw [abs_div]
    rw [abs_of_pos (mul_pos htpos htpos)]
    change |Chebyshev.theta t - t| / (t * t) ≤ Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t)
    calc
      |Chebyshev.theta t - t| / (t * t) ≤ (Cθ * Real.sqrt t * (Real.log t) ^ 10) / (t * t) := by
        exact div_le_div_of_nonneg_right htb (mul_nonneg (le_of_lt htpos) (le_of_lt htpos))
      _ = Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) := by
        have hpos1 : 0 < t * t := mul_pos htpos htpos
        have hpos2 : 0 < t * Real.sqrt t := mul_pos htpos (Real.sqrt_pos.2 htpos)
        rw [div_eq_div_iff (ne_of_gt hpos1) (ne_of_gt hpos2)]
        have hsq : Real.sqrt t * Real.sqrt t = t := by simpa [pow_two] using Real.sq_sqrt (le_of_lt htpos)
        calc
          Cθ * Real.sqrt t * (Real.log t) ^ 10 * (t * Real.sqrt t)
              = Cθ * (Real.log t) ^ 10 * (Real.sqrt t * (t * Real.sqrt t)) := by ring
          _ = Cθ * (Real.log t) ^ 10 * (t * (Real.sqrt t * Real.sqrt t)) := by
                congr 1
                exact mul_left_comm (Real.sqrt t) t (Real.sqrt t)
          _ = Cθ * (Real.log t) ^ 10 * (t * t) := by
                congr 1
                rw [hsq]
  have htail_le : |∫ t in Set.Ioi x, smE t / (t * t)| ≤ Cθ * K * (Real.log x) ^ 10 / Real.sqrt x := by
    let μ : Measure ℝ := volume.restrict (Set.Ioi x)
    have hf_int : Integrable (fun t : ℝ => smE t / (t * t)) μ := by
      dsimp [μ]
      exact hInt x hxY
    have hg_int : Integrable (fun t : ℝ => Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t)) μ := by
      have hI : IntegrableOn (fun t : ℝ => (Real.log t) ^ 10 / (t * Real.sqrt t)) (Set.Ioi x) volume :=
        Commons.Analysis.Real.integrableOn_log10_div_sqrt (by linarith [hY2, hxY] : 2 ≤ x)
      have hc : Integrable (fun t : ℝ => Cθ * ((Real.log t) ^ 10 / (t * Real.sqrt t))) μ := by
        dsimp [μ]
        exact hI.const_mul Cθ
      refine MeasureTheory.Integrable.congr hc ?_
      exact Eventually.of_forall (fun t => by ring)
    have habs : (fun t : ℝ => |smE t / (t * t)|) ≤ᵐ[μ]
        fun t : ℝ => Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) := by
      dsimp [μ]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      exact hpt t ht
    have hnorms : (∫ t : ℝ, |smE t / (t * t)| ∂μ) ≤
        ∫ t : ℝ, Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ := by
      exact MeasureTheory.integral_mono_ae (μ := μ) hf_int.abs hg_int habs
    have hnorm := MeasureTheory.norm_integral_le_integral_norm (μ := μ) (fun t : ℝ => smE t / (t * t))
    have hm1abs : |∫ t : ℝ, smE t / (t * t) ∂μ| ≤ ∫ t : ℝ, |smE t / (t * t)| ∂μ := by
      simpa only [Real.norm_eq_abs] using hnorm
    have hb2 : (∫ t : ℝ, Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ) ≤
        Cθ * K * (Real.log x) ^ 10 / Real.sqrt x := by
      have h₁ := hK x hex1
      have hconst : (∫ t : ℝ, Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ) =
          Cθ * (∫ t : ℝ, (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ) := by
        calc
          (∫ t : ℝ, Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ)
              = (∫ t : ℝ, (Real.log t) ^ 10 / (t * Real.sqrt t) * Cθ ∂μ) := by
                  refine MeasureTheory.integral_congr_ae ?_
                  exact Eventually.of_forall (fun t => by ring)
          _ = (∫ t : ℝ, (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ) * Cθ := by
                  rw [MeasureTheory.integral_mul_const]
          _ = Cθ * (∫ t : ℝ, (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ) := by
                  rw [mul_comm]
      rw [hconst]
      calc
        Cθ * (∫ t : ℝ, (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ)
            ≤ Cθ * (K * (Real.log x) ^ 10 / Real.sqrt x) := by
              exact mul_le_mul_of_nonneg_left (by simpa [μ] using h₁) hCθnon
        _ = Cθ * K * (Real.log x) ^ 10 / Real.sqrt x := by ring
    have hset : (∫ t in Set.Ioi x, smE t / (t * t)) = ∫ t : ℝ, smE t / (t * t) ∂μ := by
      dsimp [μ]
    have hm1 : |∫ t in Set.Ioi x, smE t / (t * t)| ≤ ∫ t : ℝ, |smE t / (t * t)| ∂μ := by
      rw [hset]
      exact hm1abs
    calc
      |∫ t in Set.Ioi x, smE t / (t * t)| ≤ ∫ t : ℝ, |smE t / (t * t)| ∂μ := hm1
      _ ≤ ∫ t : ℝ, Cθ * (Real.log t) ^ 10 / (t * Real.sqrt t) ∂μ := hnorms
      _ ≤ Cθ * K * (Real.log x) ^ 10 / Real.sqrt x := hb2
  have hbnd1 : |smE x / x| ≤ Cθ * (Real.log x) ^ 10 / Real.sqrt x := by
    have hb := hbnd x hxY
    rw [abs_div]
    rw [abs_of_pos hxpos]
    change |Chebyshev.theta x - x| / x ≤ Cθ * (Real.log x) ^ 10 / Real.sqrt x
    have hx0' : x ≠ 0 := ne_of_gt hxpos
    have hsx : Real.sqrt x ≠ 0 := ne_of_gt hsqrtx
    calc
      |Chebyshev.theta x - x| / x ≤ (Cθ * Real.sqrt x * (Real.log x) ^ 10) / x := by
        exact div_le_div_of_nonneg_right hb (le_of_lt hxpos)
      _ = Cθ * (Real.log x) ^ 10 / Real.sqrt x := by
        rw [div_eq_div_iff hx0' hsx]
        have hsq : Real.sqrt x * Real.sqrt x = x := by simpa [pow_two] using Real.sq_sqrt (le_of_lt hxpos)
        calc
          Cθ * Real.sqrt x * (Real.log x) ^ 10 * Real.sqrt x
              = Cθ * (Real.log x) ^ 10 * (Real.sqrt x * Real.sqrt x) := by ring
          _ = Cθ * (Real.log x) ^ 10 * x := by rw [hsq]
  have hfinal : |smh x - B₁| ≤ Cbig * (Real.log x) ^ 10 / Real.sqrt x := by
    rw [hid]
    have htri := abs_add_le (smE x / x) (-(∫ t : ℝ in Set.Ioi x, smE t / (t * t)))
    have hsub : |smE x / x - (∫ t : ℝ in Set.Ioi x, smE t / (t * t))| ≤
        |smE x / x| + |∫ t : ℝ in Set.Ioi x, smE t / (t * t)| := by
      simpa [sub_eq_add_neg, abs_neg] using htri
    have hsum : |smE x / x| + |∫ t : ℝ in Set.Ioi x, smE t / (t * t)| ≤
        Cbig * (Real.log x) ^ 10 / Real.sqrt x := by
      have h2 : |smE x / x| ≤ Cθ * (Real.log x) ^ 10 / Real.sqrt x := hbnd1
      have h3 : |∫ t : ℝ in Set.Ioi x, smE t / (t * t)| ≤ Cθ * K * (Real.log x) ^ 10 / Real.sqrt x := htail_le
      have hadd := add_le_add h2 h3
      have hden : Real.sqrt x ≠ 0 := ne_of_gt hsqrtx
      calc
        |smE x / x| + |∫ t : ℝ in Set.Ioi x, smE t / (t * t)| ≤
            Cθ * (Real.log x) ^ 10 / Real.sqrt x +
              Cθ * K * (Real.log x) ^ 10 / Real.sqrt x := hadd
        _ = Cbig * (Real.log x) ^ 10 / Real.sqrt x := by
            dsimp [Cbig]
            field_simp [hden]
    exact le_trans hsub hsum
  exact hfinal

/-- `(log x)^n/√x → 0` as `x → ∞`, for `n ≠ 0`. -/
private lemma tendsto_log_pow_div_sqrt (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => (Real.log x) ^ n / Real.sqrt x) atTop (𝓝 0) := by
  let r : ℝ := 1 / (2 * (n : ℝ))
  have hr : 0 < r := by
    dsimp [r]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    positivity
  have h₁ : Tendsto (fun x : ℝ => Real.log x / x ^ r) atTop (𝓝 0) := by
    exact Asymptotics.IsLittleO.tendsto_div_nhds_zero (isLittleO_log_rpow_atTop hr)
  have h₂ : Tendsto (fun x : ℝ => (Real.log x / x ^ r) ^ n) atTop (𝓝 0) := by
    simpa [zero_pow hn] using h₁.pow n
  have hEq : (fun x : ℝ => (Real.log x) ^ n / Real.sqrt x) =ᶠ[atTop]
      fun x : ℝ => (Real.log x / x ^ r) ^ n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_pow]
    congr 1
    have hx0 : 0 ≤ x := le_of_lt hx
    have hb : (x ^ r) ^ (n : ℝ) = x ^ (r * (n : ℝ)) := (Real.rpow_mul hx0 r (n : ℝ)).symm
    have hb' : (x ^ r) ^ n = x ^ (r * (n : ℝ)) := by
      rw [Real.rpow_natCast (x ^ r) n] at hb
      exact hb
    rw [hb']
    rw [show r * (n : ℝ) = 1 / 2 by
      dsimp [r]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [hnR]]
    rw [← Real.sqrt_eq_rpow x]
  exact h₂.congr' hEq.symm

/-- If `|f x − M| ≤ g x` eventually and `g → 0`, then `f → M`. -/
private lemma tendsto_of_abs_sub_le {f g : ℝ → ℝ} {M : ℝ} (hg : Tendsto g atTop (𝓝 0))
    (hle : ∀ᶠ x in atTop, |f x - M| ≤ g x) : Tendsto f atTop (𝓝 M) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hgε : ∀ᶠ x in atTop, |g x| < ε := by
    have := (Metric.tendsto_nhds.mp hg) ε hε
    simpa [Real.dist_eq] using this
  filter_upwards [hle, hgε] with x hx hgx
  have hb : |f x - M| < ε := by
    calc
      |f x - M| ≤ g x := hx
      _ ≤ |g x| := le_abs_self (g x)
      _ < ε := hgx
  simpa [Real.dist_eq] using hb



/-- `logRatioSum y = primeRecips y + logRatioCorrSum y`. -/
private lemma logRatioSum_eq_add (y : ℝ) :
    logRatioSum y = primeRecips y + logRatioCorrSum y := by
  unfold logRatioSum logRatioCorrSum primeRecips
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  unfold corrTerm
  ring

/-- Under RH: rate for `smf x = ∑_{p≤x} 1/p − log log x` with limit `M`. -/
private lemma rate_primeRecips_rh (h : RiemannHypothesis) :
    ∃ (M : ℝ) (C : ℝ) (y₀ : ℝ), 0 < C ∧ Real.exp 400 ≤ y₀ ∧
      (∀ x : ℝ, y₀ ≤ x → |smf x - M| ≤ C * (Real.log x) ^ 12 / Real.sqrt x) ∧
      Tendsto smf atTop (𝓝 M) := by
  obtain ⟨B₁, C₁, y₁, hC₁pos, hy₁ge, h₁⟩ := rate_logDiv_rh h
  rcases second_mertens_converges with ⟨L, hL⟩
  have hC₁non : 0 ≤ C₁ := le_of_lt hC₁pos
  have hy₁2 : (2 : ℝ) ≤ y₁ := by
    have h1 : (2 : ℝ) < Real.exp 1 := by exact Real.exp_one_gt_two
    have h2 : Real.exp 1 ≤ Real.exp 400 := Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 400)
    exact le_trans (le_of_lt h1) (le_trans h2 hy₁ge)
  have hb : ∀ t : ℝ, y₁ ≤ t → |logDiv t - Real.log t - B₁| ≤
      C₁ * (Real.log t) ^ 10 / Real.sqrt t := by
    intro t ht
    simpa [smh] using h₁ t ht
  obtain ⟨C₂, hC₂pos, y₂, hy12, hrate⟩ := primeRecips_limit_rate hC₁non hy₁2 hb (L := L) hL
  -- hrate : ∀ x, y₂ ≤ x → |(primeRecips x − log log x) − L| ≤ C₂ (logx)^{12}/√x
  refine ⟨L, C₂, y₂, hC₂pos, ?_, ?_, ?_⟩
  · exact le_trans hy₁ge hy12
  · intro x hx
    simpa [smf] using hrate x hx
  · change Filter.Tendsto (fun x : ℝ => primeRecips x - Real.log (Real.log x)) Filter.atTop (𝓝 L)
    exact hL

/-- The Mertens correction term summed over all primes. -/
private def corrTotal : ℝ := ∑' n : ℕ, corrExt n

/-- `logRatioCorrSum y` equals the partial sum of `corrExt` up to `⌊y⌋₊`. -/
private lemma logRatioCorrSum_eq_partial (y : ℝ) :
    logRatioCorrSum y = ∑ k ∈ Finset.range (⌊y⌋₊ + 1), corrExt k := by
  have hp := partial_sum_eq_range (⌊y⌋₊)
  simpa [logRatioCorrSum] using hp

theorem mertens_log_ratio_rh_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      |Commons.NumberTheory.Mertens.logRatioSum y - Real.log (Real.log y) - Real.eulerMascheroniConstant| ≤
        C * (Real.log y) ^ 12 / Real.sqrt y := by
  obtain ⟨M0, C0, y0, hC0pos, hy0ge, hrate0, hM0⟩ := rate_primeRecips_rh h
  obtain ⟨Cc, hCcpos, hcc⟩ := corr_sum_tail_bound
  have hidγ := prime_euler_constant_identity (M := M0) hM0
  have hcteq : (∑' p : Nat.Primes, corrTerm (p : ℕ)) = corrTotal := by
    dsimp [corrTotal]
    exact tsum_corrExt_eq
  have hγ : M0 + corrTotal = Real.eulerMascheroniConstant := by
    have h' : M0 + (∑' p : Nat.Primes, corrTerm (p : ℕ)) = Real.eulerMascheroniConstant := by
      simpa [corrTerm] using hidγ
    rwa [hcteq] at h'
  let Cbig : ℝ := C0 + 2 * Cc
  have hCbig : 0 < Cbig := by positivity
  refine ⟨Cbig, hCbig, y0, ?_⟩
  intro y hy0
  have hy0e : Real.exp 1 ≤ y := le_trans (by
      have h2 : Real.exp 1 ≤ Real.exp 400 := Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 400)
      exact le_trans h2 hy0ge) hy0
  have hy2 : (2 : ℝ) ≤ y := by
    have h1 : (2 : ℝ) < Real.exp 1 := by exact Real.exp_one_gt_two
    exact le_trans (le_of_lt h1) hy0e
  have hlog1 : (1 : ℝ) ≤ Real.log y := by
    have hlg := Real.log_le_log (Real.exp_pos 1) hy0e
    rwa [Real.log_exp] at hlg
  -- main decomposition
  have hdec : logRatioSum y - Real.log (Real.log y) = smf y + logRatioCorrSum y := by
    rw [logRatioSum_eq_add y]
    unfold smf
    ring
  -- corr tail bound at y:
  have hcorr : |logRatioCorrSum y - corrTotal| ≤ 2 * Cc * (Real.log y) ^ 12 / Real.sqrt y := by
    let N : ℕ := ⌊y⌋₊
    have hN1 : (1 : ℕ) ≤ N := by
      have hN2 : (2 : ℕ) ≤ N := by
        dsimp [N]
        simpa using (Nat.floor_mono hy2 : ⌊(2 : ℝ)⌋₊ ≤ ⌊y⌋₊)
      omega
    have hNy : (y - 1 : ℝ) < (N : ℝ) := by
      have hf := Nat.lt_floor_add_one y
      dsimp [N]
      nlinarith
    have hccN := hcc N hN1
    have hpart := logRatioCorrSum_eq_partial y
    have htmp : |logRatioCorrSum y - corrTotal| ≤ Cc / (N : ℝ) := by
      calc
        |logRatioCorrSum y - corrTotal| = |corrTotal - logRatioCorrSum y| := by rw [abs_sub_comm]
        _ = |corrTotal - (∑ k ∈ Finset.range (N + 1), corrExt k)| := by rw [hpart]
        _ ≤ Cc / (N : ℝ) := by
              simpa [corrTotal] using hccN
    have hypos0 : 0 < y := lt_of_lt_of_le zero_lt_one (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hy0e)
    have hsqrtpos : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos0
    have hy1 : (1 : ℝ) ≤ y := by linarith
    have hs : Real.sqrt y ≤ y := by
      have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt (le_of_lt hypos0)
      have hsy : (1 : ℝ) ≤ Real.sqrt y := by
        have h := Real.sqrt_le_sqrt hy1
        simpa [Real.sqrt_one] using h
      nlinarith
    have hlogsq : (1 : ℝ) ≤ (Real.log y) ^ 12 := one_le_pow₀ hlog1
    have hNpos : 0 < (N : ℝ) := by
      have h1 : (0 : ℝ) < N := by
        have h2 : (y - 1 : ℝ) < (N : ℝ) := hNy
        linarith
      exact h1
    have hNhalf : (y / 2 : ℝ) ≤ (N : ℝ) := by
      have hsub : (y / 2 : ℝ) ≤ y - 1 := by nlinarith [hy2]
      exact le_trans hsub (le_of_lt hNy)
    have h₁ : (1 : ℝ) / (N : ℝ) ≤ 2 / y := by
      rw [div_le_div_iff₀ hNpos hypos0]
      nlinarith [hNhalf]
    have hcnon : 0 ≤ Cc := le_of_lt hCcpos
    have h₁c : Cc / (N : ℝ) ≤ (2 * Cc) / y := by
      calc
        Cc / (N : ℝ) = Cc * (1 / (N : ℝ)) := by ring
        _ ≤ Cc * (2 / y) := mul_le_mul_of_nonneg_left h₁ hcnon
        _ = (2 * Cc) / y := by ring
    have hxy : Real.sqrt y ≤ y * (Real.log y) ^ 12 := by
      nlinarith [hs, mul_le_mul_of_nonneg_left hlogsq (le_of_lt hypos0)]
    have h₂ : (2 * Cc) / y ≤ (2 * Cc) * (Real.log y) ^ 12 / Real.sqrt y := by
      have hpos : 0 < 2 * Cc := by positivity
      rw [div_le_div_iff₀ hypos0 hsqrtpos]
      calc
        (2 * Cc) * Real.sqrt y ≤ (2 * Cc) * (y * (Real.log y) ^ 12) :=
              mul_le_mul_of_nonneg_left hxy (le_of_lt hpos)
        _ = (2 * Cc) * (Real.log y) ^ 12 * y := by ring
    have hfin : Cc / (N : ℝ) ≤ 2 * Cc * (Real.log y) ^ 12 / Real.sqrt y := by
      exact le_trans h₁c (by simpa [mul_assoc] using h₂)
    exact le_trans htmp hfin

  have hmain : logRatioSum y - Real.log (Real.log y) - Real.eulerMascheroniConstant =
      (smf y - M0) + (logRatioCorrSum y - corrTotal) := by
    rw [hdec]
    linarith [hγ]
  calc
    |logRatioSum y - Real.log (Real.log y) - Real.eulerMascheroniConstant| ≤
        Cbig * (Real.log y) ^ 12 / Real.sqrt y := by
      rw [hmain]
      have htri := abs_add_le (smf y - M0) (logRatioCorrSum y - corrTotal)
      have hsqrt : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le (Real.exp_pos 1) hy0e))
      calc
        |(smf y - M0) + (logRatioCorrSum y - corrTotal)| ≤
            |smf y - M0| + |logRatioCorrSum y - corrTotal| := htri
        _ ≤ C0 * (Real.log y) ^ 12 / Real.sqrt y + 2 * Cc * (Real.log y) ^ 12 / Real.sqrt y :=
              add_le_add (hrate0 y hy0) hcorr
        _ = Cbig * (Real.log y) ^ 12 / Real.sqrt y := by
              dsimp [Cbig]
              field_simp [hsqrt]
