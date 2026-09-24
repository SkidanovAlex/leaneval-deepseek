import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.NumberTheory.Mertens.mertens_lower

open Finset MeasureTheory Real
open scoped Chebyshev

namespace Commons.NumberTheory.Mertens

noncomputable section

/-! ## Derivative of the integration kernel `-(t log t)⁻¹` -/

private lemma hasDerivAt_mul_log {t : ℝ} (ht0 : t ≠ 0) :
    HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
  have h := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
  simp only [id_eq, one_mul] at h
  rw [mul_inv_cancel₀ ht0] at h
  exact h

private lemma hasDerivAt_neg_inv_mul_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => -((s * Real.log s)⁻¹))
      ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t :=
    hasDerivAt_mul_log ht0
  have hne : t * Real.log t ≠ 0 := mul_ne_zero ht0 hlog
  have h2 : HasDerivAt (fun s : ℝ => (s * Real.log s)⁻¹)
      (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := h1.inv hne
  have h3 : HasDerivAt (fun s : ℝ => -((s * Real.log s)⁻¹))
      (-(-(Real.log t + 1) / (t * Real.log t) ^ 2)) t := h2.neg
  refine h3.congr_deriv ?_
  field_simp

private lemma deriv_neg_inv_mul_log {t : ℝ} (ht : 1 < t) :
    deriv (fun s : ℝ => -((s * Real.log s)⁻¹)) t =
      (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) :=
  (hasDerivAt_neg_inv_mul_log ht).deriv

/-- Continuity of the kernel `(log t + 1)/(t² (log t)²)` on `[x, X]` for `x ≥ 2`. -/
private lemma continuousOn_phi {x X : ℝ} (hx : 2 ≤ x) :
    ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) (Set.Icc x X) := by
  have hlog : ContinuousOn Real.log (Set.Icc x X) :=
    Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx, ht.1])
  have hnum : ContinuousOn (fun t : ℝ => Real.log t + 1) (Set.Icc x X) :=
    hlog.add continuousOn_const
  have hden : ContinuousOn (fun t : ℝ => t ^ 2 * (Real.log t) ^ 2) (Set.Icc x X) :=
    (continuousOn_id.pow 2).mul (hlog.pow 2)
  refine ContinuousOn.div hnum hden ?_
  intro t ht
  have ht2 : (2:ℝ) ≤ t := le_trans hx ht.1
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  positivity

/-! ## Rewriting `primeRecips` and the Abel-summation kernel sum -/

private lemma primeRecips_eq_sum_ite (X : ℝ) :
    primeRecips X = ∑ k ∈ Icc 0 ⌊X⌋₊, (if k.Prime then (1 : ℝ)/k else 0) := by
  unfold primeRecips
  rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]

private lemma sum_Ioc_ite_prime_eq {x X : ℝ} (_hx : 2 ≤ x) (hxX : x ≤ X) :
    (∑ k ∈ Ioc ⌊x⌋₊ ⌊X⌋₊, (if k.Prime then (1 : ℝ)/k else 0))
      = primeRecips X - primeRecips x := by
  rw [primeRecips_eq_sum_ite X, primeRecips_eq_sum_ite x]
  have hfloor : ⌊x⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hxX
  have hsplit : Icc 0 ⌊X⌋₊ = Icc 0 ⌊x⌋₊ ∪ Ioc ⌊x⌋₊ ⌊X⌋₊ := by
    ext k; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 0 ⌊x⌋₊) (Ioc ⌊x⌋₊ ⌊X⌋₊) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [mem_Icc] at hk1
    simp only [mem_Ioc] at hk2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

private lemma sum_abel_lhs_eq {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    (∑ k ∈ Ioc ⌊x⌋₊ ⌊X⌋₊,
       (-(((k:ℝ) * Real.log (k:ℝ))⁻¹)) *
         Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => Real.log n) k)
      = -(primeRecips X - primeRecips x) := by
  have h := sum_Ioc_ite_prime_eq (x := x) (X := X) hx hxX
  have hpt : ∀ k ∈ Ioc ⌊x⌋₊ ⌊X⌋₊,
      (-(((k:ℝ) * Real.log (k:ℝ))⁻¹)) *
          Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => Real.log n) k
        = -(if k.Prime then (1:ℝ)/k else 0) := by
    intro k _hk
    by_cases hkp : k.Prime
    · have hk1 : (1:ℝ) < (k:ℝ) := by exact_mod_cast hkp.one_lt
      have hk0 : (k:ℝ) ≠ 0 := by positivity
      have hlogk : Real.log (k:ℝ) ≠ 0 := ne_of_gt (Real.log_pos hk1)
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hkp, if_true]
      field_simp
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hkp, if_false, mul_zero, neg_zero]
  rw [Finset.sum_congr rfl hpt, Finset.sum_neg_distrib]
  rw [h]

/-! ## Evaluation of the `∫ t·φ(t)` piece -/

private lemma t_phi_integral_eq {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    ∫ t in x..X, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = (Real.log (Real.log X) - Real.log (Real.log x))
        + (1 / Real.log x - 1 / Real.log X) := by
  have hx1 : (1:ℝ) < x := by linarith
  have hX1 : (1:ℝ) < X := by linarith
  have hcongr : ∫ t in x..X, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = ∫ t in x..X, (t⁻¹ / Real.log t + t⁻¹ / (Real.log t) ^ 2) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hxX ?_
    intro t ht
    have ht2 : (2:ℝ) ≤ t := le_trans hx (le_of_lt (Set.mem_Ioo.mp ht).1)
    have ht0 : t ≠ 0 := by linarith
    have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    field_simp
  rw [hcongr]
  have hlog : ContinuousOn Real.log (Set.Icc x X) :=
    Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx, ht.1])
  have hcont1 : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.Icc x X) :=
    ContinuousOn.div₀ (continuousOn_id.inv₀ (fun t ht => by
      simp only [id_eq]; linarith [hx, ht.1])) hlog
      (fun t ht => ne_of_gt (Real.log_pos (by linarith [hx, ht.1])))
  have hcont2 : ContinuousOn (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) (Set.Icc x X) :=
    ContinuousOn.div₀ (continuousOn_id.inv₀ (fun t ht => by
      simp only [id_eq]; linarith [hx, ht.1])) (hlog.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [hx, ht.1]))))
  have hInt1 : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume x X :=
    ContinuousOn.intervalIntegrable_of_Icc hxX hcont1
  have hInt2 : IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume x X :=
    ContinuousOn.intervalIntegrable_of_Icc hxX hcont2
  rw [intervalIntegral.integral_add hInt1 hInt2, integral_inv_div_log hx1 hX1,
    integral_inv_div_log_sq hx1 hX1]
  simp only [one_div]

/-! ## Evaluation of the `∫ θ(t)·φ(t)` piece via Abel summation -/

private lemma theta_phi_integral_eq {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    ∫ t in x..X, Chebyshev.theta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = -(Chebyshev.theta X) / (X * Real.log X)
        + (Chebyshev.theta x) / (x * Real.log x)
        + (primeRecips X - primeRecips x) := by
  let c : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => Real.log n)
  let f : ℝ → ℝ := fun s : ℝ => -((s * Real.log s)⁻¹)
  have hx0 : 0 ≤ x := by linarith
  have hf_diff : ∀ t ∈ Set.Icc x X, DifferentiableAt ℝ f t := fun t ht =>
    (hasDerivAt_neg_inv_mul_log (by linarith [hx, ht.1] : (1:ℝ) < t)).differentiableAt
  have hderiv_eq : ∀ t ∈ Set.Icc x X,
      deriv f t = (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) :=
    fun t ht => deriv_neg_inv_mul_log (by linarith [hx, ht.1] : (1:ℝ) < t)
  have hφcont : ContinuousOn
      (fun t : ℝ => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) (Set.Icc x X) :=
    continuousOn_phi hx
  have hf_int : IntegrableOn (deriv f) (Set.Icc x X) volume :=
    hφcont.integrableOn_Icc.congr_fun (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c hx0 hxX hf_diff hf_int
  have hcum : ∀ u : ℝ, (∑ k ∈ Icc 0 ⌊u⌋₊, c k) = Chebyshev.theta u := by
    intro u; simp only [c]; exact theta_eq_sum_cumulative u
  have hLHS : (∑ k ∈ Ioc ⌊x⌋₊ ⌊X⌋₊, f ↑k * c k) = -(primeRecips X - primeRecips x) := by
    simp only [f, c]
    exact sum_abel_lhs_eq hx hxX
  have hI : ∫ t in Set.Ioc x X, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)
      = -(Chebyshev.theta X) / (X * Real.log X)
        + (Chebyshev.theta x) / (x * Real.log x)
        + (primeRecips X - primeRecips x) := by
    have h1 : f X * (∑ k ∈ Icc 0 ⌊X⌋₊, c k) = -(Chebyshev.theta X)/(X*Real.log X) := by
      rw [hcum X]; simp only [f]; rw [inv_eq_one_div]; ring
    have h2 : f x * (∑ k ∈ Icc 0 ⌊x⌋₊, c k) = -(Chebyshev.theta x)/(x*Real.log x) := by
      rw [hcum x]; simp only [f]; rw [inv_eq_one_div]; ring
    rw [hLHS, h1, h2] at habel
    linear_combination habel
  have hconv : ∫ t in x..X, Chebyshev.theta t * ((Real.log t + 1)/(t^2*(Real.log t)^2))
      = ∫ t in Set.Ioc x X, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
    rw [intervalIntegral.integral_of_le hxX]
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro t ht
    change Chebyshev.theta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)
    rw [hderiv_eq t (Set.Ioc_subset_Icc_self ht), hcum t]
    ring
  rw [hconv, hI]

/-! ## Interval-integrability of the two pieces -/

private lemma intervalIntegrable_theta_phi {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      volume x X := by
  have h1 : IntegrableOn
      (fun t : ℝ => ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) *
        (∑ k ∈ Icc 0 ⌊t⌋₊,
          Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => Real.log n) k)) (Set.Icc x X) volume :=
    integrableOn_mul_sum_Icc
      (c := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => Real.log n)) (m := 0)
      (a := x) (b := X) (by linarith)
      (g := fun t : ℝ => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      (continuousOn_phi hx).integrableOn_Icc
  have h2 : IntegrableOn
      (fun t : ℝ => Chebyshev.theta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Icc x X) volume :=
    h1.congr_fun (fun t _ht => by
      show ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) *
          (∑ k ∈ Icc 0 ⌊t⌋₊, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => Real.log n) k)
        = Chebyshev.theta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      rw [theta_eq_sum_cumulative t]; ring) measurableSet_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxX).mpr h2

private lemma intervalIntegrable_id_phi {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    IntervalIntegrable
      (fun t : ℝ => t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      volume x X :=
  ContinuousOn.intervalIntegrable_of_Icc hxX
    (continuousOn_id.mul (continuousOn_phi hx))

/-! ## Main theorem -/

theorem theta_sub_id_phi_integral_finite {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    ∫ t in x..X, (Chebyshev.theta t - t) *
        ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = -(Chebyshev.theta X - X) / (X * Real.log X)
        + (Chebyshev.theta x - x) / (x * Real.log x)
        + (Commons.NumberTheory.Mertens.primeRecips X - Commons.NumberTheory.Mertens.primeRecips x)
        - (Real.log (Real.log X) - Real.log (Real.log x)) := by
  have hIntθ := intervalIntegrable_theta_phi hx hxX
  have hIntt := intervalIntegrable_id_phi hx hxX
  have hcongr : ∫ t in x..X, (Chebyshev.theta t - t) *
        ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = ∫ t in x..X, (Chebyshev.theta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
          - t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) := by
    refine intervalIntegral.integral_congr fun t _ht => ?_
    ring
  rw [hcongr, intervalIntegral.integral_sub hIntθ hIntt,
    theta_phi_integral_eq hx hxX, t_phi_integral_eq hx hxX]
  have hx1 : (1:ℝ) < x := by linarith
  have hX1 : (1:ℝ) < X := by linarith
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hlogX : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX1)
  have hx0 : x ≠ 0 := by linarith
  have hX0 : X ≠ 0 := by linarith
  field_simp
  ring

end

end Commons.NumberTheory.Mertens