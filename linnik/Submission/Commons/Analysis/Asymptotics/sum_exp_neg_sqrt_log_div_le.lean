import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SumIntegralComparisons

namespace Commons.Analysis.Asymptotics

open Real MeasureTheory Set
open scoped Interval

noncomputable section

/-- Antiderivative of `u ↦ exp (-(c * sqrt u))` on `u > 0`. -/
private def antideriv (c t : ℝ) : ℝ :=
  -2 * (Real.sqrt t / c + 1 / c ^ 2) * Real.exp (-(c * Real.sqrt t))

private lemma hasDerivAt_antideriv (c : ℝ) (hc : c ≠ 0) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (antideriv c) (Real.exp (-(c * Real.sqrt u))) u := by
  unfold antideriv
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt u)) u :=
    Real.hasDerivAt_sqrt (ne_of_gt hu)
  have hsc : HasDerivAt (fun t : ℝ => Real.sqrt t / c + 1 / c ^ 2)
      ((1 / (2 * Real.sqrt u)) / c) u :=
    (hs.div_const c).add_const (1 / c ^ 2)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(c * Real.sqrt t)))
      (Real.exp (-(c * Real.sqrt u)) * (-(c * (1 / (2 * Real.sqrt u))))) u :=
    ((hs.const_mul c).neg).exp
  have hprod := hsc.mul hexp
  have hs0 : Real.sqrt u ≠ 0 := by positivity
  have hfinal : HasDerivAt (fun t : ℝ => -2 * ((Real.sqrt t / c + 1 / c ^ 2)
      * Real.exp (-(c * Real.sqrt t)))) (Real.exp (-(c * Real.sqrt u))) u :=
    (hprod.const_mul (-2)).congr_deriv (by field_simp; ring)
  simpa only [← mul_assoc] using hfinal

/-- `∫_0^L exp (-(c * sqrt u)) du ≤ 2 / c^2` for `c > 0`, `L ≥ 0`. -/
private lemma integral_exp_neg_sqrt_le (c : ℝ) (hc : 0 < c) {L : ℝ} (hL : 0 ≤ L) :
    (∫ u in (0:ℝ)..L, Real.exp (-(c * Real.sqrt u))) ≤ 2 / c ^ 2 := by
  have hcont : ContinuousOn (antideriv c) (Set.Icc 0 L) := by
    unfold antideriv
    have h1 : Continuous (fun t : ℝ => Real.sqrt t / c + 1 / c ^ 2) :=
      (Real.continuous_sqrt.div_const c).add continuous_const
    have h2 : Continuous (fun t : ℝ => Real.exp (-(c * Real.sqrt t))) :=
      Real.continuous_exp.comp ((continuous_const.mul Real.continuous_sqrt).neg)
    exact ((h1.const_mul (-2)).mul h2).continuousOn
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-(c * Real.sqrt u))) volume 0 L := by
    have h2 : Continuous (fun u : ℝ => Real.exp (-(c * Real.sqrt u))) :=
      Real.continuous_exp.comp ((continuous_const.mul Real.continuous_sqrt).neg)
    exact h2.intervalIntegrable 0 L
  have hderiv : ∀ u ∈ Set.Ioo (0:ℝ) L,
      HasDerivAt (antideriv c) (Real.exp (-(c * Real.sqrt u))) u :=
    fun u hu => hasDerivAt_antideriv c (ne_of_gt hc) hu.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL hcont hderiv hint
  rw [hftc]
  have hG0 : antideriv c 0 = -2 / c ^ 2 := by
    unfold antideriv
    simp [Real.sqrt_zero, Real.exp_zero]
    ring
  have hGL : antideriv c L ≤ 0 := by
    unfold antideriv
    have h1 : 0 ≤ Real.sqrt L / c + 1 / c ^ 2 := by positivity
    have h2 : 0 ≤ Real.exp (-(c * Real.sqrt L)) := (Real.exp_pos _).le
    nlinarith [mul_nonneg h1 h2]
  have hfin : antideriv c L - antideriv c 0 = antideriv c L + 2 / c ^ 2 := by
    rw [hG0]; ring
  rw [hfin]
  linarith

/-- Substitution `x ↦ log x`. -/
private lemma integral_log_subst (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1:ℝ)..(N:ℝ), Real.exp (-(c * Real.sqrt (Real.log x))) / x)
      = ∫ u in (0:ℝ)..Real.log (N:ℝ), Real.exp (-(c * Real.sqrt u)) := by
  have hN' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := (1:ℝ)) (b := (N:ℝ))
    (f := Real.log) (f' := fun x : ℝ => x⁻¹)
    (g := fun u : ℝ => Real.exp (-(c * Real.sqrt u)))
    (by
      intro x hx
      rw [Set.uIcc_of_le hN'] at hx
      exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)))
    (continuousOn_inv₀.mono (by
      intro x hx
      rw [Set.uIcc_of_le hN'] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)))
    (Real.continuous_exp.comp ((continuous_const.mul Real.continuous_sqrt).neg))
  simpa [Function.comp, div_eq_mul_inv, Real.log_one] using hsub

/-- The function is antitone on `[1, N]`. -/
private lemma antitoneOn_exp_neg_sqrt_log_div (c : ℝ) (hc : 0 < c) {N : ℕ} :
    AntitoneOn (fun x : ℝ => Real.exp (-(c * Real.sqrt (Real.log x))) / x)
      (Set.Icc ((1:ℕ):ℝ) (N:ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  have hx1 : (1:ℝ) ≤ x := by simpa using hx.1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hsqrt : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y) := Real.sqrt_le_sqrt hlogxy
  have hmul : c * Real.sqrt (Real.log x) ≤ c * Real.sqrt (Real.log y) :=
    mul_le_mul_of_nonneg_left hsqrt hc.le
  have hexp : Real.exp (-(c * Real.sqrt (Real.log y)))
      ≤ Real.exp (-(c * Real.sqrt (Real.log x))) := Real.exp_le_exp.mpr (by linarith)
  exact div_le_div₀ (Real.exp_pos _).le hexp hx0 hxy

theorem sum_exp_neg_sqrt_log_div_le (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ)) ≤ K := by
  refine ⟨1 + 2 / c ^ 2, by positivity, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [hN]
    have h0 : (∑ n ∈ (Finset.Icc 1 0 : Finset ℕ),
        Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ)) = 0 := by simp
    rw [h0]
    positivity
  have hN1 : 1 ≤ N := hN
  have hanti := antitoneOn_exp_neg_sqrt_log_div c hc (N := N)
  have hsplit : (∑ n ∈ Finset.Icc 1 N,
        Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ))
      = Real.exp (-(c * Real.sqrt (Real.log ((1 : ℕ) : ℝ)))) / (((1 : ℕ) : ℝ))
        + ∑ i ∈ Finset.Ico 1 N,
            Real.exp (-(c * Real.sqrt (Real.log ((i + 1 : ℕ) : ℝ)))) / ((i + 1 : ℕ) : ℝ) := by
    rw [← Finset.insert_Icc_succ_left_eq_Icc hN1,
      Finset.sum_insert (by simp [Finset.mem_Icc])]
    simp only [Order.succ_eq_add_one, Nat.reduceAdd]
    congr 1
    rw [← Finset.Ico_succ_right_eq_Icc (2:ℕ) N]
    simp only [Order.succ_eq_add_one]
    rw [← Finset.sum_Ico_add (fun n : ℕ =>
      Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ)) 1 N 1]
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
  rw [hsplit]
  have hf1 : Real.exp (-(c * Real.sqrt (Real.log ((1 : ℕ) : ℝ)))) / (((1 : ℕ) : ℝ)) = 1 := by
    simp [Real.log_one, Real.sqrt_zero, Real.exp_zero]
  rw [hf1]
  have hint_le : (∑ i ∈ Finset.Ico 1 N,
        Real.exp (-(c * Real.sqrt (Real.log ((i + 1 : ℕ) : ℝ)))) / ((i + 1 : ℕ) : ℝ))
      ≤ ∫ x in (1:ℝ)..(N:ℝ), Real.exp (-(c * Real.sqrt (Real.log x))) / x := by
    simpa using AntitoneOn.sum_le_integral_Ico (a := 1) (b := N) hN1 hanti
  have hinteg : (∫ x in (1:ℝ)..(N:ℝ),
        Real.exp (-(c * Real.sqrt (Real.log x))) / x) ≤ 2 / c ^ 2 := by
    rw [integral_log_subst c hN1]
    exact integral_exp_neg_sqrt_le c hc (Real.log_nonneg (by exact_mod_cast hN1))
  linarith

end

end Commons.Analysis.Asymptotics