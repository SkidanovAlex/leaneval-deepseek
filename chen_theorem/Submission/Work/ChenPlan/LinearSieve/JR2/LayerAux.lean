import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_integral_form
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_antitone
import Submission.Work.NumberTheory.Chen.APSwitchUpper.errH_transport
import Submission.Work.NumberTheory.Chen.APSwitchUpper.errH_transport_clamped
import Submission.Work.ChenPlan.LinearSieve.JR2.errH_sharp_bounds

open Finset MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.JR2

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper

/-! ## Generic interval-integral helpers -/

lemma errH_le_exp_neg_two (s : ℝ) : errH s ≤ Real.exp (-2) := by
  rcases le_or_gt s 2 with h | h
  · rw [errH_of_le_two h]
  · by_cases h3 : s ≤ 3
    · rw [errH_of_between h h3]
      exact Real.exp_le_exp.mpr (by linarith)
    · have h3' : 3 < s := not_le.mp h3
      rw [errH_of_three_lt h3', div_le_iff₀ (by linarith : (0:ℝ) < s)]
      have he : Real.exp (-2) = Real.exp (-s) * Real.exp (s - 2) := by
        rw [← Real.exp_add]; ring_nf
      have hgoal : (3:ℝ) ≤ Real.exp (s - 2) * s := by
        have h1 : Real.exp 1 ≤ Real.exp (s - 2) := Real.exp_le_exp.mpr (by linarith)
        have h2 : (3:ℝ) ≤ Real.exp 1 * s := by
          have he1 : (1:ℝ) ≤ Real.exp 1 := (Real.one_le_exp_iff).mpr (by norm_num)
          nlinarith
        calc (3:ℝ) ≤ Real.exp 1 * s := h2
          _ ≤ Real.exp (s - 2) * s := mul_le_mul_of_nonneg_right h1 (by linarith)
      calc 3 * Real.exp (-s) = Real.exp (-s) * 3 := by ring
        _ ≤ Real.exp (-s) * (Real.exp (s - 2) * s) :=
            mul_le_mul_of_nonneg_left hgoal (Real.exp_pos _).le
        _ = Real.exp (-2) * s := by rw [he]; ring

/-- Extending the upper end of an interval integral of a nonnegative function that vanishes at
and beyond `U`. -/
lemma intervalIntegral_le_of_support {f : ℝ → ℝ} (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    {s T U : ℝ} (hsT : s ≤ T) (hnn : ∀ x, 0 ≤ f x) (hzero : ∀ x, U ≤ x → f x = 0) :
    (∫ x in s..T, f x) ≤ ∫ x in s..U, f x := by
  have hzero_interval : ∀ a b : ℝ, U ≤ a → a ≤ b → (∫ x in a..b, f x) = 0 := by
    intro a b hUa hab
    rw [intervalIntegral.integral_congr (fun x hx => ?_), intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le hab] at hx
    exact hzero x (le_trans hUa hx.1)
  rcases le_or_gt s U with hsU | hUs
  · rcases le_or_gt T U with hTU | hUT
    · exact intervalIntegral.integral_mono_interval le_rfl hsT hTU
        (Filter.Eventually.of_forall hnn) (hint s U)
    · have hsum := intervalIntegral.integral_add_adjacent_intervals (hint s U) (hint U T)
      have hz : (∫ x in U..T, f x) = 0 := hzero_interval U T le_rfl (le_of_lt hUT)
      linarith
  · have h1 : (∫ x in s..T, f x) = 0 := hzero_interval s T (le_of_lt hUs) hsT
    have h2 : (∫ x in s..U, f x) = 0 := by
      have hz : (∫ x in U..s, f x) = 0 := hzero_interval U s le_rfl (le_of_lt hUs)
      rw [intervalIntegral.integral_symm, hz, neg_zero]
    linarith

/-- The shifted delay profile is interval integrable. -/
lemma intervalIntegrable_shifted_profC (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => profC j (t - 1)) volume a b := by
  obtain ⟨C, hC0, hC⟩ := profC_bound j
  have hm : Measurable (fun t : ℝ => profC j (t - 1)) := (profC_measurable j).comp (by fun_prop)
  exact ⟨IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable C
          (Filter.Eventually.of_forall (fun x => hC (x - 1))),
         IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable C
          (Filter.Eventually.of_forall (fun x => hC (x - 1)))⟩

/-- The shifted error profile is interval integrable. -/
lemma intervalIntegrable_shifted_errH (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => errH (t - 1)) volume a b := by
  have hm : Measurable (fun t : ℝ => errH (t - 1)) := measurable_errH.comp (by fun_prop)
  have hbound : ∀ x : ℝ, ‖errH (x - 1)‖ ≤ Real.exp (-2) := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (errH_nonneg _)]; exact errH_le_exp_neg_two _
  exact ⟨IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable _
          (Filter.Eventually.of_forall hbound),
         IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable _
          (Filter.Eventually.of_forall hbound)⟩

/-- The unclamped recursion in the `t`-variable: for `j` even and `2 ≤ s`,
`∫_s^{j+4} profC j (t-1) = s·profC (j+1) s`. -/
lemma profile_eq_shifted_odd (j : ℕ) (hj : j % 2 = 0) {s : ℝ} (hs : 2 ≤ s) :
    (∫ t in s..((j:ℝ) + 4), profC j (t - 1)) = s * profC (j + 1) s := by
  have hs0 : (0:ℝ) < s := by linarith
  have hrec := profC_eq_integral_odd j hj s hs
  rw [hrec, mul_comm, div_mul_cancel₀ _ (ne_of_gt hs0)]
  have h := intervalIntegral.integral_comp_sub_right (fun u : ℝ => profC j u) 1
    (a := s) (b := (j:ℝ) + 4)
  rw [show ((j:ℝ) + 4) - 1 = (j:ℝ) + 3 by ring] at h
  exact h

/-- The clamped recursion in the `t`-variable: for `j` odd and `1 ≤ s ≤ 3`,
`∫_3^{j+4} profC j (t-1) = s·profC (j+1) s`. -/
lemma profile_eq_shifted_even (j : ℕ) (hj : j % 2 = 1) {s : ℝ} (hs : 1 ≤ s) (hs3 : s ≤ 3) :
    (∫ t in (3:ℝ)..((j:ℝ) + 4), profC j (t - 1)) = s * profC (j + 1) s := by
  have hs0 : (0:ℝ) < s := by linarith
  have hrec := profC_eq_integral_even j hj s hs
  rw [hrec, max_eq_right (by linarith : s - 1 ≤ (2:ℝ)), mul_comm, div_mul_cancel₀ _ (ne_of_gt hs0)]
  have h := intervalIntegral.integral_comp_sub_right (fun u : ℝ => profC j u) 1
    (a := (3:ℝ)) (b := (j:ℝ) + 4)
  rw [show ((j:ℝ) + 4) - 1 = (j:ℝ) + 3 by ring] at h
  rw [show (3:ℝ) - 1 = 2 by norm_num] at h
  exact h

/-- The profile integral bound, unclamped case. -/
lemma profile_integral_le_odd (j : ℕ) (hj : j % 2 = 0) {s T : ℝ} (hs : 2 ≤ s) (hsT : s ≤ T) :
    (∫ t in s..T, profC j (t - 1)) ≤ s * profC (j + 1) s := by
  rw [← profile_eq_shifted_odd j hj hs]
  exact intervalIntegral_le_of_support (f := fun x : ℝ => profC j (x - 1))
    (fun a b => intervalIntegrable_shifted_profC j a b) hsT
    (fun x => profC_nonneg j _) (fun x hx => profC_support j _ (by linarith))

/-- The profile integral bound, clamped case (`1 ≤ s ≤ 3`, integral from `3`). -/
lemma profile_integral_le_even (j : ℕ) (hj : j % 2 = 1) {s T : ℝ} (hs : 1 ≤ s) (hs3 : s ≤ 3)
    (hT : 3 ≤ T) :
    (∫ t in (3:ℝ)..T, profC j (t - 1)) ≤ s * profC (j + 1) s := by
  rw [← profile_eq_shifted_even j hj hs hs3]
  exact intervalIntegral_le_of_support (f := fun x : ℝ => profC j (x - 1))
    (fun a b => intervalIntegrable_shifted_profC j a b) hT
    (fun x => profC_nonneg j _) (fun x hx => profC_support j _ (by linarith))

/-- The tail extension of the `errH` interval integral. -/
lemma errH_interval_le_tail {s T : ℝ} (hs : 2 ≤ s) (hsT : s ≤ T) :
    (∫ t in s..T, errH (t - 1)) ≤ ∫ t in Set.Ioi s, errH (t - 1) := by
  have hInt : IntegrableOn errH (Set.Ioi (s - 1)) := integrableOn_errH_Ioi (by linarith)
  have hsub := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := s - 1) (b := T - 1) hInt
    (by linarith)
  have h1 : (∫ t in Set.Ioi s, errH (t - 1)) = ∫ u in Set.Ioi (s - 1), errH u :=
    setIntegral_Ioi_comp_sub errH s 1
  have h2 : (∫ t in s..T, errH (t - 1)) = ∫ u in s - 1..T - 1, errH u :=
    intervalIntegral.integral_comp_sub_right (fun u : ℝ => errH u) 1 (a := s) (b := T)
  have hnn : 0 ≤ ∫ u in Set.Ioi (T - 1), errH u :=
    setIntegral_nonneg_of_ae (Filter.Eventually.of_forall errH_nonneg)
  rw [h1, h2]
  linarith

/-- The clamped tail extension of the `errH` interval integral. -/
lemma errH_interval_le_Ioi_two {T : ℝ} (hT : 3 ≤ T) :
    (∫ t in (3:ℝ)..T, errH (t - 1)) ≤ ∫ u in Set.Ioi (2:ℝ), errH u := by
  have hInt : IntegrableOn errH (Set.Ioi (2:ℝ)) := integrableOn_errH_Ioi (by norm_num)
  have hsub := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := (2:ℝ)) (b := T - 1) hInt
    (by linarith)
  have h2 : (∫ t in (3:ℝ)..T, errH (t - 1)) = ∫ u in (2:ℝ)..T - 1, errH u := by
    have h := intervalIntegral.integral_comp_sub_right (fun u : ℝ => errH u) 1 (a := (3:ℝ)) (b := T)
    rw [show (3:ℝ) - 1 = 2 by norm_num] at h
    exact h
  have hnn : 0 ≤ ∫ u in Set.Ioi (T - 1), errH u :=
    setIntegral_nonneg_of_ae (Filter.Eventually.of_forall errH_nonneg)
  rw [h2]
  linarith


/-- The allowance coefficient of row `k`: `ε·1000·(k+1)·(99/100)^{k-1}`. -/
noncomputable def cCoef (k : ℕ) (ε : ℝ) : ℝ :=
  ε * 1000 * ((k : ℝ) + 1) * (99/100 : ℝ) ^ (k - 1)

lemma cCoef_nonneg {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ cCoef k ε := by
  unfold cCoef; positivity

lemma cCoef_succ (k : ℕ) (ε : ℝ) :
    cCoef (k + 1) ε = ε * 1000 * ((k : ℝ) + 2) * (99/100 : ℝ) ^ k := by
  unfold cCoef
  rw [show k + 1 - 1 = k from by omega]
  push_cast
  ring

/-- The majorant profile of the induction step from row `k` to row `k+1`: the child's normalised
profile evaluated through the parameter `u ↦ log D / log u - 1`. -/
noncomputable def PhiC (k : ℕ) (D ε : ℝ) : ℝ → ℝ := fun u =>
  profC (k - 1) (Real.log D / Real.log u - 1)
    + cCoef k ε * errH (Real.log D / Real.log u - 1)

lemma PhiC_nonneg {k : ℕ} {D ε : ℝ} (hε : 0 ≤ ε) (u : ℝ) : 0 ≤ PhiC k D ε u := by
  unfold PhiC
  exact add_nonneg (profC_nonneg _ _) (mul_nonneg (cCoef_nonneg hε) (errH_nonneg _))

/-- The parameter `u ↦ log D / log u - 1` is antitone on `(1,∞)` (for `D > 1`). -/
lemma sigma_antitone {D a b : ℝ} (hD : 1 < D) (ha : 1 < a) (hab : a ≤ b) :
    Real.log D / Real.log b - 1 ≤ Real.log D / Real.log a - 1 := by
  have hDa : 0 < Real.log D := Real.log_pos hD
  have halog : 0 < Real.log a := Real.log_pos ha
  have h1 : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have h2 : Real.log D / Real.log b ≤ Real.log D / Real.log a :=
    div_le_div_of_nonneg_left hDa.le halog h1
  linarith

/-- Monotonicity of `PhiC` in the odd-row case (`k` odd, so `profC (k-1)` is unclamped). -/
lemma PhiC_mono {k : ℕ} {D ε : ℝ} (hε : 0 ≤ ε) (hD : 1 < D) (hk : k % 2 = 1) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hσ : 1 ≤ Real.log D / Real.log b - 1) :
    PhiC k D ε a ≤ PhiC k D ε b := by
  have hσba := sigma_antitone hD ha hab
  have hc : 0 ≤ cCoef k ε := cCoef_nonneg hε
  unfold PhiC
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hc)
  · exact profC_antitone_aux (k - 1) (s := Real.log D / Real.log b - 1)
      (t := Real.log D / Real.log a - 1) hσ (Or.inl (by omega)) hσba
  · exact (errH_sharp_bounds.1) _ _ hσba

/-- Monotonicity of `PhiC` in the even-row case (`k` even, so `profC (k-1)` is clamped at `2`). -/
lemma PhiC_mono' {k : ℕ} {D ε : ℝ} (hε : 0 ≤ ε) (hD : 1 < D) (hk : k % 2 = 0) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hσ : 2 ≤ Real.log D / Real.log b - 1) :
    PhiC k D ε a ≤ PhiC k D ε b := by
  have hσba := sigma_antitone hD ha hab
  have hc : 0 ≤ cCoef k ε := cCoef_nonneg hε
  unfold PhiC
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hc)
  · exact profC_antitone_aux (k - 1) (s := Real.log D / Real.log b - 1)
      (t := Real.log D / Real.log a - 1) (by linarith) (Or.inr hσ) hσba
  · exact (errH_sharp_bounds.1) _ _ hσba

/-- The substitution value: `PhiC k D ε (D^{1/t}) = profC (k-1) (t-1) + cCoef k ε · errH (t-1)`. -/
lemma PhiC_rpow {k : ℕ} {D ε : ℝ} (hD : 1 < D) {t : ℝ} (ht : t ≠ 0) :
    PhiC k D ε (D ^ (1/t)) = profC (k - 1) (t - 1) + cCoef k ε * errH (t - 1) := by
  have hDpos : 0 < D := by linarith
  have hlogne : Real.log D ≠ 0 := ne_of_gt (Real.log_pos hD)
  unfold PhiC
  have hlog : Real.log (D ^ (1/t)) = Real.log D / t := by
    rw [Real.log_rpow hDpos]; ring
  rw [hlog]
  have : Real.log D / (Real.log D / t) - 1 = t - 1 := by
    field_simp
  rw [this]

/-- The composed profile is interval integrable. -/
lemma intervalIntegrable_PhiC (k : ℕ) (D ε : ℝ) (hD : 0 < D) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => PhiC k D ε (D ^ (1/t))) volume a b := by
  obtain ⟨C, hC0, hC⟩ := profC_bound (k - 1)
  set B : ℝ := C + |cCoef k ε| * Real.exp (-2) with hB
  have hmPhi : Measurable (fun u : ℝ => PhiC k D ε u) := by
    unfold PhiC
    exact ((profC_measurable (k-1)).comp (by fun_prop)).add
      ((measurable_errH.comp (by fun_prop)).const_mul _)
  have hmrpow : Measurable (fun t : ℝ => D ^ (1/t)) := by
    have h : (fun t : ℝ => D ^ (1/t)) = fun t => Real.exp (Real.log D * t⁻¹) := by
      funext t; rw [Real.rpow_def_of_pos hD, one_div]
    rw [h]; fun_prop
  have hm := hmPhi.comp hmrpow
  have hbound : ∀ t : ℝ, ‖PhiC k D ε (D^(1/t))‖ ≤ B := by
    intro t
    rw [Real.norm_eq_abs]
    have h1 : |profC (k-1) (Real.log D / Real.log (D^(1/t)) - 1)| ≤ C := by
      simpa [Real.norm_eq_abs] using hC (Real.log D / Real.log (D^(1/t)) - 1)
    have h2 : |cCoef k ε * errH (Real.log D / Real.log (D^(1/t)) - 1)|
        ≤ |cCoef k ε| * Real.exp (-2) := by
      rw [abs_mul, abs_of_nonneg (errH_nonneg _)]
      exact mul_le_mul_of_nonneg_left (errH_le_exp_neg_two _) (abs_nonneg _)
    unfold PhiC
    calc |profC (k-1) (Real.log D / Real.log (D^(1/t)) - 1)
            + cCoef k ε * errH (Real.log D / Real.log (D^(1/t)) - 1)|
        ≤ |profC (k-1) (Real.log D / Real.log (D^(1/t)) - 1)|
          + |cCoef k ε * errH (Real.log D / Real.log (D^(1/t)) - 1)| := abs_add_le _ _
      _ ≤ B := by rw [hB]; linarith
  exact ⟨IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B
          (Filter.Eventually.of_forall hbound),
         IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B
          (Filter.Eventually.of_forall hbound)⟩

/-- `(k-1) % 2 = 0` for odd `k`. -/
lemma odd_sub_one_mod {k : ℕ} (h : Odd k) : (k - 1) % 2 = 0 := by
  obtain ⟨m, hm⟩ := h
  subst hm
  omega

/-- `(k-1) % 2 = 1` for even `k ≥ 1`. -/
lemma even_sub_one_mod {k : ℕ} (hk : 1 ≤ k) (h : Even k) : (k - 1) % 2 = 1 := by
  obtain ⟨m, hm⟩ := h
  subst hm
  omega

/-- `profC j` vanishes below `1` (both parities). -/
lemma profC_eq_zero_of_lt_one : ∀ j : ℕ, ∀ σ : ℝ, σ < 1 → profC j σ = 0 := by
  intro j
  induction j with
  | zero =>
      intro σ hσ
      rw [profC_zero, if_neg (fun h => absurd h.1 (not_le.mpr hσ))]
  | succ n ih =>
      intro σ hσ
      rw [profC_succ]
      by_cases hpar : (n + 1) % 2 = 0
      · rw [if_pos hpar, if_neg (fun h => absurd h.1 (not_le.mpr hσ))]
      · rw [if_neg hpar, if_neg (fun h => absurd h.1 (by linarith))]

/-- `profC j` vanishes below `2` for odd `j` (the clamped parity). -/
lemma profC_eq_zero_of_lt_two : ∀ j : ℕ, j % 2 = 1 → ∀ σ : ℝ, σ < 2 → profC j σ = 0 := by
  intro j
  induction j with
  | zero =>
      intro hj
      exact absurd hj (by norm_num)
  | succ n ih =>
      intro hj σ hσ
      rw [profC_succ]
      by_cases hpar : (n + 1) % 2 = 0
      · exact absurd (hpar.symm.trans hj) (by norm_num)
      · rw [if_neg hpar, if_neg (fun h => absurd h.1 (not_le.mpr hσ))]

/-! ## The four budget inequalities, as an interface

The arithmetic of the induction step consumes exactly four scalar inequalities; they are proved
in `Submission.Work.ChenPlan.LinearSieve.JR2.budget_sharp` (as the conjunction `budget_sharp`).
Bundling them as a `Prop` lets the step lemmas be stated (and developed) without depending on
that module. -/
def Budgets : Prop :=
  (∀ s ε : ℝ, 2 ≤ s → 0 ≤ ε → ε ≤ 1/100 →
     ε * errH (s - 1) + (1 + ε) * (∫ t in Set.Ioi s, errH (t - 1)) / s ≤ (99/100) * errH s)
  ∧ (∀ s ε : ℝ, 1 ≤ s → s ≤ 3 → 0 ≤ ε → ε ≤ 1/100 →
     (1+ε)^2 * ((47/50) * Real.exp (-2)) / s + (1 + ε) * (3 / s) * ε * errH 2
       ≤ (99/100) * errH s)
  ∧ (∀ (m : ℕ) (s : ℝ), 2 ≤ m → 2 ≤ s →
     profC (m - 1) s + profC (m - 2) (s - 1) ≤ 990 * (99/100:ℝ)^(m - 2) * errH s)
  ∧ (∀ (m : ℕ) (ε s : ℝ), 3 ≤ m → Odd m → 1 ≤ s → s ≤ 3 → 0 ≤ ε → ε ≤ 1/100 →
     (2 + ε) * profC (m - 1) s + (1 + ε) * (3 / s) * profC (m - 2) 2
       ≤ 990 * (99/100:ℝ)^(m - 2) * errH s)

end

end Work.ChenPlan.LinearSieve.JR2
