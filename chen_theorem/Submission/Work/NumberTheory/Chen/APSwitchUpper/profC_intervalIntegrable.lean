/-
# `APSwitchUpper.profC_intervalIntegrable` — integrability of the delay profiles

`profC n` (`APSwitchUpper.prof`) is the `n`-th member `f_{n+1}` of the classical
delay-difference family of the Rosser–Iwaniec linear sieve:

* `profC 0 s = (3 − s)/s` on `[1,3]` and `0` elsewhere;
* `profC (n+1) s` is `(∫ … profC n (t−1) dt)/s` on a half-open interval (with the
  clamp `max s 3` for even `n+1`), and `0` elsewhere.

Each `profC n` is a piecewise-defined function whose pieces are *integrals with
parameters in the integration bounds*, so its regularity is not immediate.  We
prove here the two structural facts, by induction on `n`:

* `profC_measurable` — `profC n` is Borel measurable;
* `profC_bound` — `profC n` is bounded (with an explicit recursive constant);

and deduce the requested `profC_intervalIntegrable`: `profC n` is interval
integrable on every interval, i.e. `Integrable` against `volume.restrict (Ioc a b)`
for all `a b`.  The proof of measurability of the recursion step writes the
parameter-dependent interval integral as a Bochner integral over `ℝ` of the
indicator of `{(s,t) | max s 3 < t ≤ N}` and applies
`MeasureTheory.StronglyMeasurable.integral_prod_right'`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **Measurability of the delay profiles.**  `profC n` is measurable for every `n`.

The recursion is an integral whose bounds depend on the argument, so the induction step
rewrites `∫ t in u s..v, profC n (t-1)` as `∫ t, (Ioc (u s) v).indicator (profC n (·-1)) t`
(a.e. everywhere, since `u s ≤ v` on the branch where the value is nonzero) and uses the
measurability of the Bochner integral in its parameter. -/
theorem profC_measurable : ∀ n : ℕ, Measurable (profC n) := by
  intro n
  induction n with
  | zero =>
      have h0 : profC 0 = fun s : ℝ => if 1 ≤ s ∧ s ≤ 3 then (3 - s) / s else 0 := rfl
      rw [h0]
      refine Measurable.ite ?_ ?_ measurable_const
      · exact (measurableSet_le measurable_const measurable_id).inter
              (measurableSet_le measurable_id measurable_const)
      · exact (measurable_const.sub measurable_id).div measurable_id
  | succ n ih =>
      have hh : Measurable (fun t : ℝ => profC n (t - 1)) := ih.comp (by fun_prop)
      have h3N : (3 : ℝ) ≤ (n : ℝ) + 4 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
      -- the `max s 3` branch (even recursion index)
      have hEven : Measurable (fun s : ℝ =>
          if 1 ≤ s ∧ s < (n : ℝ) + 4 then
            (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0) := by
        have hG : StronglyMeasurable (fun s : ℝ =>
            ∫ t, (Set.Ioc (max s 3) ((n : ℝ) + 4)).indicator (fun t => profC n (t - 1)) t
              ∂volume) := by
          have hφ : StronglyMeasurable (fun p : ℝ × ℝ =>
              (Set.Ioc (max p.1 3) ((n : ℝ) + 4)).indicator (fun t => profC n (t - 1)) p.2) := by
            have hset : MeasurableSet {p : ℝ × ℝ | max p.1 3 < p.2 ∧ p.2 ≤ (n : ℝ) + 4} :=
              (measurableSet_lt (by fun_prop) measurable_snd).inter
                (measurableSet_le measurable_snd measurable_const)
            have hif : (fun p : ℝ × ℝ =>
                (Set.Ioc (max p.1 3) ((n : ℝ) + 4)).indicator (fun t => profC n (t - 1)) p.2)
                = fun p : ℝ × ℝ =>
                    if max p.1 3 < p.2 ∧ p.2 ≤ (n : ℝ) + 4 then profC n (p.2 - 1) else 0 := by
              funext p; simp only [Set.indicator, Set.mem_Ioc]
            rw [hif]
            exact (Measurable.ite hset (hh.comp measurable_snd) measurable_const).stronglyMeasurable
          exact hφ.integral_prod_right'
        have hE : (fun s : ℝ => if 1 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0)
            = (fun s : ℝ => if 1 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t, (Set.Ioc (max s 3) ((n : ℝ) + 4)).indicator
                (fun t => profC n (t - 1)) t ∂volume) / s else 0) := by
          funext s
          by_cases hs : 1 ≤ s ∧ s < (n : ℝ) + 4
          · rw [if_pos hs, if_pos hs]
            congr 1
            rw [intervalIntegral.integral_of_le
              (max_le (le_of_lt hs.2) h3N)]
            exact (MeasureTheory.integral_indicator measurableSet_Ioc).symm
          · rw [if_neg hs, if_neg hs]
        rw [hE]
        refine Measurable.ite ?_ ?_ measurable_const
        · exact (measurableSet_le measurable_const measurable_id).inter
            (measurableSet_lt measurable_id measurable_const)
        · exact hG.measurable.div measurable_id
      -- the `s` branch (odd recursion index)
      have hOdd : Measurable (fun s : ℝ =>
          if 2 ≤ s ∧ s < (n : ℝ) + 4 then
            (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0) := by
        have hG : StronglyMeasurable (fun s : ℝ =>
            ∫ t, (Set.Ioc s ((n : ℝ) + 4)).indicator (fun t => profC n (t - 1)) t
              ∂volume) := by
          have hφ : StronglyMeasurable (fun p : ℝ × ℝ =>
              (Set.Ioc p.1 ((n : ℝ) + 4)).indicator (fun t => profC n (t - 1)) p.2) := by
            have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ (n : ℝ) + 4} :=
              (measurableSet_lt measurable_fst measurable_snd).inter
                (measurableSet_le measurable_snd measurable_const)
            have hif : (fun p : ℝ × ℝ =>
                (Set.Ioc p.1 ((n : ℝ) + 4)).indicator (fun t => profC n (t - 1)) p.2)
                = fun p : ℝ × ℝ =>
                    if p.1 < p.2 ∧ p.2 ≤ (n : ℝ) + 4 then profC n (p.2 - 1) else 0 := by
              funext p; simp only [Set.indicator, Set.mem_Ioc]
            rw [hif]
            exact (Measurable.ite hset (hh.comp measurable_snd) measurable_const).stronglyMeasurable
          exact hφ.integral_prod_right'
        have hE : (fun s : ℝ => if 2 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0)
            = (fun s : ℝ => if 2 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t, (Set.Ioc s ((n : ℝ) + 4)).indicator
                (fun t => profC n (t - 1)) t ∂volume) / s else 0) := by
          funext s
          by_cases hs : 2 ≤ s ∧ s < (n : ℝ) + 4
          · rw [if_pos hs, if_pos hs]
            congr 1
            rw [intervalIntegral.integral_of_le (le_of_lt hs.2)]
            exact (MeasureTheory.integral_indicator measurableSet_Ioc).symm
          · rw [if_neg hs, if_neg hs]
        rw [hE]
        refine Measurable.ite ?_ ?_ measurable_const
        · exact (measurableSet_le measurable_const measurable_id).inter
            (measurableSet_lt measurable_id measurable_const)
        · exact hG.measurable.div measurable_id
      have hfun : profC (n + 1) = fun s : ℝ =>
          if (n + 1) % 2 = 0 then
            (if 1 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0)
          else
            (if 2 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0) := by
        funext s; rw [profC_succ]
      rw [hfun]
      by_cases hpar : (n + 1) % 2 = 0
      · have h1 : (fun s : ℝ => if (n + 1) % 2 = 0 then
            (if 1 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0)
          else
            (if 2 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0))
          = (fun s : ℝ => if 1 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0) := by
          funext s; rw [if_pos hpar]
        rw [h1]; exact hEven
      · have h1 : (fun s : ℝ => if (n + 1) % 2 = 0 then
            (if 1 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0)
          else
            (if 2 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0))
          = (fun s : ℝ => if 2 ≤ s ∧ s < (n : ℝ) + 4 then
              (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0) := by
          funext s; rw [if_neg hpar]
        rw [h1]; exact hOdd

/-- **Boundedness of the delay profiles.**  `profC n` is bounded on `ℝ`, with the explicit
recursive constant `C_0 = 2`, `C_{n+1} = C_n·(n+2) + 1`: on the support the recursion divides
an integral of `profC n (·-1)` over an interval of length `≤ n+2` by `s ≥ 1`. -/
theorem profC_bound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖profC n s‖ ≤ C := by
  intro n
  induction n with
  | zero =>
      refine ⟨2, by norm_num, fun s => ?_⟩
      rw [profC_zero]
      by_cases h : 1 ≤ s ∧ s ≤ 3
      · rw [if_pos h]
        have hs0 : 0 < s := by linarith [h.1]
        have h3s : 0 ≤ 3 - s := by linarith [h.2]
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg h3s, abs_of_pos hs0, div_le_iff₀ hs0]
        linarith [h.1]
      · rw [if_neg h]
        norm_num
  | succ n ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      refine ⟨C * ((n : ℝ) + 2) + 1, by positivity, fun s => ?_⟩
      have hCn : 0 ≤ C * ((n : ℝ) + 2) := mul_nonneg hC0 (by positivity)
      have h3N : (3 : ℝ) ≤ (n : ℝ) + 4 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
      rw [profC_succ]
      by_cases hpar : (n + 1) % 2 = 0
      · rw [if_pos hpar]
        by_cases h : 1 ≤ s ∧ s < (n : ℝ) + 4
        · rw [if_pos h]
          have hs0 : 0 < s := by linarith [h.1]
          have hA : max s 3 ≤ (n : ℝ) + 4 := max_le (le_of_lt h.2) h3N
          have hlen : |((n : ℝ) + 4) - max s 3| ≤ (n : ℝ) + 2 := by
            rw [abs_of_nonneg (by linarith [hA])]
            linarith [le_max_right s (3 : ℝ)]
          have hI : ‖∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)‖ ≤ C * ((n : ℝ) + 2) :=
            le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hC (x - 1)))
              (mul_le_mul_of_nonneg_left hlen hC0)
          rw [norm_div, Real.norm_of_nonneg (le_of_lt hs0), div_le_iff₀ hs0]
          have hstep : C * ((n : ℝ) + 2) ≤ (C * ((n : ℝ) + 2) + 1) * s :=
            by nlinarith [hCn, h.1]
          linarith [hI, hstep]
        · rw [if_neg h, norm_zero]
          linarith
      · rw [if_neg hpar]
        by_cases h : 2 ≤ s ∧ s < (n : ℝ) + 4
        · rw [if_pos h]
          have hs0 : 0 < s := by linarith [h.1]
          have hlen : |((n : ℝ) + 4) - s| ≤ (n : ℝ) + 2 := by
            rw [abs_of_nonneg (by linarith [h.2])]
            linarith [h.1]
          have hI : ‖∫ t in s..((n : ℝ) + 4), profC n (t - 1)‖ ≤ C * ((n : ℝ) + 2) :=
            le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hC (x - 1)))
              (mul_le_mul_of_nonneg_left hlen hC0)
          rw [norm_div, Real.norm_of_nonneg (le_of_lt hs0), div_le_iff₀ hs0]
          have hstep : C * ((n : ℝ) + 2) ≤ (C * ((n : ℝ) + 2) + 1) * s :=
            by nlinarith [hCn, h.1]
          linarith [hI, hstep]
        · rw [if_neg h, norm_zero]
          linarith

theorem profC_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (Work.NumberTheory.Chen.APSwitchUpper.profC n) MeasureTheory.volume a b := by
  obtain ⟨C, _hC0, hC⟩ := profC_bound n
  have hm : Measurable (profC n) := profC_measurable n
  refine ⟨Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC),
         Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)⟩

end

end Work.NumberTheory.Chen.APSwitchUpper
