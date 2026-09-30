import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.mrlas.norm_Kf_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integrability of `t ↦ ‖Kf f t‖² / t^{3+2α}` on `(0,∞)`

`Kf f t = Σ_{n ≤ t} f n log n` is a partial sum of a Dirichlet series with coefficients
`f n log n`, and for `t ≤ 1` it vanishes.  For `t ≥ 1` the trivial bound
`‖Kf f t‖ ≤ t log t` gives

`‖Kf f t‖² / t^{3+2α} ≤ (log t)² / t^{1+2α} ≤ (2/α)² / t^{1+α}`,

and `t ↦ t^{-(1+α)}` is integrable on `(1,∞)` because `-(1+α) < -1`.  This is the
dominating function used by the Mellin–Plancherel / Parseval argument for `Kf`.
-/

namespace Work.BMF.casdiv

open MeasureTheory Finset

/-- `Kf f t = Σ_{n ≤ ⌊t⌋} f n log n` vanishes for `t ≤ 1` (the only possible index is `n = 1`
and `log 1 = 0`). -/
private lemma Kf_eq_zero_of_le_one (f : ℕ → ℂ) {t : ℝ} (ht : t ≤ 1) : Work.BMF.Kf f t = 0 := by
  rw [Work.BMF.Kf]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn2 : n ≤ ⌊t⌋₊ := (Finset.mem_Icc.mp hn).2
  have hfl : ⌊t⌋₊ ≤ 1 := by
    have h := Nat.floor_mono ht
    simpa using h
  have hn' : n = 1 := le_antisymm (le_trans hn2 hfl) hn1
  subst hn'
  simp

/-- `t ↦ Kf f t` is measurable: it is a function of `⌊t⌋` only. -/
private lemma measurable_Kf (f : ℕ → ℂ) : Measurable (fun t : ℝ => Work.BMF.Kf f t) := by
  have hA : Measurable (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n, f m * (Real.log m : ℂ)) :=
    measurable_of_countable _
  have hcomp : Measurable
      (fun t : ℝ => (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n, f m * (Real.log m : ℂ)) ⌊t⌋₊) :=
    hA.comp (Nat.measurable_floor (R := ℝ))
  simpa only [Work.BMF.Kf] using hcomp

/-- For `t ≥ 1` and `α > 0`, `(log t)² ≤ (2/α)² * t^α`. -/
private lemma log_sq_le_rpow (α : ℝ) (hα : 0 < α) {t : ℝ} (ht : 1 ≤ t) :
    (Real.log t) ^ 2 ≤ (2 / α) ^ 2 * t ^ α := by
  have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le one_pos ht)
  have h1 : Real.log t ≤ (2 / α) * t ^ (α / 2) := by
    have h := Real.log_le_rpow_div ht0 (show (0 : ℝ) < α / 2 by linarith)
    have he : t ^ (α / 2) / (α / 2) = (2 / α) * t ^ (α / 2) := by field_simp
    rwa [he] at h
  have h2 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h3 : (Real.log t) ^ 2 ≤ ((2 / α) * t ^ (α / 2)) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have h4 : ((2 / α) * t ^ (α / 2)) ^ 2 = (2 / α) ^ 2 * t ^ α := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
    congr 1
    ring
  linarith [h3, h4.le]

theorem Kf_integrableOn (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) (Set.Ioi (0 : ℝ)) := by
  set C : ℝ := (2 / α) ^ 2 with hCdef
  have hmeas : Measurable (fun t : ℝ => ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) :=
    ((measurable_Kf f).norm.pow_const 2).div (by measurability)
  -- pointwise bound for `t ≥ 1`
  have hpoint : ∀ t : ℝ, 1 ≤ t →
      ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α) ≤ C * t ^ (-(1 + α)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hKf : ‖Work.BMF.Kf f t‖ ≤ t * Real.log t := Work.BMF.mrlas.norm_Kf_le f hb ht
    have hL : 0 ≤ Real.log t := Real.log_nonneg ht
    have hsq : (Real.log t) ^ 2 ≤ C * t ^ α := by
      have h := log_sq_le_rpow α hα ht
      rw [hCdef]
      exact h
    have hgoal : ‖Work.BMF.Kf f t‖ ^ 2 ≤ C * t ^ (2 + α) := by
      have h2 : ‖Work.BMF.Kf f t‖ ^ 2 ≤ (t * Real.log t) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hKf 2
      have h3 : (t * Real.log t) ^ 2 = t ^ (2 : ℝ) * (Real.log t) ^ 2 := by
        rw [mul_pow, ← Real.rpow_two t]
      have h5 : t ^ (2 : ℝ) * (Real.log t) ^ 2 ≤ t ^ (2 : ℝ) * (C * t ^ α) :=
        mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (le_of_lt ht0) 2)
      have h6 : t ^ (2 : ℝ) * (C * t ^ α) = C * t ^ (2 + α) := by
        rw [Real.rpow_add ht0]
        ring
      calc ‖Work.BMF.Kf f t‖ ^ 2 ≤ (t * Real.log t) ^ 2 := h2
        _ = t ^ (2 : ℝ) * (Real.log t) ^ 2 := h3
        _ ≤ t ^ (2 : ℝ) * (C * t ^ α) := h5
        _ = C * t ^ (2 + α) := h6
    have hexp : t ^ (-(1 + α)) * t ^ (3 + 2 * α) = t ^ (2 + α) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [div_le_iff₀ (Real.rpow_pos_of_pos ht0 _), mul_assoc, hexp]
    exact hgoal
  -- integrability on `(0,1]`: the integrand vanishes there
  have hleft : IntegrableOn (fun t : ℝ => ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      (Set.Ioc (0 : ℝ) 1) := by
    refine (integrableOn_zero (s := Set.Ioc (0 : ℝ) 1)).congr_fun ?_ measurableSet_Ioc
    intro t ht
    change (0 : ℝ) = ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)
    rw [Kf_eq_zero_of_le_one f ht.2]
    simp
  -- integrability on `(1,∞)`: dominated by a multiple of `t^{-(1+α)}`
  have hright : IntegrableOn (fun t : ℝ => ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      (Set.Ioi 1) := by
    have hmaj : IntegrableOn (fun t : ℝ => C * t ^ (-(1 + α))) (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul
        (integrableOn_Ioi_rpow_of_lt (a := -(1 + α)) (c := 1) (by linarith) one_pos) C
    refine Integrable.mono' hmaj hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)‖ ≤ C * t ^ (-(1 + α))
    rw [Real.norm_of_nonneg
      (div_nonneg (pow_nonneg (norm_nonneg _) 2) (Real.rpow_pos_of_pos (lt_trans one_pos ht) _).le)]
    exact hpoint t (le_of_lt ht)
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h0, h1⟩ | h1)
      · exact h0
      · linarith
    · intro h0
      by_cases h1 : t ≤ 1
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have h := hleft.union hright
  rwa [hset] at h

end Work.BMF.casdiv
