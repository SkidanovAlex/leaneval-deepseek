import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set

namespace Commons.Analysis.Integral

lemma intervalIntegral_indicator_Ioo {f : ℝ → ℂ} {a b p q : ℝ}
    (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b)
    (hint : IntervalIntegrable (fun u : ℝ => f u) (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b) :
    (∫ u in a..b, Set.indicator (Set.Ioo p q) (fun _ : ℝ => (1 : ℂ)) u * f u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
      = (∫ u in p..q, f u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  -- The scalar-1 indicator integrand equals the plain indicator `Set.indicator (Ioo p q) f`
  -- pointwise, since the indicator takes values 0 or 1 in ℂ.
  have h_eq :
      (fun u : ℝ => Set.indicator (Set.Ioo p q) (fun _ : ℝ => (1 : ℂ)) u * f u)
        = Set.indicator (Set.Ioo p q) f := by
    funext u
    by_cases hu : u ∈ Set.Ioo p q
    · simp [hu]
    · simp [hu]
  rw [h_eq]
  let g : ℝ → ℂ := Set.indicator (Set.Ioo p q) f
  change (∫ u in a..b, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
    = (∫ u in p..q, f u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
  have hab : a ≤ b := le_trans hap (le_trans hpq hqb)
  -- g is interval integrable on [a, b]: on the (unordered) interval of integration it is
  -- bounded by the integrable function f, so we use the indicator-integrability lemma.
  have hint_g : IntervalIntegrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
    dsimp [g]
    exact intervalIntegrable_iff.2
      (IntegrableOn.indicator hint.def' measurableSet_Ioo)
  have sub_ap : uIcc a p ⊆ uIcc a b := by
    intro x hx
    rw [uIcc_of_le hap] at hx
    rw [uIcc_of_le hab]
    exact ⟨hx.1, le_trans hx.2 (le_trans hpq hqb)⟩
  have sub_pq : uIcc p q ⊆ uIcc a b := by
    intro x hx
    rw [uIcc_of_le hpq] at hx
    rw [uIcc_of_le hab]
    exact ⟨le_trans hap hx.1, le_trans hx.2 hqb⟩
  have sub_qb : uIcc q b ⊆ uIcc a b := by
    intro x hx
    rw [uIcc_of_le hqb] at hx
    rw [uIcc_of_le hab]
    exact ⟨le_trans (le_trans hap hpq) hx.1, hx.2⟩
  have sub_aq : uIcc a q ⊆ uIcc a b := by
    intro x hx
    rw [uIcc_of_le (le_trans hap hpq)] at hx
    rw [uIcc_of_le hab]
    exact ⟨hx.1, le_trans hx.2 hqb⟩
  have hint_ap : IntervalIntegrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ) a p :=
    hint_g.mono_set sub_ap
  have hint_pq : IntervalIntegrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ) p q :=
    hint_g.mono_set sub_pq
  have hint_qb : IntervalIntegrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ) q b :=
    hint_g.mono_set sub_qb
  have hint_aq : IntervalIntegrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ) a q :=
    hint_g.mono_set sub_aq
  -- g vanishes identically on [a, p] and on [q, b].
  have h_zero_ap : EqOn g (fun _ : ℝ => (0 : ℂ)) (uIcc a p) := by
    intro x hx
    rw [uIcc_of_le hap] at hx
    have hx_not : x ∉ Set.Ioo p q := by
      intro hmem
      exact not_lt_of_ge hx.2 hmem.1
    simp [g, hx_not]
  have h_zero_qb : EqOn g (fun _ : ℝ => (0 : ℂ)) (uIcc q b) := by
    intro x hx
    rw [uIcc_of_le hqb] at hx
    have hx_not : x ∉ Set.Ioo p q := by
      intro hmem
      exact not_le_of_gt hmem.2 hx.1
    simp [g, hx_not]
  have h_left : (∫ u in a..p, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) = 0 := by
    calc
      (∫ u in a..p, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
          = (∫ _ in a..p, (0 : ℂ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
            exact intervalIntegral.integral_congr h_zero_ap
      _ = 0 := by simp
  have h_right : (∫ u in q..b, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) = 0 := by
    calc
      (∫ u in q..b, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
          = (∫ _ in q..b, (0 : ℂ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
            exact intervalIntegral.integral_congr h_zero_qb
      _ = 0 := by simp
  have h_mid : (∫ u in p..q, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
      = (∫ u in p..q, f u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hpq ?_
    intro x hx
    simp [g, hx]
  calc
    (∫ u in a..b, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
        = (∫ u in a..p, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
            + (∫ u in p..q, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
            + (∫ u in q..b, g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hint_aq hint_qb]
          rw [← intervalIntegral.integral_add_adjacent_intervals hint_ap hint_pq]
    _ = (∫ u in p..q, f u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
          rw [h_left, h_mid, h_right]
          simp

end Commons.Analysis.Integral