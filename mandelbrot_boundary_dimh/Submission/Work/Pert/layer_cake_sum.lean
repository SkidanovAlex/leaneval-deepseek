import Mathlib
import Submission.Work.Pert.lc_step_sep
import Submission.Work.Pert.lc_window_count
import Submission.Work.Pert.lc_geom_inj_sum

namespace Work.Pert

/-! # Layer-cake summation estimate (PERT)

The target lemma `layer_cake_sum` bounds, for a level quantity `H` that drops by at least
`15/16` at every step, the exponential sum `∑_{j ∈ F} exp (-(2π t j))` where `t j ≥ max 1 (c H j + β)`.

The proof uses three companion lemmas (proved in sibling files of this directory):

* `Work.Pert.lc_step_sep` : the drop hypothesis telescopes to a *linear* drop;
* `Work.Pert.lc_window_count` : because of the linear drop, at most one index of `F` falls in each
  window of length `15/16` of `H`-values, giving the counting bound `#{j ∈ F : H j ≤ L} ≤ 16L/15 + 1`;
* `Work.Pert.lc_geom_inj_sum` : a geometric-series bound for a finite set whose `u`-values are
  separated by a fixed gap `γ`.

Writing `a = max 1 β`, `γ = c * 15/16` and `u j = max 1 (β + c * H j)`, every term is at most
`exp (-(2π u j)) = exp (-(2π a)) · exp (-(2π (u j - a)))`.  Splitting `F` into the "flat" set
`{j : β + c * H j ≤ a}` (where `u j = a`, contributing at most `32/(15c) + 1` by the counting
lemma) and its complement (where the `u`-values are separated by `γ`, contributing at most
`1 + 1/(2πγ)` by the geometric bound) gives
`∑_{j ∈ F} exp (-(2π u j)) ≤ exp (-(2π a)) * (4 + 5/c)`. -/

theorem layer_cake_sum {c β : ℝ} (hc : 0 < c) (hβ : -1 ≤ β) {H : ℕ → ℝ} {n : ℕ}
    (hpos : ∀ j, j ≤ n → 0 ≤ H j)
    (hstep : ∀ j, j < n → H (j + 1) ≤ H j - 15 / 16)
    {t : ℕ → ℝ} (ht1 : ∀ j ≤ n, 1 ≤ t j) (ht2 : ∀ j ≤ n, c * H j + β ≤ t j)
    (F : Finset ℕ) (hF : ∀ j ∈ F, j ≤ n) :
    ∑ j ∈ F, Real.exp (-(2 * Real.pi * t j)) ≤
      Real.exp (-(2 * Real.pi * max 1 β)) * (4 + 5 / c) := by
  set a : ℝ := max 1 β with ha
  set γ : ℝ := c * (15 / 16) with hγ
  let u : ℕ → ℝ := fun j => max 1 (β + c * H j)
  have hu_eq : ∀ j, u j = max 1 (β + c * H j) := fun j => rfl
  have ha1 : 1 ≤ a := by rw [ha]; exact le_max_left 1 β
  have hγpos : 0 < γ := by rw [hγ]; positivity
  -- (1) termwise comparison `t j ≥ u j`
  have hterm : ∀ j ∈ F, Real.exp (-(2 * Real.pi * t j)) ≤ Real.exp (-(2 * Real.pi * u j)) := by
    intro j hj
    have hjle : j ≤ n := hF j hj
    have hut : u j ≤ t j := by
      rw [hu_eq j]
      exact max_le (ht1 j hjle) (by linarith [ht2 j hjle])
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  -- (2) the "flat" part `A = {j : β + c * H j ≤ a}`
  have hA : (∑ j ∈ F.filter (fun j => β + c * H j ≤ a),
        Real.exp (-(2 * Real.pi * (u j - a)))) ≤ 32 / (15 * c) + 1 := by
    have hconst : ∀ j ∈ F.filter (fun j => β + c * H j ≤ a),
        Real.exp (-(2 * Real.pi * (u j - a))) = 1 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hjle : j ≤ n := hF j hj.1
      have hcH0 : 0 ≤ c * H j := mul_nonneg hc.le (hpos j hjle)
      have hua : u j = a := by
        have h1 : u j ≤ a := by
          rw [hu_eq j]
          exact max_le ha1 hj.2
        have h2 : a ≤ u j := by
          rw [hu_eq j, ha]
          exact max_le_max le_rfl (by linarith)
        exact le_antisymm h1 h2
      rw [hua]
      simp
    have hsum1 : (∑ j ∈ F.filter (fun j => β + c * H j ≤ a),
          Real.exp (-(2 * Real.pi * (u j - a))))
        = ((F.filter (fun j => β + c * H j ≤ a)).card : ℝ) := by
      rw [Finset.sum_congr rfl hconst]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hsum1]
    have hsub : F.filter (fun j => β + c * H j ≤ a) ⊆ F.filter (fun j => H j ≤ 2 / c) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      have h2 : a - β ≤ 2 := by
        rw [ha]
        by_cases h : β ≤ 1
        · rw [max_eq_left h]; linarith
        · rw [max_eq_right (le_of_lt (not_le.mp h))]; linarith
      have h3 : c * H j ≤ 2 := by linarith [hj.2, h2]
      rw [le_div_iff₀ hc]
      linarith
    have hcard : ((F.filter (fun j => β + c * H j ≤ a)).card : ℝ)
        ≤ ((F.filter (fun j => H j ≤ 2 / c)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hwc := lc_window_count (H := H) (n := n) (F := F) hpos hstep hF (L := 2 / c)
      (by positivity)
    have harith : 16 * (2 / c) / 15 + 1 = 32 / (15 * c) + 1 := by
      field_simp; ring
    rw [harith] at hwc
    linarith
  -- (3) the decaying part `{j : ¬(β + c * H j ≤ a)}`
  have hS : (∑ j ∈ F.filter (fun j => ¬ (β + c * H j ≤ a)),
        Real.exp (-(2 * Real.pi * (u j - a)))) ≤ 1 + 1 / (2 * Real.pi * γ) := by
    apply lc_geom_inj_sum hγpos
    · intro j hj
      rw [Finset.mem_filter] at hj
      have h1 : a < β + c * H j := lt_of_not_ge hj.2
      rw [hu_eq j]
      exact lt_of_lt_of_le h1 (le_max_right 1 _)
    · intro j hj j' hj' hlt
      rw [Finset.mem_filter] at hj hj'
      have hjc : a < β + c * H j := lt_of_not_ge hj.2
      have hj'c : a < β + c * H j' := lt_of_not_ge hj'.2
      have huj : u j = β + c * H j := by
        rw [hu_eq j]
        exact max_eq_right (by linarith [hjc, ha1])
      have huj' : u j' = β + c * H j' := by
        rw [hu_eq j']
        exact max_eq_right (by linarith [hj'c, ha1])
      have hj'le : j' ≤ n := hF j' hj'.1
      have hsep := lc_step_sep hstep j j' (le_of_lt hlt) hj'le
      have hgap : (1 : ℝ) ≤ ((j' - j : ℕ) : ℝ) := by
        have : 1 ≤ j' - j := by omega
        exact_mod_cast this
      have hdiff : (15 / 16 : ℝ) ≤ H j - H j' := by
        have h2 : (15 / 16 : ℝ) ≤ (15 / 16) * ((j' - j : ℕ) : ℝ) := by nlinarith
        linarith
      have hcH : c * (15 / 16) ≤ c * (H j - H j') := mul_le_mul_of_nonneg_left hdiff hc.le
      rw [huj, huj', hγ]
      linarith
  -- (4) the numerical constants
  have harith2 : (32 / (15 * c) + 1) + (1 + 1 / (2 * Real.pi * γ)) ≤ 4 + 5 / c := by
    rw [hγ]
    have hq : 1 / (2 * Real.pi * (c * (15 / 16))) ≤ 8 / (15 * c) := by
      have hc15 : 0 < 2 * (c * (15 / 16)) := by positivity
      have hle : 2 * (c * (15 / 16)) ≤ 2 * Real.pi * (c * (15 / 16)) := by
        nlinarith [Real.pi_gt_three, hc]
      calc 1 / (2 * Real.pi * (c * (15 / 16))) ≤ 1 / (2 * (c * (15 / 16))) :=
            one_div_le_one_div_of_le hc15 hle
        _ = 8 / (15 * c) := by field_simp; ring
    have hb2 : (32 / (15 * c) + 1) + (1 + 8 / (15 * c)) ≤ 4 + 5 / c := by
      apply le_of_mul_le_mul_right _ hc
      have e1 : (32 / (15 * c) + 1 + (1 + 8 / (15 * c))) * c = 32 / 15 + 2 * c + 8 / 15 := by
        field_simp; ring
      have e2 : (4 + 5 / c) * c = 4 * c + 5 := by field_simp
      rw [e1, e2]
      linarith
    linarith
  have hsplit : (∑ j ∈ F, Real.exp (-(2 * Real.pi * (u j - a)))) =
      (∑ j ∈ F.filter (fun j => β + c * H j ≤ a), Real.exp (-(2 * Real.pi * (u j - a))))
      + (∑ j ∈ F.filter (fun j => ¬ (β + c * H j ≤ a)),
          Real.exp (-(2 * Real.pi * (u j - a)))) := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun j => β + c * H j ≤ a)
        (fun j => Real.exp (-(2 * Real.pi * (u j - a))))]
  have hinner : (∑ j ∈ F, Real.exp (-(2 * Real.pi * (u j - a)))) ≤ 4 + 5 / c := by
    rw [hsplit]
    linarith
  have main : (∑ j ∈ F, Real.exp (-(2 * Real.pi * t j)))
      ≤ Real.exp (-(2 * Real.pi * a)) * (4 + 5 / c) := by
    calc (∑ j ∈ F, Real.exp (-(2 * Real.pi * t j)))
        ≤ ∑ j ∈ F, Real.exp (-(2 * Real.pi * u j)) := Finset.sum_le_sum hterm
      _ = Real.exp (-(2 * Real.pi * a)) * ∑ j ∈ F, Real.exp (-(2 * Real.pi * (u j - a))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-(2 * Real.pi * a)) * (4 + 5 / c) :=
          mul_le_mul_of_nonneg_left hinner (Real.exp_nonneg _)
  rw [ha] at main
  exact main

end Work.Pert
