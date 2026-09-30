import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open MeasureTheory

set_option linter.unusedVariables false

/-- The step function `y ↦ ∑_{n ∈ ℕ ∩ [y, y+H']} g n` is integrable on any bounded window
`(X, X+L]` with `0 < X`: on that window the summation index always lies in the fixed finite
range `[⌈X⌉₊, ⌊X+L+H'⌋₊]`, so the function is bounded there by `∑_{n} ‖g n‖` over that range
and is a finite sum of indicators of measurable sets. -/
theorem window_norm_integrableOn_Ioc {g : ℕ → ℂ} {X L H' : ℝ} (hX : 0 < X) :
    IntegrableOn (fun y : ℝ => ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖)
      (Set.Ioc X (X + L)) volume := by
  have hma : Measurable (fun y : ℝ => ∑ n ∈ Work.BMF.natIcc y (y + H'), g n) := by
    have hpair : Measurable (fun y : ℝ => (⌈y⌉₊, ⌊y + H'⌋₊)) := by measurability
    have hF : Measurable (fun pq : ℕ × ℕ => ∑ n ∈ Finset.Icc pq.1 pq.2, g n) :=
      measurable_of_countable _
    exact hF.comp hpair
  let B : Finset ℕ := Finset.Icc ⌈X⌉₊ ⌊X + L + H'⌋₊
  let C : ℝ := ∑ n ∈ B, ‖g n‖
  have hbound : ∀ y ∈ Set.Ioc X (X + L), ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ ≤ C := by
    intro y hy
    have hsub : Work.BMF.natIcc y (y + H') ⊆ B := by
      intro n hn
      have hn' : ⌈y⌉₊ ≤ n ∧ n ≤ ⌊y + H'⌋₊ :=
        Finset.mem_Icc.mp (show n ∈ Finset.Icc ⌈y⌉₊ ⌊y + H'⌋₊ from hn)
      refine Finset.mem_Icc.mpr ⟨le_trans (Nat.ceil_mono (le_of_lt hy.1)) hn'.1, ?_⟩
      exact le_trans hn'.2 (Nat.floor_mono (by linarith [hy.2]))
    calc ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖
        ≤ ∑ n ∈ Work.BMF.natIcc y (y + H'), ‖g n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ B, ‖g n‖ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => norm_nonneg _)
      _ = C := rfl
  have hfin : volume (Set.Ioc X (X + L)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  apply Measure.integrableOn_of_bounded (M := C) hfin hma.norm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  simpa using hbound y hy

theorem window_norm_intervalIntegrable {g : ℕ → ℂ} {x L H' a b : ℝ} (hx : 1 ≤ x) (hH' : 0 ≤ H')
    (ha : a ∈ Set.Icc x (x + L)) (hb : b ∈ Set.Icc x (x + L)) :
    IntervalIntegrable (fun y : ℝ => ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖) MeasureTheory.volume a b := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hmain := window_norm_integrableOn_Ioc (g := g) (X := x) (L := L) (H' := H') hxpos
  obtain ⟨hax, haL⟩ := Set.mem_Icc.mp ha
  obtain ⟨hbx, hbL⟩ := Set.mem_Icc.mp hb
  have h1 : Set.Ioc a b ⊆ Set.Ioc x (x + L) :=
    fun y hy => ⟨lt_of_le_of_lt hax hy.1, le_trans hy.2 hbL⟩
  have h2 : Set.Ioc b a ⊆ Set.Ioc x (x + L) :=
    fun y hy => ⟨lt_of_le_of_lt hbx hy.1, le_trans hy.2 haL⟩
  exact ⟨hmain.mono_set h1, hmain.mono_set h2⟩

end Work.N8
