import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs
import Submission.Work.N8.window_norm_intervalIntegrable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lower bound for the average of short sums over shifts

For `g : ℕ → ℂ` with `‖g n‖ ≤ 1`, and reals `1 ≤ x`, `0 < H' ≤ L`, the average over the shifts
`y ∈ [x, x + L - H']` of the short sum `Σ_{n ∈ ℕ ∩ [y, y+H']} g n` dominates `H'` times the full
sum over `[x, x+L]`, up to an error `4 H' (⌊H'⌋ + 1)`.

The proof computes the (complex) integral `∫_x^{x+L-H'} Σ_{n ∈ ℕ ∩ [y,y+H']} g n dy` by Fubini:
each integer `n` contributes `g n` weighted by the length `w n = |[x,R] ∩ [n-H', n]|`
(`R = x + L - H'`).  The weight `w n` is `H'` for all `n` in the "core" `x + H' ≤ n ≤ R`, and the
total deficit `Σ_{n ∈ ℕ ∩ [x,x+L]} (H' - w n)` is at most `H'` times the number of indices outside
the core, which is at most `2 (⌊H'⌋ + 1)`.
-/

namespace Work.N8

open MeasureTheory intervalIntegral

/-- Membership in `Work.BMF.natIcc a b` rewritten as a pair of real inequalities (for `0 ≤ b`). -/
lemma mem_natIcc {a b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    n ∈ Work.BMF.natIcc a b ↔ a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b := by
  rw [Work.BMF.natIcc, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb]

/-- The interval integral of the indicator of a closed interval equals the (clamped) length of
its intersection with the integration range. -/
lemma indicator_integral_Icc (a b c d : ℝ) (hab : a ≤ b) :
    ∫ y in a..b, ((Set.Icc c d).indicator (fun _ => (1:ℝ)) y : ℂ)
      = ((max 0 (min b d - max a c) : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le hab]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [Set.indicator_indicator]
  simp only [Complex.ofReal_one]
  rw [MeasureTheory.integral_indicator_const (1:ℂ) (measurableSet_Ioc.inter measurableSet_Icc)]
  rw [Complex.real_smul, mul_one]
  congr 1
  rw [MeasureTheory.measureReal_def]
  have h1 : Set.Ioc a b ∩ Set.Icc c d ⊆ Set.Icc (max a c) (min b d) := by
    intro y hy
    exact ⟨max_le (le_of_lt hy.1.1) hy.2.1, le_min hy.1.2 hy.2.2⟩
  have h2 : Set.Icc (max a c) (min b d) ⊆ (Set.Ioc a b ∩ Set.Icc c d) ∪ {a} := by
    intro y hy
    rcases eq_or_lt_of_le (le_trans (le_max_left a c) hy.1) with h | h
    · exact Or.inr (Set.mem_singleton_iff.mpr h.symm)
    · exact Or.inl ⟨⟨h, le_trans hy.2 (min_le_left _ _)⟩,
        ⟨le_trans (le_max_right a c) hy.1, le_trans hy.2 (min_le_right _ _)⟩⟩
  have hnull : volume (Set.Icc (max a c) (min b d) \ (Set.Ioc a b ∩ Set.Icc c d)) = 0 :=
    measure_mono_null (fun y hy => by
      rcases h2 hy.1 with h | h
      · exact absurd h hy.2
      · exact h) Real.volume_singleton
  rw [measure_eq_measure_of_null_sdiff h1 hnull, Real.volume_Icc, ENNReal.toReal_ofReal', max_comm]

/-- A constant multiple of the indicator of a closed interval is interval-integrable. -/
lemma intervalIntegrable_const_indicator (c : ℂ) (p q a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => c * ((Set.Icc p q).indicator (fun _ => (1:ℝ)) y : ℂ))
      volume a b := by
  have hbd : ∀ y : ℝ, ‖c * ((Set.Icc p q).indicator (fun _ => (1:ℝ)) y : ℂ)‖ ≤ ‖c‖ := by
    intro y
    rw [norm_mul]
    have h1 : ‖((Set.Icc p q).indicator (fun _ => (1:ℝ)) y : ℂ)‖ ≤ 1 := by
      by_cases hy : y ∈ Set.Icc p q
      · rw [Set.indicator_of_mem hy]; simp
      · rw [Set.indicator_of_notMem hy]; simp
    calc ‖c‖ * ‖((Set.Icc p q).indicator (fun _ => (1:ℝ)) y : ℂ)‖ ≤ ‖c‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg c)
      _ = ‖c‖ := mul_one _
  have hmeas : Measurable
      (fun y : ℝ => c * ((Set.Icc p q).indicator (fun _ => (1:ℝ)) y : ℂ)) := by
    exact (by measurability : Measurable
      (fun y : ℝ => ((Set.Icc p q).indicator (fun _ => (1:ℝ)) y : ℂ))).const_mul c
  constructor
  · exact Measure.integrableOn_of_bounded (M := ‖c‖)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  · exact Measure.integrableOn_of_bounded (M := ‖c‖)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbd)

private lemma card_bad_left' (x L H' : ℝ) (hx : 1 ≤ x) (hH' : 0 < H') (hH'L : H' ≤ L) :
    ((Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => (n:ℝ) < x + H')).card ≤ ⌊H'⌋₊ + 1 := by
  have hsub : (Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => (n:ℝ) < x + H')
      ⊆ Finset.Icc ⌈x⌉₊ ⌊x + H'⌋₊ := by
    intro n hn
    rw [Finset.mem_filter, Work.BMF.natIcc, Finset.mem_Icc] at hn
    exact Finset.mem_Icc.mpr ⟨hn.1.1, Nat.le_floor (le_of_lt hn.2)⟩
  have hfloor : ⌊x + H'⌋₊ ≤ ⌈x⌉₊ + ⌊H'⌋₊ := by
    have h1 : x + H' ≤ (⌈x⌉₊ : ℝ) + H' := by have := Nat.le_ceil x; linarith
    calc ⌊x + H'⌋₊ ≤ ⌊(⌈x⌉₊ : ℝ) + H'⌋₊ := Nat.floor_mono h1
      _ = ⌊H' + (⌈x⌉₊ : ℝ)⌋₊ := by rw [add_comm]
      _ = ⌊H'⌋₊ + ⌈x⌉₊ := Nat.floor_add_natCast (le_of_lt hH') ⌈x⌉₊
      _ = ⌈x⌉₊ + ⌊H'⌋₊ := by omega
  calc ((Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => (n:ℝ) < x + H')).card
      ≤ (Finset.Icc ⌈x⌉₊ ⌊x + H'⌋₊).card := Finset.card_le_card hsub
    _ = ⌊x + H'⌋₊ + 1 - ⌈x⌉₊ := by rw [Nat.card_Icc]
    _ ≤ ⌊H'⌋₊ + 1 := by omega

private lemma card_bad_right' (x L H' : ℝ) (hx : 1 ≤ x) (hH' : 0 < H') (hH'L : H' ≤ L) :
    ((Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => x + L - H' < (n:ℝ))).card
      ≤ ⌊H'⌋₊ + 1 := by
  have hRnn : 0 ≤ x + L - H' := by linarith
  have hsub : (Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => x + L - H' < (n:ℝ))
      ⊆ Finset.Icc (⌊x + L - H'⌋₊ + 1) ⌊x + L⌋₊ := by
    intro n hn
    rw [Finset.mem_filter, Work.BMF.natIcc, Finset.mem_Icc] at hn
    refine Finset.mem_Icc.mpr ⟨?_, hn.1.2⟩
    have hfl : (⌊x + L - H'⌋₊ : ℝ) ≤ x + L - H' := Nat.floor_le hRnn
    have hlt' : (⌊x + L - H'⌋₊ : ℝ) < (n : ℝ) := lt_of_le_of_lt hfl hn.2
    have := Nat.cast_lt.mp hlt'
    omega
  have hfloor : ⌊x + L⌋₊ ≤ ⌊x + L - H'⌋₊ + ⌊H'⌋₊ + 1 := by
    have hlt : x + L < ((⌊x + L - H'⌋₊ + ⌊H'⌋₊ + 2 : ℕ) : ℝ) := by
      have h1 := Nat.lt_floor_add_one (x + L - H')
      have h2 := Nat.lt_floor_add_one H'
      push_cast
      linarith
    have h3 := (Nat.floor_lt (by linarith : (0:ℝ) ≤ x + L)).mpr hlt
    omega
  calc ((Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => x + L - H' < (n:ℝ))).card
      ≤ (Finset.Icc (⌊x + L - H'⌋₊ + 1) ⌊x + L⌋₊).card := Finset.card_le_card hsub
    _ = ⌊x + L⌋₊ + 1 - (⌊x + L - H'⌋₊ + 1) := by rw [Nat.card_Icc]
    _ = ⌊x + L⌋₊ - ⌊x + L - H'⌋₊ := by omega
    _ ≤ ⌊H'⌋₊ + 1 := by omega

theorem shift_avg_lower {g : ℕ → ℂ} {x L H' : ℝ} (hx : 1 ≤ x) (hH' : 0 < H') (hH'L : H' ≤ L)
    (hg : ∀ n, ‖g n‖ ≤ 1) :
    H' * ‖∑ n ∈ Work.BMF.natIcc x (x + L), g n‖ - 4 * H' * ((⌊H'⌋₊ : ℝ) + 1)
      ≤ ∫ y in x..(x + L - H'), ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ := by
  set R : ℝ := x + L - H' with hRdef
  have hxR : x ≤ R := by rw [hRdef]; linarith
  set F : Finset ℕ := Finset.Icc 0 ⌊x + L⌋₊ with hFdef
  set ww : ℕ → ℝ := fun n => max 0 (min R (n:ℝ) - max x ((n:ℝ) - H')) with hwwdef
  have hww : ∀ n : ℕ, ww n = max 0 (min R (n:ℝ) - max x ((n:ℝ) - H')) := fun n => by rw [hwwdef]
  -- basic properties of the weight `ww`
  have hww_le : ∀ n : ℕ, ww n ≤ H' := by
    intro n
    rw [hww n]
    have hW : min R (n:ℝ) - max x ((n:ℝ) - H') ≤ H' := by
      have h1 : min R (n:ℝ) ≤ (n:ℝ) := min_le_right _ _
      have h2 : (n:ℝ) - H' ≤ max x ((n:ℝ) - H') := le_max_right _ _
      linarith
    calc max 0 (min R (n:ℝ) - max x ((n:ℝ) - H')) ≤ max 0 H' := max_le_max le_rfl hW
      _ = H' := max_eq_right (le_of_lt hH')
  have hww_eq : ∀ n : ℕ, x + H' ≤ (n:ℝ) → (n:ℝ) ≤ R → ww n = H' := by
    intro n h1 h2
    rw [hww n]
    have hmin : min R (n:ℝ) = (n:ℝ) := min_eq_right h2
    have hmax : max x ((n:ℝ) - H') = (n:ℝ) - H' := max_eq_right (by linarith)
    rw [hmin, hmax]
    have hsub : (n:ℝ) - ((n:ℝ) - H') = H' := by ring
    rw [hsub, max_eq_right (le_of_lt hH')]
  have hww_zero : ∀ n : ℕ, (n:ℝ) < x → ww n = 0 := by
    intro n hn
    have h1 : min R (n:ℝ) = (n:ℝ) := min_eq_right (le_trans (le_of_lt hn) hxR)
    have h2 : max x ((n:ℝ) - H') = x := max_eq_left (by linarith)
    rw [hww n, h1, h2, max_eq_left]
    linarith [le_of_lt hn]
  -- containment of the sliding window in the fixed index range
  have hsubF : ∀ y : ℝ, y ≤ R → Work.BMF.natIcc y (y + H') ⊆ F := by
    intro y hy n hn
    rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
    rw [hFdef, Finset.mem_Icc]
    exact ⟨Nat.zero_le _, le_trans hn.2 (Nat.floor_le_floor (by linarith))⟩
  -- pointwise identity: the sliding sum is the fixed-sum of `g n` against indicators
  have hpt : ∀ y : ℝ, x ≤ y → y ≤ R →
      (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)
        = ∑ n ∈ F, g n * ((Set.Icc ((n:ℝ) - H') (n)).indicator (fun _ => (1:ℝ)) y : ℂ) := by
    intro y hyx hyR
    have hy0 : 0 ≤ y + H' := by linarith
    have hsub : Work.BMF.natIcc y (y + H') ⊆ F := hsubF y hyR
    have hpt' : ∀ n : ℕ,
        ((Set.Icc ((n:ℝ) - H') (n)).indicator (fun _ => (1:ℝ)) y : ℂ)
          = (if n ∈ Work.BMF.natIcc y (y + H') then (1:ℂ) else 0) := by
      intro n
      by_cases h : y ∈ Set.Icc ((n:ℝ) - H') (n)
      · have hmem : n ∈ Work.BMF.natIcc y (y + H') := by
          rw [mem_natIcc hy0]; exact ⟨h.2, by linarith [h.1]⟩
        rw [Set.indicator_of_mem h, if_pos hmem]; simp
      · have hmem : n ∉ Work.BMF.natIcc y (y + H') := by
          intro hc; rw [mem_natIcc hy0] at hc; exact h ⟨by linarith [hc.2], hc.1⟩
        rw [Set.indicator_of_notMem h, if_neg hmem]
    have h1 : (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)
        = ∑ n ∈ Work.BMF.natIcc y (y + H'),
            g n * (if n ∈ Work.BMF.natIcc y (y + H') then (1:ℂ) else 0) := by
      apply Finset.sum_congr rfl; intro n hn; rw [if_pos hn, mul_one]
    have h2 : (∑ n ∈ Work.BMF.natIcc y (y + H'),
            g n * (if n ∈ Work.BMF.natIcc y (y + H') then (1:ℂ) else 0))
        = ∑ n ∈ F, g n * (if n ∈ Work.BMF.natIcc y (y + H') then (1:ℂ) else 0) :=
      Finset.sum_subset hsub (fun n _ hn => by rw [if_neg hn, mul_zero])
    calc (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)
        = ∑ n ∈ F, g n * (if n ∈ Work.BMF.natIcc y (y + H') then (1:ℂ) else 0) := by
            rw [h1, h2]
      _ = ∑ n ∈ F, g n * ((Set.Icc ((n:ℝ) - H') (n)).indicator (fun _ => (1:ℝ)) y : ℂ) := by
            apply Finset.sum_congr rfl; intro n hn
            rw [← hpt' n]
  -- the `F`-sum reduces to a sum over `natIcc x (x+L)`
  have hsubFxL : Work.BMF.natIcc x (x + L) ⊆ F := by
    intro n hn
    rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
    rw [hFdef, Finset.mem_Icc]
    exact ⟨Nat.zero_le _, hn.2⟩
  have hone : ∀ n ∈ F, n ∉ Work.BMF.natIcc x (x + L) → g n * (ww n : ℂ) = 0 := by
    intro n hnF hnN
    have hnlt : n < ⌈x⌉₊ := by
      rw [hFdef, Finset.mem_Icc] at hnF
      by_contra hc
      exact hnN (by rw [Work.BMF.natIcc, Finset.mem_Icc]; exact ⟨le_of_not_gt hc, hnF.2⟩)
    have hxc : (n:ℝ) < x := by
      have h1 : (n:ℝ) + 1 ≤ (⌈x⌉₊ : ℝ) := by
        have := Nat.lt_iff_add_one_le.mp hnlt; exact_mod_cast this
      have h2 : (⌈x⌉₊ : ℝ) - 1 < x := by
        have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ x by linarith); linarith
      linarith
    rw [hww_zero n hxc]; simp
  -- evaluation of the integral via Fubini
  have hInt : (∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n))
      = ∑ n ∈ Work.BMF.natIcc x (x + L), g n * (ww n : ℂ) := by
    rw [intervalIntegral.integral_congr
      (g := fun y => ∑ n ∈ F,
        g n * ((Set.Icc ((n:ℝ) - H') (n)).indicator (fun _ => (1:ℝ)) y : ℂ))
      (fun y hy => hpt y (min_eq_left hxR ▸ hy.1) (max_eq_right hxR ▸ hy.2))]
    rw [intervalIntegral.integral_finset_sum
      (f := fun n y => g n * ((Set.Icc ((n:ℝ) - H') (n)).indicator (fun _ => (1:ℝ)) y : ℂ))
      (s := F) (fun n hn => intervalIntegrable_const_indicator (g n) ((n:ℝ)-H') n x R)]
    rw [Finset.sum_congr rfl (fun n hn =>
      by rw [intervalIntegral.integral_const_mul, indicator_integral_Icc _ _ _ _ hxR])]
    rw [← Finset.sum_subset hsubFxL hone]
  -- the deficit sum
  have hbad_card : (((Work.BMF.natIcc x (x + L)).filter
      (fun (n:ℕ) => (n:ℝ) < x + H' ∨ R < (n:ℝ))).card) ≤ 4 * (⌊H'⌋₊ + 1) := by
    have hsplit : (Work.BMF.natIcc x (x + L)).filter
          (fun (n:ℕ) => (n:ℝ) < x + H' ∨ R < (n:ℝ))
        = ((Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => (n:ℝ) < x + H'))
          ∪ ((Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => R < (n:ℝ))) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_union]
      tauto
    rw [hsplit]
    have h1 := card_bad_left' x L H' hx hH' hH'L
    have h2 : ((Work.BMF.natIcc x (x + L)).filter (fun (n:ℕ) => R < (n:ℝ))).card
        ≤ ⌊H'⌋₊ + 1 := by
      rw [hRdef]; exact card_bad_right' x L H' hx hH' hH'L
    calc _ ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ (⌊H'⌋₊ + 1) + (⌊H'⌋₊ + 1) := add_le_add h1 h2
      _ ≤ 4 * (⌊H'⌋₊ + 1) := by omega
  have hdef : ∑ n ∈ Work.BMF.natIcc x (x + L), (H' - ww n)
      ≤ 4 * H' * ((⌊H'⌋₊ : ℝ) + 1) := by
    have hsum_eq : ∑ n ∈ (Work.BMF.natIcc x (x + L)).filter
            (fun (n:ℕ) => (n:ℝ) < x + H' ∨ R < (n:ℝ)), (H' - ww n)
        = ∑ n ∈ Work.BMF.natIcc x (x + L), (H' - ww n) := by
      apply Finset.sum_subset
      · intro n hn; exact (Finset.mem_filter.mp hn).1
      · intro n hn hnf
        have hp : ¬ ((n:ℝ) < x + H' ∨ R < (n:ℝ)) := fun hp =>
          hnf (Finset.mem_filter.mpr ⟨hn, hp⟩)
        rw [not_or, not_lt, not_lt] at hp
        rw [hww_eq n hp.1 hp.2, sub_self]
    rw [← hsum_eq]
    have hle : ∀ n ∈ (Work.BMF.natIcc x (x + L)).filter
            (fun (n:ℕ) => (n:ℝ) < x + H' ∨ R < (n:ℝ)), (H' - ww n) ≤ H' := by
      intro n hn
      have h0 : 0 ≤ ww n := by rw [hww n]; exact le_max_left 0 _
      linarith
    calc ∑ n ∈ (Work.BMF.natIcc x (x + L)).filter
              (fun (n:ℕ) => (n:ℝ) < x + H' ∨ R < (n:ℝ)), (H' - ww n)
        ≤ ∑ n ∈ (Work.BMF.natIcc x (x + L)).filter
              (fun (n:ℕ) => (n:ℝ) < x + H' ∨ R < (n:ℝ)), H' := Finset.sum_le_sum hle
      _ = (((Work.BMF.natIcc x (x + L)).filter
              (fun (n:ℕ) => (n:ℝ) < x + H' ∨ R < (n:ℝ))).card : ℝ) * H' := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * ((⌊H'⌋₊ : ℝ) + 1)) * H' := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hH')
            exact_mod_cast hbad_card
      _ = 4 * H' * ((⌊H'⌋₊ : ℝ) + 1) := by ring
  -- comparison of the full sum with the integral
  have hkey : ‖(H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)
        - ∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)‖
      ≤ ∑ n ∈ Work.BMF.natIcc x (x + L), (H' - ww n) := by
    rw [hInt]
    have heq : (H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)
          - ∑ n ∈ Work.BMF.natIcc x (x + L), g n * (ww n : ℂ)
        = ∑ n ∈ Work.BMF.natIcc x (x + L), g n * ((H' - ww n : ℝ) : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      push_cast
      ring
    rw [heq]
    calc ‖∑ n ∈ Work.BMF.natIcc x (x + L), g n * ((H' - ww n : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Work.BMF.natIcc x (x + L), ‖g n * ((H' - ww n : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Work.BMF.natIcc x (x + L), ‖g n‖ * |H' - ww n| := by
            apply Finset.sum_congr rfl; intro n hn
            rw [norm_mul]
            simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ n ∈ Work.BMF.natIcc x (x + L), (H' - ww n) := by
            apply Finset.sum_le_sum; intro n hn
            have hnn : 0 ≤ H' - ww n := by linarith [hww_le n]
            calc ‖g n‖ * |H' - ww n| ≤ 1 * |H' - ww n| :=
                  mul_le_mul_of_nonneg_right (hg n) (abs_nonneg _)
              _ = |H' - ww n| := one_mul _
              _ = H' - ww n := abs_of_nonneg hnn
  have hHBnorm : ‖(H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)‖
      = H' * ‖∑ n ∈ Work.BMF.natIcc x (x + L), g n‖ := by
    rw [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH']
  have htri : ‖(H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)‖
      ≤ ‖(H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)
          - ∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)‖
        + ‖∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)‖ := by
    have := norm_add_le
      ((H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)
        - ∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n))
      (∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n))
    simpa [sub_add_cancel] using this
  have hint_norm : ‖∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)‖
      ≤ ∫ y in x..R, ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ :=
    intervalIntegral.norm_integral_le_integral_norm hxR
  have hfin : H' * ‖∑ n ∈ Work.BMF.natIcc x (x + L), g n‖
      ≤ 4 * H' * ((⌊H'⌋₊ : ℝ) + 1)
        + ∫ y in x..R, ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ := by
    calc H' * ‖∑ n ∈ Work.BMF.natIcc x (x + L), g n‖
        = ‖(H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)‖ := hHBnorm.symm
      _ ≤ ‖(H' : ℂ) * (∑ n ∈ Work.BMF.natIcc x (x + L), g n)
            - ∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)‖
          + ‖∫ y in x..R, (∑ n ∈ Work.BMF.natIcc y (y + H'), g n)‖ := htri
      _ ≤ (∑ n ∈ Work.BMF.natIcc x (x + L), (H' - ww n))
          + ∫ y in x..R, ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ := add_le_add hkey hint_norm
      _ ≤ 4 * H' * ((⌊H'⌋₊ : ℝ) + 1)
          + ∫ y in x..R, ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ := add_le_add hdef le_rfl
  linarith [hfin]

end Work.N8
