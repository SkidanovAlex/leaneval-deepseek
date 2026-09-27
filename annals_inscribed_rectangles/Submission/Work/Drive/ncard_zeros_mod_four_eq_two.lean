import Mathlib
import Submission.Work.Drive.parity_tools_defs

/-!
# Zeros of an antisymmetric periodic function: the `2 mod 4` parity

This file proves the analytic core of "two essential loops of `ℝP²` meet an odd number of times"
(`CHAIN_ROUTE_REDUCTION.md` §4) and of the oddness inputs of Hugelmeyer's Lemma 2:

> a continuous `f : ℝ → ℝ` with `f (t + 1) = f t` and `f (t + 1/2) = - f t`, whose zeros in `[0,1)`
> are finite and all sign changes, has a number of zeros congruent to `2` modulo `4`.

The mechanism is one-dimensional and uses only the intermediate value theorem: the zeros pair up under
`t ↦ t + 1/2`, and on each half of the period the sign goes from `f t₀` to `-f t₀`, so each half
contains an odd number of sign changes, i.e. of zeros (`hsc`).
-/

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1200000 in
noncomputable section

/-! ## Analytic preliminaries -/

/-- A continuous function on an interval whose endpoint values have opposite signs has a zero. -/
lemma exists_zero_of_opposite_signs {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (h : (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a)) :
    ∃ t ∈ Set.Icc a b, f t = 0 := by
  rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · have hmem : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
    obtain ⟨t, ht, hft⟩ := (intermediate_value_Icc hab hf) hmem
    exact ⟨t, ht, hft⟩
  · have hmem : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨le_of_lt hb, le_of_lt ha⟩
    obtain ⟨t, ht, hft⟩ := (intermediate_value_Icc' hab hf) hmem
    exact ⟨t, ht, hft⟩

/-- A continuous function with no zero on an interval has the same sign at the two ends. -/
lemma pos_iff_pos_of_no_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : ∀ t ∈ Set.Icc a b, f t ≠ 0) :
    (0 < f a ↔ 0 < f b) := by
  constructor
  · intro ha
    by_contra hb
    have hb' : f b < 0 := lt_of_le_of_ne (le_of_not_gt hb) (h b ⟨hab, le_rfl⟩)
    obtain ⟨t, ht, htz⟩ := exists_zero_of_opposite_signs hab hf (Or.inr ⟨hb', ha⟩)
    exact h t ht htz
  · intro hb
    by_contra ha
    have ha' : f a < 0 := lt_of_le_of_ne (le_of_not_gt ha) (h a ⟨le_rfl, hab⟩)
    obtain ⟨t, ht, htz⟩ := exists_zero_of_opposite_signs hab hf (Or.inl ⟨ha', hb⟩)
    exact h t ht htz

/-! ## The parity of the number of zeros on an interval -/

/-- **Uniform interface of a sign change.**  At a sign change of `f` there is `ε > 0` such that `f`
has no zero on either side of the zero and takes values of strictly opposite sign on the two sides. -/
lemma exists_signChange_data {f : ℝ → ℝ} {z : ℝ} (h : SignChangeAt f z) :
    ∃ ε > 0, (∀ s, z - ε < s → s < z → f s ≠ 0) ∧
      (∀ t, z < t → t < z + ε → f t ≠ 0) ∧
      (∀ s t, z - ε < s → s < z → z < t → t < z + ε → ¬((0 < f s) ↔ (0 < f t))) := by
  rcases h with ⟨ε, hε, hl, hr⟩ | ⟨ε, hε, hl, hr⟩
  · refine ⟨ε, hε, fun s h1 h2 => ne_of_lt (hl s h1 h2), fun t h1 h2 => ne_of_gt (hr t h1 h2),
      fun s t h1 h2 h3 h4 hiff => ?_⟩
    have hs : f s < 0 := hl s h1 h2
    have ht : 0 < f t := hr t h3 h4
    have : 0 < f s := hiff.mpr ht
    linarith
  · refine ⟨ε, hε, fun s h1 h2 => ne_of_gt (hl s h1 h2), fun t h1 h2 => ne_of_lt (hr t h1 h2),
      fun s t h1 h2 h3 h4 hiff => ?_⟩
    have hs : 0 < f s := hl s h1 h2
    have ht : f t < 0 := hr t h3 h4
    have : 0 < f t := hiff.mp hs
    linarith

/-- Propositional core of the step from `f a` to `f zL`: if `A ↔ B` is false then `A ↔ C` is the
negation of `B ↔ C`. -/
lemma iff_iff_not_iff {A B C : Prop} (h : ¬(A ↔ B)) : (A ↔ C) ↔ ¬(B ↔ C) := by
  by_cases h1 : A <;> by_cases h2 : B <;> by_cases h3 : C <;> simp_all

/-- **Parity of the number of zeros on an interval.**  For a continuous `f : ℝ → ℝ` with `f a ≠ 0`,
`f b ≠ 0`, finitely many zeros on `[a,b]`, all of them sign changes, the number of zeros is even
exactly when `f a` and `f b` have the same sign.  (Strong induction on the number of zeros, peeling off
the first one.) -/
theorem even_ncard_zeros_iff {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hfin : ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).Finite)
    (hsc : ∀ t ∈ Set.Icc a b, f t = 0 → SignChangeAt f t)
    (ha : f a ≠ 0) (hb : f b ≠ 0) :
    ((0 < f a ↔ 0 < f b) ↔ Even ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).ncard) := by
  classical
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b → ContinuousOn f (Set.Icc a b) →
      ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).Finite →
      (∀ t ∈ Set.Icc a b, f t = 0 → SignChangeAt f t) → f a ≠ 0 → f b ≠ 0 →
      ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).ncard ≤ n →
      ((0 < f a ↔ 0 < f b) ↔ Even ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).ncard) from
    H _ a b hab hf hfin hsc ha hb (le_refl _)
  intro n
  induction n with
  | zero =>
    intro a b hab hf hfin hsc ha hb hle
    have hemp : ({t ∈ Set.Icc a b | f t = 0} : Set ℝ) = ∅ := by
      by_contra hne
      have hpos : 0 < ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).ncard :=
        (Set.ncard_pos hfin).mpr (Set.nonempty_iff_ne_empty.mpr hne)
      omega
    have hno : ∀ t ∈ Set.Icc a b, f t ≠ 0 := by
      intro t ht htz
      have hmem : t ∈ ({t ∈ Set.Icc a b | f t = 0} : Set ℝ) := ⟨ht, htz⟩
      rw [hemp] at hmem
      exact hmem
    rw [hemp, Set.ncard_empty]
    exact ⟨fun _ => ⟨0, rfl⟩, fun _ => pos_iff_pos_of_no_zero hab hf hno⟩
  | succ n ih =>
    intro a b hab hf hfin hsc ha hb hle
    by_cases hemp : ({t ∈ Set.Icc a b | f t = 0} : Set ℝ) = ∅
    · have hno : ∀ t ∈ Set.Icc a b, f t ≠ 0 := by
        intro t ht htz
        have hmem : t ∈ ({t ∈ Set.Icc a b | f t = 0} : Set ℝ) := ⟨ht, htz⟩
        rw [hemp] at hmem
        exact hmem
      rw [hemp, Set.ncard_empty]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => pos_iff_pos_of_no_zero hab hf hno⟩
    · -- the first zero of `f` on `[a,b]`
      obtain ⟨z, hzS, hzmin⟩ : ∃ z, z ∈ ({t ∈ Set.Icc a b | f t = 0} : Set ℝ) ∧
          ∀ t ∈ ({t ∈ Set.Icc a b | f t = 0} : Set ℝ), z ≤ t := by
        have hneF : hfin.toFinset.Nonempty := by
          rw [Set.Finite.toFinset_nonempty]
          exact Set.nonempty_iff_ne_empty.mpr hemp
        refine ⟨hfin.toFinset.min' hneF, ?_, ?_⟩
        · rw [← Set.Finite.mem_toFinset]
          exact Finset.min'_mem _ hneF
        · intro t ht
          exact Finset.min'_le _ _ ((Set.Finite.mem_toFinset hfin).mpr ht)
      have hzmem : z ∈ Set.Icc a b := hzS.1
      have hfz : f z = 0 := hzS.2
      have haz : a < z := lt_of_le_of_ne hzmem.1 (by rintro rfl; exact ha hfz)
      have hzb : z < b := lt_of_le_of_ne hzmem.2 (by rintro rfl; exact hb hfz)
      obtain ⟨ε, hε, hLne, hRne, hLR⟩ := exists_signChange_data (hsc z hzmem hfz)
      -- a point `zL` just left of `z` (and `≥ a`), and a point `z'` just right of `z` (and `< b`)
      obtain ⟨zL, hazL, hzLlt, hzLclose⟩ : ∃ zL, a ≤ zL ∧ zL < z ∧ z - ε < zL :=
        ⟨max a (z - ε / 2), le_max_left _ _, max_lt haz (by linarith),
          lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
      obtain ⟨z', hz'gt, hz'ltb, hz'close⟩ : ∃ z', z < z' ∧ z' < b ∧ z' < z + ε := by
        refine ⟨z + min ε (b - z) / 2, ?_, ?_, ?_⟩
        · have := lt_min hε (by linarith : 0 < b - z); linarith
        · have := min_le_right ε (b - z); linarith
        · have := min_le_left ε (b - z); linarith
      have hLne' : f zL ≠ 0 := hLne zL hzLclose hzLlt
      have hRne' : f z' ≠ 0 := hRne z' hz'gt hz'close
      have hLR' : ¬((0 < f zL) ↔ (0 < f z')) := hLR zL z' hzLclose hzLlt hz'gt hz'close
      -- the zero set on `[a,b]` is `{z}` together with the zero set on `[z',b]`
      have hSsplit : ({t ∈ Set.Icc a b | f t = 0} : Set ℝ)
          = insert z ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ) := by
        ext t
        constructor
        · rintro ⟨ht, htz⟩
          have ht' : a ≤ t ∧ t ≤ b := ht
          by_cases htz' : t ≤ z'
          · have hzt : z ≤ t := hzmin t ⟨ht, htz⟩
            rcases lt_or_eq_of_le hzt with hlt | heq
            · exact absurd htz (hRne t hlt (lt_of_le_of_lt htz' hz'close))
            · exact Set.mem_insert_iff.mpr (Or.inl heq.symm)
          · exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨le_of_not_ge htz', ht'.2⟩, htz⟩)
        · intro ht
          rcases Set.mem_insert_iff.mp ht with h | h
          · exact h.symm ▸ hzS
          · obtain ⟨⟨hz't, htb⟩, hft⟩ := h
            exact ⟨⟨le_trans haz.le (le_trans hz'gt.le hz't), htb⟩, hft⟩
      have hsub' : ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ) ⊆
          ({t ∈ Set.Icc a b | f t = 0} : Set ℝ) := by
        intro t ht
        obtain ⟨⟨hz't, htb⟩, hft⟩ := ht
        exact ⟨⟨le_trans haz.le (le_trans hz'gt.le hz't), htb⟩, hft⟩
      have hfin' : ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ).Finite := hfin.subset hsub'
      have hznotmem : z ∉ ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ) :=
        fun h => absurd h.1.1 (not_le.mpr hz'gt)
      have hcard : ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).ncard
          = 1 + ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ).ncard := by
        rw [hSsplit, Set.ncard_insert_of_notMem hznotmem hfin', Nat.add_comm]
      have hno_left : ∀ s ∈ Set.Icc a zL, f s ≠ 0 := by
        intro s hs hsz
        have hsS : s ∈ ({t ∈ Set.Icc a b | f t = 0} : Set ℝ) :=
          ⟨⟨hs.1, le_trans hs.2 (le_trans hzLlt.le hzmem.2)⟩, hsz⟩
        exact absurd (hzmin s hsS) (not_le.mpr (lt_of_le_of_lt hs.2 hzLlt))
      have hle' : ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ).ncard ≤ n := by
        have h1 : ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ).ncard + 1
            = ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).ncard := by
          rw [hcard, Nat.add_comm]
        omega
      have hih := ih z' b hz'ltb.le
        (hf.mono (Set.Icc_subset_Icc_left (le_trans haz.le hz'gt.le))) hfin'
        (fun t (ht : t ∈ Set.Icc z' b) => by
          have ht' : a ≤ t := le_trans haz.le (le_trans hz'gt.le ht.1)
          exact fun hft => hsc t ⟨ht', ht.2⟩ hft) hRne' hb hle'
      have hAB : (0 < f a) ↔ (0 < f zL) :=
        pos_iff_pos_of_no_zero hazL
          (hf.mono (Set.Icc_subset_Icc_right (le_trans hzLlt.le hzmem.2))) hno_left
      have hB : (0 < f a ↔ 0 < f b) ↔ (0 < f zL ↔ 0 < f b) :=
        ⟨fun h => hAB.symm.trans h, fun h => hAB.trans h⟩
      have hC : (0 < f zL ↔ 0 < f b) ↔ ¬(0 < f z' ↔ 0 < f b) :=
        iff_iff_not_iff hLR'

      have hD : ¬(0 < f z' ↔ 0 < f b) ↔ ¬Even ({t ∈ Set.Icc z' b | f t = 0} : Set ℝ).ncard := by
        rw [hih]
      rw [hcard, Nat.add_comm, Nat.even_add_one]
      exact hB.trans (hC.trans hD)

/-- The odd case: opposite signs at the ends force an odd number of zeros. -/
theorem odd_ncard_zeros_of_opposite_signs {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hfin : ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).Finite)
    (hsc : ∀ t ∈ Set.Icc a b, f t = 0 → SignChangeAt f t)
    (ha : f a ≠ 0) (hb : f b ≠ 0)
    (hsign : (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a)) :
    Odd ({t ∈ Set.Icc a b | f t = 0} : Set ℝ).ncard := by
  have hiff := even_ncard_zeros_iff hab hf hfin hsc ha hb
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hsame : (0 < f a ↔ 0 < f b) := hiff.mpr heven
  rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : ¬(0 < f a) := by linarith
    exact this (hsame.mpr h2)
  · have : ¬(0 < f b) := by linarith
    exact this (hsame.mp h2)

/-- **The number of zeros of an antisymmetric periodic function is `2` modulo `4`.** -/
theorem ncard_zeros_mod_four_eq_two (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ t, f (t + 1) = f t) (hanti : ∀ t, f (t + 1 / 2) = - f t)
    (hfin : {t ∈ Set.Ico (0 : ℝ) 1 | f t = 0}.Finite)
    (hsc : ∀ t, f t = 0 → SignChangeAt f t) :
    {t ∈ Set.Ico (0 : ℝ) 1 | f t = 0}.ncard % 4 = 2 := by
  classical
  -- a base point `t₀ ∈ [0, 1/2)` with `f t₀ ≠ 0`
  have ht0 : ∃ t₀ ∈ Set.Ico (0 : ℝ) (1 / 2), f t₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : f 0 = 0 := hcon 0 ⟨le_rfl, by norm_num⟩
    rcases hsc 0 h0 with ⟨ε, hε, hl, hr⟩ | ⟨ε, hε, hl, hr⟩ <;>
      · have hs0 : 0 < min ε (1 / 2) / 2 := by
          have := lt_min hε (by norm_num : (0 : ℝ) < 1 / 2); linarith
        have hse : min ε (1 / 2) / 2 < ε := by
          have := min_le_left ε (1 / 2); linarith
        have hs2 : min ε (1 / 2) / 2 < 1 / 2 := by
          have := min_le_right ε (1 / 2); linarith
        have hne := hr _ hs0 (by linarith : min ε (1 / 2) / 2 < 0 + ε)
        have hz := hcon _ ⟨le_of_lt hs0, hs2⟩
        linarith
  obtain ⟨t₀, ht0mem, ht0ne⟩ := ht0
  obtain ⟨ht0nn, ht0lt⟩ := ht0mem
  -- the odd count on the interval `[t₀, t₀ + 1/2]`
  have hC : Odd ({t ∈ Set.Icc t₀ (t₀ + 1 / 2) | f t = 0} : Set ℝ).ncard := by
    refine odd_ncard_zeros_of_opposite_signs (by linarith) hf.continuousOn ?_ ?_ ht0ne ?_ ?_
    · refine hfin.subset ?_
      intro t ht
      obtain ⟨⟨ht1, ht2⟩, htz⟩ := ht
      exact ⟨⟨le_trans ht0nn ht1, by linarith⟩, htz⟩
    · intro t _ htz
      exact hsc t htz
    · rw [hanti t₀]; exact neg_ne_zero.mpr ht0ne
    · rw [hanti t₀]
      rcases lt_or_gt_of_ne ht0ne with h | h
      · exact Or.inl ⟨h, by linarith⟩
      · exact Or.inr ⟨by linarith, h⟩
  -- the two halves of the period
  have hZsplit : ({t ∈ Set.Ico (0 : ℝ) 1 | f t = 0} : Set ℝ)
      = ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ)
        ∪ ({t ∈ Set.Ico (1 / 2) 1 | f t = 0} : Set ℝ) := by
    ext t; constructor
    · rintro ⟨ht, htz⟩
      by_cases h : t < 1 / 2
      · exact Or.inl ⟨⟨ht.1, h⟩, htz⟩
      · exact Or.inr ⟨⟨le_of_not_gt h, ht.2⟩, htz⟩
    · rintro (⟨ht, htz⟩ | ⟨ht, htz⟩)
      · exact ⟨⟨ht.1, by linarith [ht.2]⟩, htz⟩
      · exact ⟨⟨by linarith [ht.1], ht.2⟩, htz⟩
  have hdisjZ : Disjoint ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ)
      ({t ∈ Set.Ico (1 / 2) 1 | f t = 0} : Set ℝ) := by
    rw [Set.disjoint_left]
    rintro t ⟨⟨-, h1⟩, -⟩ ⟨⟨h2, -⟩, -⟩
    exact absurd h2 (not_le.mpr h1)
  have hfinZ1 : ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ).Finite :=
    hfin.subset (fun t ht => ⟨⟨ht.1.1, by linarith [ht.1.2]⟩, ht.2⟩)
  have hfinZ2 : ({t ∈ Set.Ico (1 / 2) 1 | f t = 0} : Set ℝ).Finite :=
    hfin.subset (fun t ht => ⟨⟨by linarith [ht.1.1], ht.1.2⟩, ht.2⟩)
  have hZcard : ({t ∈ Set.Ico (0 : ℝ) 1 | f t = 0} : Set ℝ).ncard
      = ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ).ncard
        + ({t ∈ Set.Ico (1 / 2) 1 | f t = 0} : Set ℝ).ncard := by
    rw [hZsplit, Set.ncard_union_eq hdisjZ hfinZ1 hfinZ2]
  -- the two halves have the same number of zeros
  have hshift : ({t ∈ Set.Ico (1 / 2) 1 | f t = 0} : Set ℝ).ncard
      = ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ).ncard := by
    have himg : (fun t : ℝ => t + 1 / 2) '' ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ)
        = ({t ∈ Set.Ico (1 / 2) 1 | f t = 0} : Set ℝ) := by
      ext u; constructor
      · rintro ⟨t, ⟨⟨ht1, ht2⟩, htz⟩, rfl⟩
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [hanti, htz]; ring
      · rintro ⟨⟨hu1, hu2⟩, huz⟩
        refine ⟨u - 1 / 2, ⟨⟨by linarith, by linarith⟩, ?_⟩, by ring⟩
        have h1 : f (u - 1 / 2 + 1 / 2) = - f (u - 1 / 2) := hanti (u - 1 / 2)
        rw [show u - 1 / 2 + 1 / 2 = u by ring, huz] at h1
        linarith
    rw [← himg, Set.ncard_image_of_injective _ (fun a b h => by linarith)]
  -- the first half, split at `t₀` and at `1/2`
  have hZ1split : ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ)
      = ({t ∈ Set.Ico (0 : ℝ) t₀ | f t = 0} : Set ℝ)
        ∪ ({t ∈ Set.Ico t₀ (1 / 2) | f t = 0} : Set ℝ) := by
    ext t; constructor
    · rintro ⟨ht, htz⟩
      by_cases h : t < t₀
      · exact Or.inl ⟨⟨ht.1, h⟩, htz⟩
      · exact Or.inr ⟨⟨le_of_not_gt h, ht.2⟩, htz⟩
    · rintro (⟨ht, htz⟩ | ⟨ht, htz⟩)
      · exact ⟨⟨ht.1, by linarith [ht.2, ht0lt]⟩, htz⟩
      · exact ⟨⟨by linarith [ht.1], ht.2⟩, htz⟩
  have hdisjAB : Disjoint ({t ∈ Set.Ico (0 : ℝ) t₀ | f t = 0} : Set ℝ)
      ({t ∈ Set.Ico t₀ (1 / 2) | f t = 0} : Set ℝ) := by
    rw [Set.disjoint_left]
    rintro t ⟨⟨-, h1⟩, -⟩ ⟨⟨h2, -⟩, -⟩
    exact absurd h2 (not_le.mpr h1)
  have hDsplit : ({t ∈ Set.Icc t₀ (t₀ + 1 / 2) | f t = 0} : Set ℝ)
      = ({t ∈ Set.Ico t₀ (1 / 2) | f t = 0} : Set ℝ)
        ∪ ({t ∈ Set.Ico (1 / 2) (t₀ + 1 / 2) | f t = 0} : Set ℝ) := by
    ext t; constructor
    · rintro ⟨⟨ht1, ht2⟩, htz⟩
      by_cases h : t < 1 / 2
      · exact Or.inl ⟨⟨ht1, h⟩, htz⟩
      · refine Or.inr ⟨⟨le_of_not_gt h, ?_⟩, htz⟩
        refine lt_of_le_of_ne ht2 ?_
        rintro rfl
        rw [hanti t₀] at htz
        exact ht0ne (by linarith)
    · rintro (⟨ht, htz⟩ | ⟨ht, htz⟩)
      · exact ⟨⟨ht.1, by linarith [ht.2]⟩, htz⟩
      · exact ⟨⟨by linarith [ht.1, ht0lt], le_of_lt ht.2⟩, htz⟩
  have hdisjBE : Disjoint ({t ∈ Set.Ico t₀ (1 / 2) | f t = 0} : Set ℝ)
      ({t ∈ Set.Ico (1 / 2) (t₀ + 1 / 2) | f t = 0} : Set ℝ) := by
    rw [Set.disjoint_left]
    rintro t ⟨⟨-, h1⟩, -⟩ ⟨⟨h2, -⟩, -⟩
    exact absurd h2 (not_le.mpr h1)
  have hfinA : ({t ∈ Set.Ico (0 : ℝ) t₀ | f t = 0} : Set ℝ).Finite :=
    hfin.subset (fun t ht => ⟨⟨ht.1.1, by linarith [ht.1.2, ht0lt]⟩, ht.2⟩)
  have hfinB : ({t ∈ Set.Ico t₀ (1 / 2) | f t = 0} : Set ℝ).Finite :=
    hfin.subset (fun t ht => ⟨⟨by linarith [ht.1.1, ht0nn], by linarith [ht.1.2]⟩, ht.2⟩)
  have hfinE : ({t ∈ Set.Ico (1 / 2) (t₀ + 1 / 2) | f t = 0} : Set ℝ).Finite :=
    hfin.subset (fun t ht => ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2, ht0lt]⟩, ht.2⟩)
  have hfinD : ({t ∈ Set.Icc t₀ (t₀ + 1 / 2) | f t = 0} : Set ℝ).Finite :=
    hfin.subset (fun t ht => ⟨⟨by linarith [ht.1.1, ht0nn], by linarith [ht.1.2, ht0lt]⟩, ht.2⟩)
  -- the outer pieces have the same number of zeros
  have hAE : ({t ∈ Set.Ico (0 : ℝ) t₀ | f t = 0} : Set ℝ).ncard
      = ({t ∈ Set.Ico (1 / 2) (t₀ + 1 / 2) | f t = 0} : Set ℝ).ncard := by
    have himg : (fun t : ℝ => t + 1 / 2) '' ({t ∈ Set.Ico (0 : ℝ) t₀ | f t = 0} : Set ℝ)
        = ({t ∈ Set.Ico (1 / 2) (t₀ + 1 / 2) | f t = 0} : Set ℝ) := by
      ext u; constructor
      · rintro ⟨t, ⟨⟨ht1, ht2⟩, htz⟩, rfl⟩
        exact ⟨⟨by linarith, by linarith⟩, by rw [hanti, htz]; ring⟩
      · rintro ⟨⟨hu1, hu2⟩, huz⟩
        refine ⟨u - 1 / 2, ⟨⟨by linarith, by linarith⟩, ?_⟩, by ring⟩
        have h1 : f (u - 1 / 2 + 1 / 2) = - f (u - 1 / 2) := hanti (u - 1 / 2)
        rw [show u - 1 / 2 + 1 / 2 = u by ring, huz] at h1
        linarith
    rw [← himg, Set.ncard_image_of_injective _ (fun a b h => by linarith)]
  have hZ1 : ({t ∈ Set.Ico (0 : ℝ) (1 / 2) | f t = 0} : Set ℝ).ncard
      = ({t ∈ Set.Ico (0 : ℝ) t₀ | f t = 0} : Set ℝ).ncard
        + ({t ∈ Set.Ico t₀ (1 / 2) | f t = 0} : Set ℝ).ncard := by
    rw [hZ1split, Set.ncard_union_eq hdisjAB hfinA hfinB]
  have hD : ({t ∈ Set.Icc t₀ (t₀ + 1 / 2) | f t = 0} : Set ℝ).ncard
      = ({t ∈ Set.Ico t₀ (1 / 2) | f t = 0} : Set ℝ).ncard
        + ({t ∈ Set.Ico (1 / 2) (t₀ + 1 / 2) | f t = 0} : Set ℝ).ncard := by
    rw [hDsplit, Set.ncard_union_eq hdisjBE hfinB hfinE]
  have hfinal : ({t ∈ Set.Ico (0 : ℝ) 1 | f t = 0} : Set ℝ).ncard
      = 2 * ({t ∈ Set.Icc t₀ (t₀ + 1 / 2) | f t = 0} : Set ℝ).ncard := by
    rw [hZcard, hshift, hZ1, hD, ← hAE]
    ring
  rw [hfinal]
  obtain ⟨k, hk⟩ := hC
  omega


end

end Work.Drive
