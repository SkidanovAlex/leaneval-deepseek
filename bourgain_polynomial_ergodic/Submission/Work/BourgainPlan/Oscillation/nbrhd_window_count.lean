import Mathlib
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs

/-!
# How many scales can have their radius in a given dyadic window?

This file proves `nbrhd_window_count`, the elementary counting lemma underlying the
"half-shell correction" of Bourgain's oscillation argument for the multi-frequency
neighbourhood maximal function at an *arbitrary* antitone family of radii `ρ`.

Setting, for a finite frequency set `T`, a real `θ`, and a radius `r`,

* `W T r θ = 1` iff `θ` lies in the periodised `r`-neighbourhood of the frequencies of `T`
  (a `0/1`-valued function, see `Work.BourgainPlan.Oscillation.W`),

and given radii `ρ t` sandwiched in the dyadic window of level `jt t`,

* `2 ^ (-(jt t) - 2) < ρ t ≤ 2 ^ (-(jt t) - 1)`  (`hspec`, `hupper`),

with `ρ` antitone (`hanti`) and with the window-counting hypothesis (`hwin`)

* `ρ t ≤ 2 ^ (-j - 1) ⟹ ρ (t + M) ≤ 2 ^ (-j - 2)`,

the sum of the *squared shell indicators*
`(W T (2 ^ (-(jt t) - 1)) θ - W T (ρ t) θ) ^ 2` over `t < N` is at most `M + 1`.

Each summand is `0` or `1`; it is `1` exactly when the periodised distance `d` of `θ` to `T`
satisfies `ρ t < d ≤ 2 ^ (-(jt t) - 1)`.  Together with `hspec` this pins `d` into one
*dyadic* window `(2 ^ (-(jt t) - 2), 2 ^ (-(jt t) - 1)]`, so all contributing `t` share the
same value of `jt` (the windows are disjoint).  For a fixed level `j`, the radii lying in the
window `(2 ^ (-j - 2), 2 ^ (-j - 1)]` occupy at most `M` consecutive indices: if `a` is the
first such index then `hwin` puts `ρ (a + M)` already below `2 ^ (-j - 2)`, and antitonicity
keeps it below for all later indices.  Since the sum equals the number of contributing
indices, it is `≤ M ≤ M + 1`.

This is the "at most `M + 1` scales per dyadic window" input of `NbrhdMaximalLacunary`
(see `Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs`).
-/

namespace Work.BourgainPlan.Oscillation

open Finset

noncomputable section

/-! ## The indicator `W` as a `0/1` function -/

/-- `W T r θ = 1` exactly when `θ` lies in the periodised `r`-neighbourhood of `T`. -/
lemma W_eq_one_iff (T : Finset (ℝ × ℂ)) (r θ : ℝ) :
    W T r θ = 1 ↔ ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r := by
  rw [W]
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r <;> simp [h]

/-- `W T r θ = 0` exactly when `θ` is at periodised distance `> r` from every frequency of `T`. -/
lemma W_eq_zero_iff (T : Finset (ℝ × ℂ)) (r θ : ℝ) :
    W T r θ = 0 ↔ ∀ p ∈ T, ∀ l : ℤ, r < |θ + (l : ℝ) - p.1| := by
  constructor
  · intro h0 p hp l
    by_contra hc
    push Not at hc
    have h1 : W T r θ = 1 := (W_eq_one_iff T r θ).mpr ⟨p, hp, l, hc⟩
    rw [h0] at h1
    norm_num at h1
  · intro h0
    by_contra hc
    have h1 : W T r θ = 1 := by
      rcases W_eq_zero_or_one T r θ with h' | h'
      · exact absurd h' hc
      · exact h'
    obtain ⟨p, hp, l, hl⟩ := (W_eq_one_iff T r θ).mp h1
    have := h0 p hp l
    linarith

/-- The difference of two nested `W`-indicators takes the values `0` and `1` only. -/
lemma W_sub_eq_zero_or_one (T : Finset (ℝ × ℂ)) {r r' : ℝ} (h : r ≤ r') (θ : ℝ) :
    W T r' θ - W T r θ = 0 ∨ W T r' θ - W T r θ = 1 := by
  rcases W_eq_zero_or_one T r' θ with h' | h'
  · have hh := W_mono_zero T h θ h'
    rw [h', hh]; norm_num
  · rcases W_eq_zero_or_one T r θ with hh | hh
    · rw [h', hh]; norm_num
    · rw [h', hh]; norm_num

/-- The difference of two nested `W`-indicators equals `1` exactly on the shell where the
outer indicator is `1` and the inner one is `0`. -/
lemma W_sub_eq_one_iff (T : Finset (ℝ × ℂ)) {r r' : ℝ} (h : r ≤ r') (θ : ℝ) :
    W T r' θ - W T r θ = 1 ↔ W T r' θ = 1 ∧ W T r θ = 0 := by
  rcases W_eq_zero_or_one T r' θ with h' | h'
  · have hh := W_mono_zero T h θ h'
    rw [h', hh]; norm_num
  · rcases W_eq_zero_or_one T r θ with hh | hh
    · rw [h', hh]; norm_num
    · rw [h', hh]; norm_num

/-! ## The counting lemma -/

/-- **At most `M + 1` scales can have their radius in one "effective" dyadic window.**
For an antitone radius family `ρ` whose `t`-th term sits in the dyadic window of level
`jt t` (`2 ^ (-(jt t) - 2) < ρ t ≤ 2 ^ (-(jt t) - 1)`) and which drops by more than one
level every `M` steps (`hwin`), the total squared shell measure
`Σ_{t < N} (W T (2 ^ (-(jt t) - 1)) θ - W T (ρ t) θ) ^ 2` is at most `M + 1`. -/
theorem nbrhd_window_count (T : Finset (ℝ × ℂ)) (ρ : ℕ → ℝ) (jt : ℕ → ℕ) (M : ℕ)
    (hspec : ∀ t, (2:ℝ)^(-(jt t : ℝ)-2) < ρ t)
    (hupper : ∀ t, ρ t ≤ (2:ℝ)^(-(jt t : ℝ)-1))
    (hanti : Antitone ρ)
    (hwin : ∀ (j t : ℕ), ρ t ≤ (2:ℝ)^(-(j:ℝ)-1) → ρ (t+M) ≤ (2:ℝ)^(-(j:ℝ)-2))
    (θ : ℝ) (N : ℕ) :
    Finset.sum (Finset.range N) (fun t => (Work.BourgainPlan.Oscillation.W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - Work.BourgainPlan.Oscillation.W T (ρ t) θ) ^ 2)
      ≤ ((M:ℝ) + 1) := by
  classical
  -- each summand is `0` or `1`, and it is `1` exactly on the shell
  have hf01 : ∀ t, (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2 = 0 ∨
      (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2 = 1 := by
    intro t
    rcases W_sub_eq_zero_or_one T (hupper t) θ with h | h <;> simp [h]
  have hf1 : ∀ t, (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2 = 1 ↔
      (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ = 1 ∧ W T (ρ t) θ = 0) := by
    intro t
    have hsq : (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2 = 1 ↔
        W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ = 1 := by
      rcases W_sub_eq_zero_or_one T (hupper t) θ with h | h <;> rw [h] <;> norm_num
    rw [hsq, W_sub_eq_one_iff T (hupper t) θ]
  -- the set of contributing scales
  set S : Finset ℕ := (Finset.range N).filter
    (fun t => (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2 ≠ 0) with hS
  have hSsub : S ⊆ Finset.range N := by
    intro t ht
    rw [hS] at ht
    exact Finset.mem_of_mem_filter t ht
  have hmem : ∀ t ∈ S, (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2 = 1 := by
    intro t ht
    rcases hf01 t with h | h
    · rw [hS] at ht
      exact absurd h (Finset.mem_filter.mp ht).2
    · exact h
  have hsumS : ∑ t ∈ S, (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2 = (S.card : ℝ) := by
    rw [Finset.sum_congr rfl hmem]
    simp
  have hsum : ∑ t ∈ Finset.range N, (W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ) ^ 2
      = (S.card : ℝ) := by
    rw [← Finset.sum_subset hSsub (fun x hx hxS => ?_), hsumS]
    by_contra hne
    exact hxS (by rw [hS]; exact Finset.mem_filter.mpr ⟨hx, hne⟩)
  -- the contributing scales themselves: all share the same `jt`, and their radii lie in one
  -- dyadic window, which can hold at most `M` of them
  have hcard : S.card ≤ M := by
    by_cases hne : S.Nonempty
    · obtain ⟨t₀, ht₀⟩ := hne
      have hW1 : ∀ t ∈ S, W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ = 1 ∧ W T (ρ t) θ = 0 :=
        fun t ht => (hf1 t).mp (hmem t ht)
      -- Step 1: the shell at scale `t` forces `jt t` to be the dyadic level of the
      -- (unique) periodised distance of `θ` to `T`, hence is independent of `t`.
      have hj_eq : ∀ t ∈ S, jt t = jt t₀ := by
        intro t ht
        obtain ⟨ha, hb⟩ := hW1 t ht
        obtain ⟨ha₀, hb₀⟩ := hW1 t₀ ht₀
        rcases lt_trichotomy (jt t) (jt t₀) with h | h | h
        · exfalso
          obtain ⟨p, hp, l, hl⟩ := (W_eq_one_iff T ((2:ℝ)^(-(jt t₀ : ℝ)-1)) θ).mp ha₀
          have hgt := (W_eq_zero_iff T (ρ t) θ).mp hb p hp l
          have hspec_t := hspec t
          have hmono : (2:ℝ)^(-(jt t₀ : ℝ) - 1) ≤ (2:ℝ)^(-(jt t : ℝ) - 2) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
            have : (jt t : ℝ) + 1 ≤ (jt t₀ : ℝ) := by exact_mod_cast h
            linarith
          linarith
        · exact h
        · exfalso
          obtain ⟨p, hp, l, hl⟩ := (W_eq_one_iff T ((2:ℝ)^(-(jt t : ℝ)-1)) θ).mp ha
          have hgt := (W_eq_zero_iff T (ρ t₀) θ).mp hb₀ p hp l
          have hspec_t₀ := hspec t₀
          have hmono : (2:ℝ)^(-(jt t : ℝ) - 1) ≤ (2:ℝ)^(-(jt t₀ : ℝ) - 2) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
            have : (jt t₀ : ℝ) + 1 ≤ (jt t : ℝ) := by exact_mod_cast h
            linarith
          linarith
      set j := jt t₀ with hj
      have hSwin : ∀ t ∈ S, (2:ℝ)^(-(j:ℝ)-2) < ρ t ∧ ρ t ≤ (2:ℝ)^(-(j:ℝ)-1) := by
        intro t ht
        have hje : jt t = j := by rw [hj]; exact hj_eq t ht
        have h : (2:ℝ)^(-(jt t : ℝ)-2) < ρ t ∧ ρ t ≤ (2:ℝ)^(-(jt t : ℝ)-1) :=
          ⟨hspec t, hupper t⟩
        rw [hje] at h
        exact h
      -- Step 2: a dyadic window contains at most `M` indices of an antitone `ρ` satisfying
      -- `hwin`, because `M` steps after its first index the window is already left behind.
      have hJne : (Set.Nonempty {t : ℕ | (2:ℝ)^(-(j:ℝ)-2) < ρ t ∧ ρ t ≤ (2:ℝ)^(-(j:ℝ)-1)}) :=
        ⟨t₀, hSwin t₀ ht₀⟩
      set a := sInf ({t : ℕ | (2:ℝ)^(-(j:ℝ)-2) < ρ t ∧ ρ t ≤ (2:ℝ)^(-(j:ℝ)-1)} : Set ℕ) with ha_def
      have ha_mem : a ∈ {t : ℕ | (2:ℝ)^(-(j:ℝ)-2) < ρ t ∧ ρ t ≤ (2:ℝ)^(-(j:ℝ)-1)} := by
        rw [ha_def]; exact Nat.sInf_mem hJne
      have hsub : S ⊆ Finset.Ico a (a+M) := by
        intro t ht
        have htJ := hSwin t ht
        have hge : a ≤ t := by rw [ha_def]; exact Nat.sInf_le htJ
        have hlt : t < a + M := by
          by_contra hc
          push Not at hc
          have h1 : ρ t ≤ (2:ℝ)^(-(j:ℝ)-2) := le_trans (hanti hc) (hwin j a ha_mem.2)
          linarith [htJ.1]
        exact Finset.mem_Ico.mpr ⟨hge, hlt⟩
      have hle : S.card ≤ (Finset.Ico a (a+M)).card := Finset.card_le_card hsub
      simpa using hle
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      exact Nat.zero_le M
  rw [hsum]
  have hcast : (S.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcard
  linarith

end

end Work.BourgainPlan.Oscillation
