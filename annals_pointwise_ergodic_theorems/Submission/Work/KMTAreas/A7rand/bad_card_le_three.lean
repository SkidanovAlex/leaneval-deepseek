import Mathlib

namespace Work.KMTAreas.A7rand

/-- Counting lemma for the "bad" set of scales.

Let `s : ℕ → ℕ` be monotone and `ξ : ℝ`.  An index `m` is *bad* when the
scale `s` strictly increases at `m` and the dyadic weight `2 ^ (s m) * |ξ|`
crosses the level `1`: `2 ^ (s m) * |ξ| ≤ 1` while `2 ^ (s (m+1)) * |ξ| ≥ 1/2`.

Since `s` is monotone, the weights `A m = 2 ^ (s m) * |ξ|` are nondecreasing
and, whenever `s` strictly increases at `m`, `A (m+1) ≥ 2 * A m`.  So the bad
indices are exactly the indices at which the geometric sequence of weights
"jumps over" the level `1`; there can be at most three of them.

(That three is optimal: with `|ξ| = 1/4` and `s m = m` the indices `0, 1, 2`
are all bad.) -/
theorem bad_card_le_three (N : ℕ) (s : ℕ → ℕ) (hs : Monotone s) (ξ : ℝ) :
    ((Finset.range N).filter (fun m : ℕ =>
        s (m + 1) > s m ∧ (2 : ℝ) ^ (s m) * |ξ| ≤ 1 ∧
          (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|)).card ≤ 3 := by
  classical
  let T : Finset ℕ := (Finset.range N).filter (fun m : ℕ =>
        s (m + 1) > s m ∧ (2 : ℝ) ^ (s m) * |ξ| ≤ 1 ∧
          (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|)
  change T.card ≤ 3
  let A : ℕ → ℝ := fun m => (2 : ℝ) ^ (s m) * |ξ|
  have hAm : Monotone A := by
    intro m n hmn
    simp only [A]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hs hmn)) (abs_nonneg ξ)
  have memA : ∀ m ∈ T, s (m + 1) > s m ∧ A m ≤ 1 ∧ (1 : ℝ) / 2 ≤ A (m + 1) := by
    intro m hm
    simp only [T, Finset.mem_filter] at hm
    exact hm.2
  have hstep : ∀ m, s (m + 1) > s m → 2 * A m ≤ A (m + 1) := by
    intro m h
    have hs' : s m + 1 ≤ s (m + 1) := Nat.succ_le_of_lt h
    have hpow : (2 : ℝ) ^ (s m + 1) ≤ (2 : ℝ) ^ (s (m + 1)) :=
      pow_le_pow_right₀ (by norm_num) hs'
    have hpow2 : (2 : ℝ) ^ (s m + 1) = 2 * (2 : ℝ) ^ (s m) := by rw [pow_succ']
    have hle : 2 * (2 : ℝ) ^ (s m) ≤ (2 : ℝ) ^ (s (m + 1)) := hpow2 ▸ hpow
    calc 2 * A m = (2 * (2 : ℝ) ^ (s m)) * |ξ| := by simp only [A]; ring
      _ ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ| := mul_le_mul_of_nonneg_right hle (abs_nonneg ξ)
      _ = A (m + 1) := by simp only [A]
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT]; simp
  · set m0 := T.min' hT with hm0def
    have hm0mem : m0 ∈ T := Finset.min'_mem T hT
    have hm0le : ∀ m ∈ T, m0 ≤ m := fun m hm => Finset.min'_le T m hm
    have hA_lower : ∀ m ∈ T, m ≠ m0 → (1 : ℝ) / 2 ≤ A m := by
      intro m hm hne
      have hm0lt : m0 < m := lt_of_le_of_ne (hm0le m hm) (Ne.symm hne)
      have h1 : A (m0 + 1) ≤ A m := hAm (Nat.succ_le_of_lt hm0lt)
      exact le_trans (memA m0 hm0mem).2.2 h1
    have hA_upper : ∀ m ∈ T, A m ≤ 1 := fun m hm => (memA m hm).2.1
    have hs_lt : ∀ a ∈ T, ∀ b ∈ T, a < b → s a < s b := by
      intro a ha b hb hab
      have h1 : s a < s (a + 1) := (memA a ha).1
      have h2 : s (a + 1) ≤ s b := hs (Nat.succ_le_of_lt hab)
      omega
    have hs_inj : Set.InjOn s (↑T : Set ℕ) := by
      intro a ha b hb hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (ne_of_lt (hs_lt a ha b hb h))
      · exact h
      · exact absurd hab.symm (ne_of_lt (hs_lt b hb a ha h))
    rcases (T.erase m0).eq_empty_or_nonempty with hemp | hne'
    · have hcardT : T.card = 1 := by
        have hh := Finset.card_erase_add_one hm0mem
        rw [hemp] at hh
        simp at hh
        omega
      omega
    · set m1 := (T.erase m0).min' hne' with hm1def
      have hm1mem' : m1 ∈ T.erase m0 := Finset.min'_mem _ hne'
      have hm1mem : m1 ∈ T := (Finset.mem_erase.mp hm1mem').2
      have hm1ne : m1 ≠ m0 := (Finset.mem_erase.mp hm1mem').1
      have hm1le : ∀ m ∈ T.erase m0, m1 ≤ m := fun m hm => Finset.min'_le _ m hm
      have hsub : (T.erase m0).image s ⊆ ({s m1, s m1 + 1} : Finset ℕ) := by
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨m, hm, rfl⟩ := hk
        have hmT : m ∈ T := (Finset.mem_erase.mp hm).2
        have hmne : m ≠ m0 := (Finset.mem_erase.mp hm).1
        have hm_up : A m ≤ 1 := hA_upper m hmT
        have hm1_low : (1 : ℝ) / 2 ≤ A m1 := hA_lower m1 hm1mem hm1ne
        have hsm_ge : s m1 ≤ s m := hs (hm1le m hm)
        have hpow : (2 : ℝ) ^ (s m) = (2 : ℝ) ^ (s m - s m1) * (2 : ℝ) ^ (s m1) := by
          rw [← pow_add, Nat.sub_add_cancel hsm_ge]
        have hAeq : A m = (2 : ℝ) ^ (s m - s m1) * A m1 := by
          simp only [A]; rw [hpow]; ring
        have hj2 : (2 : ℝ) ^ (s m - s m1) * (1 / 2) ≤ 1 := by
          calc (2 : ℝ) ^ (s m - s m1) * (1 / 2)
              ≤ (2 : ℝ) ^ (s m - s m1) * A m1 := by
                apply mul_le_mul_of_nonneg_left hm1_low; positivity
            _ = A m := hAeq.symm
            _ ≤ 1 := hm_up
        have hratio : (2 : ℝ) ^ (s m - s m1) ≤ 2 := by linarith
        have hratio' : (2 : ℝ) ^ (s m - s m1) ≤ (2 : ℝ) ^ 1 := by simpa using hratio
        have hsm_le : s m - s m1 ≤ 1 :=
          (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hratio'
        have hsm_upper : s m ≤ s m1 + 1 := by omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hinj : Set.InjOn s (↑(T.erase m0) : Set ℕ) := by
        intro a ha b hb hab
        exact hs_inj (Finset.mem_erase.mp ha).2 (Finset.mem_erase.mp hb).2 hab
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hinj] at hcard
      have h2 : (T.erase m0).card ≤ 2 :=
        le_trans hcard (Finset.card_le_two (a := s m1) (b := s m1 + 1))
      have hcardT : T.card = (T.erase m0).card + 1 := (Finset.card_erase_add_one hm0mem).symm
      omega

end Work.KMTAreas.A7rand
