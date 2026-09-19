import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.Zeta.mangoldt_series_re

open scoped BigOperators

namespace Commons.NumberTheory.Zeta

private lemma log_ge_one_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have hlog3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h31 : (1 : ℝ) ≤ Real.log 3 := by
    have := Real.log_three_gt_d9
    norm_num at this ⊢
    linarith
  linarith

private lemma min_one_le_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ min (1 : ℝ) y := by
  by_cases h : y ≤ 1
  · rw [min_eq_right h]
    exact hy
  · rw [min_eq_left (le_of_not_ge h)]
    norm_num

private lemma harm_prefix_le_one_add_log (J : ℕ) (x : ℝ) (hJx : (J : ℝ) ≤ x) (hx1 : 1 ≤ x) :
    (∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (j : ℝ)) ≤ 1 + Real.log x := by
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  by_cases hJ0 : J = 0
  · subst J
    simp
    linarith
  · have hJ1 : 1 ≤ J := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hJ0)
    have hJ0r : 0 < (J : ℝ) := by exact_mod_cast hJ1
    calc
      (∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (j : ℝ)) = (harmonic J : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        rw [Rat.cast_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Rat.cast_inv, Rat.cast_natCast, one_div]
      _ ≤ 1 + Real.log (J : ℝ) := by simpa using (harmonic_le_one_add_log J)
      _ ≤ 1 + Real.log x := by
        have hlog : Real.log (J : ℝ) ≤ Real.log x := Real.log_le_log hJ0r hJx
        linarith

private lemma reindex_left (A F : ℕ) (hF1 : 1 ≤ F) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc A (F - 1), g (F - n)) = (∑ j ∈ Finset.Icc 1 (F - A), g j) := by
  classical
  refine Finset.sum_bij (s := Finset.Icc A (F - 1)) (t := Finset.Icc 1 (F - A))
    (fun n _ => F - n) ?hi ?hinj ?hsurj ?hfun
  · intro n hn
    have hnA : A ≤ n := (Finset.mem_Icc.mp hn).1
    have hnF : n ≤ F - 1 := (Finset.mem_Icc.mp hn).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a₁ ha₁ a₂ ha₂ h
    have h₁ : A ≤ a₁ := (Finset.mem_Icc.mp ha₁).1
    have h₂ : a₁ ≤ F - 1 := (Finset.mem_Icc.mp ha₁).2
    have h₃ : A ≤ a₂ := (Finset.mem_Icc.mp ha₂).1
    have h₄ : a₂ ≤ F - 1 := (Finset.mem_Icc.mp ha₂).2
    omega
  · intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hb2 : b ≤ F - A := (Finset.mem_Icc.mp hb).2
    refine ⟨F - b, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · omega
  · intro a ha
    rfl

private lemma reindex_right (F B : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc (F + 2) B, g (n - F - 1)) = (∑ k ∈ Finset.Icc 1 (B - F - 1), g k) := by
  classical
  refine Finset.sum_bij (s := Finset.Icc (F + 2) B) (t := Finset.Icc 1 (B - F - 1))
    (fun n _ => n - F - 1) ?hi ?hinj ?hsurj ?hfun
  · intro n hn
    have hnA : F + 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnF : n ≤ B := (Finset.mem_Icc.mp hn).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a₁ ha₁ a₂ ha₂ h
    have h₁ : F + 2 ≤ a₁ := (Finset.mem_Icc.mp ha₁).1
    have h₂ : a₁ ≤ B := (Finset.mem_Icc.mp ha₁).2
    have h₃ : F + 2 ≤ a₂ := (Finset.mem_Icc.mp ha₂).1
    have h₄ : a₂ ≤ B := (Finset.mem_Icc.mp ha₂).2
    omega
  · intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hb2 : b ≤ B - F - 1 := (Finset.mem_Icc.mp hb).2
    refine ⟨F + 1 + b, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · omega
  · intro a ha
    rfl

private lemma left_term_bound (x T : ℝ) (hx : 3 ≤ x) (hT : 2 ≤ T) {n : ℕ}
    (hn : n ≤ Nat.floor x - 1) :
    min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) ≤
      (2 * x) / (T * ((Nat.floor x : ℝ) - (n : ℝ))) := by
  let F := Nat.floor x
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 < T := by linarith
  have hFle : (F : ℝ) ≤ x := Nat.floor_le hx0
  have hF1 : 1 ≤ F := by exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ x))
  have hnRx : (n : ℝ) ≤ x := by
    have hnF : n ≤ F := le_trans hn (Nat.sub_le F 1)
    have hnR : (n : ℝ) ≤ (F : ℝ) := by exact_mod_cast hnF
    linarith
  have habs : |x - (n : ℝ)| = x - (n : ℝ) := by
    exact abs_of_nonneg (sub_nonneg.mpr hnRx)
  have hd1 : 0 < ((F : ℝ) - (n : ℝ)) := by
    have hnR : (n : ℝ) ≤ (F : ℝ) - 1 := by
      have hsubcast : ((F - 1 : ℕ) : ℝ) = (F : ℝ) - 1 := by simpa using (Nat.cast_sub (R := ℝ) hF1)
      rw [← hsubcast]
      exact_mod_cast hn
    linarith
  have hTd1 : 0 < T * ((F : ℝ) - (n : ℝ)) := by positivity
  have hden : T * ((F : ℝ) - (n : ℝ)) ≤ T * (x - (n : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hT0)
    linarith
  calc
    min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) ≤ (2 * x) / (T * |x - (n : ℝ)|) := min_le_right _ _
    _ = (2 * x) / (T * (x - (n : ℝ))) := by rw [habs]
    _ ≤ (2 * x) / (T * ((F : ℝ) - (n : ℝ))) := by
      exact div_le_div_of_nonneg_left (by nlinarith : 0 ≤ 2 * x) hTd1 hden

private lemma right_term_bound (x T : ℝ) (hx : 3 ≤ x) (hT : 2 ≤ T) {n : ℕ}
    (hn : Nat.floor x + 2 ≤ n) :
    min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) ≤
      (2 * x) / (T * ((n : ℝ) - (Nat.floor x : ℝ) - 1)) := by
  let F := Nat.floor x
  have hT0 : 0 < T := by linarith
  have hxlt : x < (F : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcast : ((F + 2 : ℕ) : ℝ) = (F : ℝ) + 2 := by norm_num [Nat.cast_add]
  have hnF2 : (F : ℝ) + 2 ≤ (n : ℝ) := by
    rw [← hcast]
    exact_mod_cast hn
  have hxneg : x - (n : ℝ) < 0 := by linarith
  have habs : |x - (n : ℝ)| = (n : ℝ) - x := by
    rw [abs_of_neg hxneg]
    ring
  have hd : 0 < (n : ℝ) - (F : ℝ) - 1 := by linarith
  have hd2 : 0 < T * ((n : ℝ) - (F : ℝ) - 1) := mul_pos hT0 hd
  have hden : T * ((n : ℝ) - (F : ℝ) - 1) ≤ T * ((n : ℝ) - x) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hT0)
    linarith
  calc
    min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) ≤ (2 * x) / (T * |x - (n : ℝ)|) := min_le_right _ _
    _ = (2 * x) / (T * ((n : ℝ) - x)) := by rw [habs]
    _ ≤ (2 * x) / (T * ((n : ℝ) - (F : ℝ) - 1)) := by
      exact div_le_div_of_nonneg_left (by nlinarith : 0 ≤ 2 * x) hd2 hden

private lemma left_sum_bound (x T : ℝ) (hx : 3 ≤ x) (hT : 2 ≤ T) :
    (∑ n ∈ Finset.Icc (Nat.floor (x / 2) + 1) (Nat.floor x - 1),
        (2 * x) / (T * ((Nat.floor x : ℝ) - (n : ℝ)))) ≤
      ((2 * x) / T) * (1 + Real.log x) := by
  let A := Nat.floor (x / 2) + 1
  let F := Nat.floor x
  let J := F - A
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 < T := by linarith
  have hTne : T ≠ 0 := ne_of_gt hT0
  have hF1 : 1 ≤ F := by exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ x))
  have hJle : (J : ℝ) ≤ x := by
    have hJF : J ≤ F := Nat.sub_le F A
    have hcast : (J : ℝ) ≤ (F : ℝ) := by exact_mod_cast hJF
    have hFle : (F : ℝ) ≤ x := Nat.floor_le hx0
    linarith
  calc
    (∑ n ∈ Finset.Icc A (F - 1),
        (2 * x) / (T * ((F : ℝ) - (n : ℝ))))
      = (∑ n ∈ Finset.Icc A (F - 1),
          (2 * x) / (T * ((F - n : ℕ) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnF : n ≤ F := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le F 1)
        have hsub : ((F - n : ℕ) : ℝ) = (F : ℝ) - (n : ℝ) := Nat.cast_sub (R := ℝ) hnF
        rw [hsub]
    _ = (∑ j ∈ Finset.Icc 1 J, (2 * x) / (T * (j : ℝ))) := by
        exact reindex_left A F hF1 (fun m => (2 * x) / (T * (m : ℝ)))
    _ = ((2 * x) / T) * (∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (j : ℝ)) := by
        calc
          (∑ j ∈ Finset.Icc 1 J, (2 * x) / (T * (j : ℝ)))
              = (∑ j ∈ Finset.Icc 1 J, ((2 * x) / T) * (1 / (j : ℝ))) := by
                apply Finset.sum_congr rfl
                intro j hj
                have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
                have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hj1)
                field_simp [hTne, hj0]
          _ = ((2 * x) / T) * (∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (j : ℝ)) := by
                rw [Finset.mul_sum]
    _ ≤ ((2 * x) / T) * (1 + Real.log x) := by
        apply mul_le_mul_of_nonneg_left _ _
        · exact harm_prefix_le_one_add_log J x hJle (by linarith : 1 ≤ x)
        · have h2x : 0 ≤ 2 * x := by nlinarith
          exact div_nonneg h2x (le_of_lt hT0)

private lemma right_sum_bound (x T : ℝ) (hx : 3 ≤ x) (hT : 2 ≤ T) :
    (∑ n ∈ Finset.Icc (Nat.floor x + 2) (Nat.floor (2 * x)),
        (2 * x) / (T * ((n : ℝ) - (Nat.floor x : ℝ) - 1))) ≤
      ((2 * x) / T) * (1 + Real.log x) := by
  let F := Nat.floor x
  let B := Nat.floor (2 * x)
  let K := B - F - 1
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 < T := by linarith
  have hTne : T ≠ 0 := ne_of_gt hT0
  have hKle : (K : ℝ) ≤ x := by
    have hFB : F ≤ B := by
      exact Nat.floor_le_floor (by nlinarith : x ≤ 2 * x)
    have h1le : 1 ≤ B - F := by
      have hF1B : F + 1 ≤ B := by
        apply Nat.le_floor
        have hc : ((F + 1 : ℕ) : ℝ) = (F : ℝ) + 1 := by norm_num [Nat.cast_add]
        rw [hc]
        have hFle : (F : ℝ) ≤ x := Nat.floor_le hx0
        nlinarith
      omega
    calc
      (K : ℝ) = ((B - F - 1 : ℕ) : ℝ) := by simp [K]
      _ = ((B - F : ℕ) : ℝ) - 1 := by
        simpa using (Nat.cast_sub (R := ℝ) h1le)
      _ = (B : ℝ) - (F : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) hFB]
      _ ≤ x := by
        have hB' : (B : ℝ) ≤ 2 * x := Nat.floor_le (by nlinarith : 0 ≤ 2 * x)
        have hF' : x - 1 ≤ (F : ℝ) := by
          have hxlt : x < (F : ℝ) + 1 := Nat.lt_floor_add_one x
          linarith
        linarith
  calc
    (∑ n ∈ Finset.Icc (F + 2) B,
        (2 * x) / (T * ((n : ℝ) - (F : ℝ) - 1)))
      = (∑ n ∈ Finset.Icc (F + 2) B,
          (2 * x) / (T * ((n - F - 1 : ℕ) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnF2 : F + 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hncast : ((n - F - 1 : ℕ) : ℝ) = (n : ℝ) - (F : ℝ) - 1 := by
          have hsub1 : ((n - (F + 1) : ℕ) : ℝ) = (n : ℝ) - ((F + 1 : ℕ) : ℝ) :=
            Nat.cast_sub (R := ℝ) (by omega : F + 1 ≤ n)
          have hFc : ((F + 1 : ℕ) : ℝ) = (F : ℝ) + 1 := by norm_num [Nat.cast_add]
          have hnat : n - F - 1 = n - (F + 1) := by omega
          rw [hnat, hsub1, hFc]
          ring
        rw [hncast]
    _ = (∑ k ∈ Finset.Icc 1 K, (2 * x) / (T * (k : ℝ))) := by
        exact reindex_right F B (fun m => (2 * x) / (T * (m : ℝ)))
    _ = ((2 * x) / T) * (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ)) := by
        calc
          (∑ k ∈ Finset.Icc 1 K, (2 * x) / (T * (k : ℝ)))
              = (∑ k ∈ Finset.Icc 1 K, ((2 * x) / T) * (1 / (k : ℝ))) := by
                apply Finset.sum_congr rfl
                intro k hk
                have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
                have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk1)
                field_simp [hTne, hk0]
          _ = ((2 * x) / T) * (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ)) := by
                rw [Finset.mul_sum]
    _ ≤ ((2 * x) / T) * (1 + Real.log x) := by
        apply mul_le_mul_of_nonneg_left _ _
        · exact harm_prefix_le_one_add_log K x hKle (by linarith : 1 ≤ x)
        · have h2x : 0 ≤ 2 * x := by nlinarith
          exact div_nonneg h2x (le_of_lt hT0)

private lemma sum_split_three (A F B : ℕ) (hF1 : 1 ≤ F) (f : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hfF : f F ≤ 1) (hfF1 : f (F + 1) ≤ 1) :
    (∑ n ∈ Finset.Icc A B, f n) ≤
      (∑ n ∈ Finset.Icc A (F - 1), f n) + 2 + (∑ n ∈ Finset.Icc (F + 2) B, f n) := by
  classical
  let p1 : ℕ → Prop := fun n => n ≤ F - 1
  let p2 : ℕ → Prop := fun n => n = F ∨ n = F + 1
  let p3 : ℕ → Prop := fun n => F + 2 ≤ n
  have hpt (n : ℕ) (hn : n ∈ Finset.Icc A B) :
      f n ≤ (if p1 n then f n else 0) + (if p2 n then f n else 0) +
          (if p3 n then f n else 0) := by
    have hpart : n ≤ F - 1 ∨ n = F ∨ n = F + 1 ∨ F + 2 ≤ n := by omega
    rcases hpart with h1 | hF | hF1' | hbig
    · have hnot2 : ¬(n = F ∨ n = F + 1) := by omega
      have hnot3 : ¬(F + 2 ≤ n) := by omega
      rw [if_pos h1, if_neg hnot2, if_neg hnot3]
      simp
    · have hnot1 : ¬(n ≤ F - 1) := by omega
      have hP2 : n = F ∨ n = F + 1 := Or.inl hF
      have hnot3 : ¬(F + 2 ≤ n) := by omega
      rw [if_neg hnot1, if_pos hP2, if_neg hnot3]
      simp
    · have hnot1 : ¬(n ≤ F - 1) := by omega
      have hP2 : n = F ∨ n = F + 1 := Or.inr hF1'
      have hnot3 : ¬(F + 2 ≤ n) := by omega
      rw [if_neg hnot1, if_pos hP2, if_neg hnot3]
      simp
    · have hnot1 : ¬(n ≤ F - 1) := by omega
      have hnot2 : ¬(n = F ∨ n = F + 1) := by omega
      rw [if_neg hnot1, if_neg hnot2, if_pos hbig]
      simp
  have hsum := Finset.sum_le_sum hpt
  have hsplit : (∑ n ∈ Finset.Icc A B, f n) ≤
      (∑ n ∈ Finset.Icc A B, (if p1 n then f n else 0)) +
      (∑ n ∈ Finset.Icc A B, (if p2 n then f n else 0)) +
      (∑ n ∈ Finset.Icc A B, (if p3 n then f n else 0)) := by
    simpa [Finset.sum_add_distrib] using hsum
  have h1 : (∑ n ∈ Finset.Icc A B, (if p1 n then f n else 0)) ≤
      (∑ n ∈ Finset.Icc A (F - 1), f n) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, p1] at hn
      exact Finset.mem_Icc.mpr ⟨hn.1.1, hn.2⟩
    · intro n hn hn'
      exact hf0 n
  have h3 : (∑ n ∈ Finset.Icc A B, (if p3 n then f n else 0)) ≤
      (∑ n ∈ Finset.Icc (F + 2) B, f n) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, p3] at hn
      exact Finset.mem_Icc.mpr ⟨hn.2, hn.1.2⟩
    · intro n hn hn'
      exact hf0 n
  have h2 : (∑ n ∈ Finset.Icc A B, (if p2 n then f n else 0)) ≤ 2 := by
    rw [← Finset.sum_filter]
    have hle : (∑ n ∈ (Finset.Icc A B).filter p2, f n) ≤
        (∑ n ∈ (Finset.Icc A B).filter p2, (1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, p2] at hn
      rcases hn.2 with hF | hF1
      · rw [hF]
        exact hfF
      · rw [hF1]
        exact hfF1
    have hcard : ((Finset.Icc A B).filter p2).card ≤ 2 := by
      have hsub : (Finset.Icc A B).filter p2 ⊆ ({F, F + 1} : Finset ℕ) := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc, p2] at hn
        simp [hn.2]
      have hc : ({F, F + 1} : Finset ℕ).card = 2 := by simp
      calc
        ((Finset.Icc A B).filter p2).card ≤ ({F, F + 1} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 2 := hc
    calc
      (∑ n ∈ (Finset.Icc A B).filter p2, f n) ≤
          (∑ n ∈ (Finset.Icc A B).filter p2, (1 : ℝ)) := hle
      _ = (((Finset.Icc A B).filter p2).card : ℝ) := by simp
      _ ≤ 2 := by exact_mod_cast hcard
  linarith

theorem middle_min_dist_sum_le (x T : ℝ) (hx : 3 ≤ x) (hT : 2 ≤ T) :
    (∑ n ∈ Finset.Icc (Nat.floor (x / 2) + 1) (Nat.floor (2 * x)),
        min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|))) ≤
      100 * (x * Real.log x / T) + 100 := by
  let A := Nat.floor (x / 2) + 1
  let B := Nat.floor (2 * x)
  let F := Nat.floor x
  let trm : ℕ → ℝ := fun n => min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|))
  change (∑ n ∈ Finset.Icc A B, trm n) ≤ 100 * (x * Real.log x / T) + 100
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 < T := by linarith
  have hF1 : 1 ≤ F := by
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ x))
  have htrm0 : ∀ n : ℕ, 0 ≤ trm n := by
    intro n
    dsimp [trm]
    apply min_one_le_of_nonneg
    have h2x : 0 ≤ 2 * x := by nlinarith
    have habs0 : 0 ≤ |x - (n : ℝ)| := abs_nonneg _
    have hTabs : 0 ≤ T * |x - (n : ℝ)| := mul_nonneg (le_of_lt hT0) habs0
    exact div_nonneg h2x hTabs
  have htrm1 : trm F ≤ 1 := by dsimp [trm]; exact min_le_left _ _
  have htrm2 : trm (F + 1) ≤ 1 := by dsimp [trm]; exact min_le_left _ _
  have hcov := sum_split_three A F B hF1 trm htrm0 htrm1 htrm2
  have hL : (∑ n ∈ Finset.Icc A (F - 1), trm n) ≤ ((2 * x) / T) * (1 + Real.log x) := by
    calc
      (∑ n ∈ Finset.Icc A (F - 1), trm n)
          ≤ (∑ n ∈ Finset.Icc A (F - 1), (2 * x) / (T * ((F : ℝ) - (n : ℝ)))) := by
            apply Finset.sum_le_sum
            intro n hn
            exact left_term_bound x T hx hT (by
              have h2 := (Finset.mem_Icc.mp hn).2
              simpa using h2)
      _ ≤ ((2 * x) / T) * (1 + Real.log x) := left_sum_bound x T hx hT
  have hR : (∑ n ∈ Finset.Icc (F + 2) B, trm n) ≤ ((2 * x) / T) * (1 + Real.log x) := by
    calc
      (∑ n ∈ Finset.Icc (F + 2) B, trm n)
          ≤ (∑ n ∈ Finset.Icc (F + 2) B, (2 * x) / (T * ((n : ℝ) - (F : ℝ) - 1))) := by
            apply Finset.sum_le_sum
            intro n hn
            exact right_term_bound x T hx hT (by
              have h1 := (Finset.mem_Icc.mp hn).1
              simpa using h1)
      _ ≤ ((2 * x) / T) * (1 + Real.log x) := right_sum_bound x T hx hT
  have hS : (∑ n ∈ Finset.Icc A B, trm n) ≤
      2 + 2 * (((2 * x) / T) * (1 + Real.log x)) := by
    linarith [hcov, hL, hR]
  have hlog1 : 1 ≤ Real.log x := log_ge_one_of_three_le hx
  have hc0 : 0 ≤ (2 * x) / T := by
    apply div_nonneg
    · nlinarith
    · exact le_of_lt hT0
  have hq0 : 0 ≤ x * Real.log x / T := by
    apply div_nonneg
    · exact mul_nonneg hx0 (by linarith)
    · exact le_of_lt hT0
  have hEstep : ((2 * x) / T) * (1 + Real.log x) ≤ ((2 * x) / T) * (2 * Real.log x) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    linarith
  have hring : 2 * (((2 * x) / T) * (2 * Real.log x)) = 8 * (x * Real.log x / T) := by ring
  have hfin1 : 2 + 2 * (((2 * x) / T) * (1 + Real.log x)) ≤
      100 * (x * Real.log x / T) + 100 := by
    calc
      2 + 2 * (((2 * x) / T) * (1 + Real.log x))
          ≤ 2 + 2 * (((2 * x) / T) * (2 * Real.log x)) := by
            have hm := mul_le_mul_of_nonneg_left hEstep (by norm_num : (0 : ℝ) ≤ 2)
            linarith
      _ = 2 + 8 * (x * Real.log x / T) := by rw [hring]
      _ ≤ 100 * (x * Real.log x / T) + 100 := by
            have h8 : 8 * (x * Real.log x / T) ≤ 100 * (x * Real.log x / T) := by
              exact mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 100) hq0
            linarith
  exact le_trans hS hfin1

end Commons.NumberTheory.Zeta