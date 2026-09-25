import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace Commons.NumberTheory.Zeta

private lemma log_ge_one_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have hlog3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h31 : (1 : ℝ) ≤ Real.log 3 := by
    have := Real.log_three_gt_d9
    norm_num at this ⊢
    linarith
  linarith

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

private lemma reindex_left (A F : ℕ) (_hF1 : 1 ≤ F) (g : ℕ → ℝ) :
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

private lemma sum_Icc_split_middle (f : ℕ → ℝ) (A F B : ℕ) (hF1 : 1 ≤ F) (hAF : A ≤ F) (hFB : F + 1 ≤ B) :
    (∑ n ∈ Finset.Icc A B, f n) =
      (∑ n ∈ Finset.Icc A (F - 1), f n) + f F + f (F + 1) +
        (∑ n ∈ Finset.Icc (F + 2) B, f n) := by
  have hFB' : F ≤ B := by omega
  have hunion : Finset.Icc A B = Finset.Icc A (F - 1) ∪ Finset.Icc F B := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro h
      rcases h with ⟨h1, h2⟩
      by_cases hn : n ≤ F - 1
      · exact Or.inl ⟨h1, hn⟩
      · exact Or.inr ⟨by omega, h2⟩
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, by omega⟩
      · exact ⟨by omega, h2⟩
  have hdisj : Disjoint (Finset.Icc A (F - 1)) (Finset.Icc F B) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2
    omega
  rw [hunion, Finset.sum_union hdisj]
  have h2 : Finset.Icc F B = insert F (Finset.Icc (F + 1) B) :=
    (Finset.insert_Icc_add_one_left_eq_Icc hFB').symm
  have h3 : Finset.Icc (F + 1) B = insert (F + 1) (Finset.Icc (F + 2) B) :=
    (Finset.insert_Icc_add_one_left_eq_Icc hFB).symm
  have hnf1 : F ∉ Finset.Icc (F + 1) B := by
    simp only [Finset.mem_Icc]; omega
  have hnf2 : F + 1 ∉ Finset.Icc (F + 2) B := by
    simp only [Finset.mem_Icc]; omega
  rw [h2, Finset.sum_insert hnf1, h3, Finset.sum_insert hnf2]
  ring

theorem middle_min_dist_sum_le_refined (x T : ℝ) (hx : 4 ≤ x) (hT : 2 ≤ T) :
    (∑ n ∈ Finset.Icc (Nat.floor (x / 2) + 1) (Nat.floor (2 * x)),
        min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|))) ≤
      8 * (x * Real.log x / T) +
        min (1 : ℝ) ((2 * x) / (T * |x - (Nat.floor x : ℝ)|)) +
        min (1 : ℝ) ((2 * x) / (T * |x - ((Nat.floor x : ℝ) + 1)|)) := by
  have hx3 : 3 ≤ x := by linarith
  let A := Nat.floor (x / 2) + 1
  let B := Nat.floor (2 * x)
  let F := Nat.floor x
  let trm : ℕ → ℝ := fun n => min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|))
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 < T := by linarith
  have hAF : A ≤ F := by
    dsimp only [A, F]
    have h1 : ((Nat.floor (x / 2) : ℕ) : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
    have h2 : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
    have hlt : ((Nat.floor (x / 2) : ℕ) : ℝ) + 1 < (Nat.floor x : ℝ) := by linarith
    exact_mod_cast le_of_lt hlt
  have hFB : F + 1 ≤ B := by
    dsimp only [F, B]
    have h1 : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have h2 : 2 * x < ((Nat.floor (2 * x) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (2 * x)
    have hlt : ((Nat.floor x : ℕ) : ℝ) + 1 < ((Nat.floor (2 * x) : ℕ) : ℝ) := by linarith
    exact_mod_cast le_of_lt hlt
  have hL : (∑ n ∈ Finset.Icc A (F - 1), trm n) ≤ ((2 * x) / T) * (1 + Real.log x) := by
    have hstep : (∑ n ∈ Finset.Icc A (F - 1), trm n) ≤
        (∑ n ∈ Finset.Icc A (F - 1),
          (2 * x) / (T * ((Nat.floor x : ℝ) - (n : ℝ)))) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [trm]
      exact left_term_bound x T hx3 hT (by
        have h := (Finset.mem_Icc.mp hn).2
        simpa [F] using h)
    have hb := left_sum_bound x T hx3 hT
    refine le_trans hstep ?_
    simpa [A, F] using hb
  have hR : (∑ n ∈ Finset.Icc (F + 2) B, trm n) ≤ ((2 * x) / T) * (1 + Real.log x) := by
    have hstep : (∑ n ∈ Finset.Icc (F + 2) B, trm n) ≤
        (∑ n ∈ Finset.Icc (F + 2) B,
          (2 * x) / (T * ((n : ℝ) - (Nat.floor x : ℝ) - 1))) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [trm]
      exact right_term_bound x T hx3 hT (by
        have h := (Finset.mem_Icc.mp hn).1
        simpa [F] using h)
    have hb := right_sum_bound x T hx3 hT
    refine le_trans hstep ?_
    simpa [F, B] using hb
  have hF1 : 1 ≤ F := by
    dsimp only [F]
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ x))
  have hpart := sum_Icc_split_middle trm A F B hF1 hAF hFB
  have hmain : ((2 * x) / T) * (1 + Real.log x) + ((2 * x) / T) * (1 + Real.log x) ≤
      8 * (x * Real.log x / T) := by
    have hlog1 : 1 ≤ Real.log x := log_ge_one_of_three_le hx3
    have hfac : 0 ≤ (2 * x) / T := by positivity
    have hineq : 2 * (1 + Real.log x) ≤ 4 * Real.log x := by linarith
    have hmm := mul_le_mul_of_nonneg_left hineq hfac
    calc ((2 * x) / T) * (1 + Real.log x) + ((2 * x) / T) * (1 + Real.log x)
        = ((2 * x) / T) * (2 * (1 + Real.log x)) := by ring
      _ ≤ ((2 * x) / T) * (4 * Real.log x) := hmm
      _ = 8 * (x * Real.log x / T) := by ring
  have key : (∑ n ∈ Finset.Icc A B, trm n) ≤
      8 * (x * Real.log x / T) + trm F + trm (F + 1) := by
    have hsum : (∑ n ∈ Finset.Icc A B, trm n) ≤
        ((2 * x) / T) * (1 + Real.log x) + trm F + trm (F + 1) +
          ((2 * x) / T) * (1 + Real.log x) := by
      rw [hpart]; linarith [hL, hR]
    linarith [hsum, hmain]
  have hLHS : (∑ n ∈ Finset.Icc (Nat.floor (x / 2) + 1) (Nat.floor (2 * x)),
        min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|))) =
      (∑ n ∈ Finset.Icc A B, trm n) := by
    simp only [A, B, trm]
  have hR1 : trm F = min (1 : ℝ) ((2 * x) / (T * |x - (Nat.floor x : ℝ)|)) := by
    simp only [trm, F]
  have hR2 : trm (F + 1) = min (1 : ℝ) ((2 * x) / (T * |x - ((Nat.floor x : ℝ) + 1)|)) := by
    simp only [trm, F, Nat.cast_add, Nat.cast_one]
  rw [hLHS, ← hR1, ← hR2]
  exact key

end Commons.NumberTheory.Zeta
