import Mathlib.Data.Nat.Choose.Multinomial

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Commons.Combinatorics.Multinomial

/-- `n * (n - 1)! = n!` for `n ≥ 1`. -/
private lemma mul_factorial_pred {n : ℕ} (hn : 1 ≤ n) :
    n * Nat.factorial (n - 1) = Nat.factorial n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [Nat.factorial_succ]

/-- Product identity for the elementary "balancing" move on two coordinates: decreasing
coordinate `i` by one and increasing coordinate `j` by one multiplies the product of the
factorials by `(a j + 1) / (a i)`; stated without division, cross-multiplied. -/
private lemma prod_factorial_update {m : ℕ} (a : Fin m → ℕ) {i j : Fin m} (hij : i ≠ j)
    (hi : 1 ≤ a i) :
    (a i) * ∏ x, Nat.factorial (Function.update (Function.update a i (a i - 1)) j (a j + 1) x)
      = (a j + 1) * ∏ x, Nat.factorial (a x) := by
  classical
  set b : Fin m → ℕ := Function.update (Function.update a i (a i - 1)) j (a j + 1) with hb
  have hbi : b i = a i - 1 := by
    rw [hb, Function.update_apply, if_neg hij, Function.update_apply, if_pos rfl]
  have hbj : b j = a j + 1 := by
    rw [hb, Function.update_apply, if_pos rfl]
  have hb_eq : ∀ x, x ≠ i → x ≠ j → b x = a x := by
    intro x hxi hxj
    rw [hb, Function.update_apply, if_neg hxj, Function.update_apply, if_neg hxi]
  have hrest : (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (b x))
      = (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (a x)) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxi : x ≠ i := fun h => hx.2 (by simp [h])
    have hxj : x ≠ j := fun h => hx.2 (by simp [h])
    rw [hb_eq x hxi hxj]
  have hfac_i : a i * Nat.factorial (b i) = Nat.factorial (a i) := by
    rw [hbi]; exact mul_factorial_pred hi
  have hfac_j : Nat.factorial (b j) = (a j + 1) * Nat.factorial (a j) := by
    rw [hbj, Nat.factorial_succ]
  have hsplit_b : (∏ x, Nat.factorial (b x))
      = (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (b x)) *
          (Nat.factorial (b i) * Nat.factorial (b j)) := by
    rw [← Finset.prod_sdiff (s₁ := ({i, j} : Finset (Fin m))) (s₂ := Finset.univ) (by simp),
      Finset.prod_pair hij]
  have hsplit_a : (∏ x, Nat.factorial (a x))
      = (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (a x)) *
          (Nat.factorial (a i) * Nat.factorial (a j)) := by
    rw [← Finset.prod_sdiff (s₁ := ({i, j} : Finset (Fin m))) (s₂ := Finset.univ) (by simp),
      Finset.prod_pair hij]
  have hL : (a i) * (∏ x, Nat.factorial (b x))
      = (a i * Nat.factorial (b i)) *
          (Nat.factorial (b j) *
            (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (b x))) := by
    rw [hsplit_b]; ring
  have hcommon : (a i * Nat.factorial (b i)) *
          (Nat.factorial (b j) *
            (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (b x)))
      = (Nat.factorial (a i) * ((a j + 1) * Nat.factorial (a j))) *
          (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (a x)) := by
    rw [hrest, hfac_i, hfac_j]
    ring
  have hR : (Nat.factorial (a i) * ((a j + 1) * Nat.factorial (a j))) *
          (∏ x ∈ (Finset.univ \ ({i, j} : Finset (Fin m))), Nat.factorial (a x))
      = (a j + 1) * (∏ x, Nat.factorial (a x)) := by
    rw [hsplit_a]; ring
  have hgoal : (a i) * (∏ x, Nat.factorial (b x))
      = (a j + 1) * (∏ x, Nat.factorial (a x)) := hL.trans (hcommon.trans hR)
  rw [hb] at hgoal
  exact hgoal

/-- Sum invariance for the balancing move. -/
private lemma sum_update_update {m : ℕ} (a : Fin m → ℕ) {i j : Fin m} (hij : i ≠ j)
    (hi : 1 ≤ a i) :
    ∑ x, Function.update (Function.update a i (a i - 1)) j (a j + 1) x = ∑ x, a x := by
  classical
  set b : Fin m → ℕ := Function.update (Function.update a i (a i - 1)) j (a j + 1) with hb
  have hbi : b i = a i - 1 := by
    rw [hb, Function.update_apply, if_neg hij, Function.update_apply, if_pos rfl]
  have hbj : b j = a j + 1 := by
    rw [hb, Function.update_apply, if_pos rfl]
  have hb_eq : ∀ x, x ≠ i → x ≠ j → b x = a x := by
    intro x hxi hxj
    rw [hb, Function.update_apply, if_neg hxj, Function.update_apply, if_neg hxi]
  have hji : j ∈ Finset.univ.erase i := by
    rw [Finset.mem_erase]; exact ⟨Ne.symm hij, Finset.mem_univ j⟩
  have h1 : ∑ x, b x = b i + ∑ x ∈ Finset.univ.erase i, b x :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have h2 : ∑ x ∈ Finset.univ.erase i, b x
      = b j + ∑ x ∈ (Finset.univ.erase i).erase j, b x :=
    (Finset.add_sum_erase _ _ hji).symm
  have h3 : ∑ x, a x = a i + (a j + ∑ x ∈ (Finset.univ.erase i).erase j, a x) := by
    rw [(Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm,
      (Finset.add_sum_erase _ _ hji).symm]
  have h4 : ∑ x ∈ (Finset.univ.erase i).erase j, b x
      = ∑ x ∈ (Finset.univ.erase i).erase j, a x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
    exact hb_eq x hx.2 hx.1
  have hgoal : ∑ x, b x = ∑ x, a x := by
    rw [h1, h2, h3, h4, hbi, hbj]
    omega
  rw [hb] at hgoal
  exact hgoal

/-- The elementary balancing move strictly increases the multinomial coefficient. -/
private lemma multinomial_lt_update {m : ℕ} (a : Fin m → ℕ) {i j : Fin m} (hij : i ≠ j)
    (h : a j + 2 ≤ a i) :
    Nat.multinomial Finset.univ a <
      Nat.multinomial Finset.univ (Function.update (Function.update a i (a i - 1)) j (a j + 1)) := by
  classical
  set b : Fin m → ℕ := Function.update (Function.update a i (a i - 1)) j (a j + 1) with hb
  have hi : 1 ≤ a i := by omega
  have hprod : (a i) * (∏ x, Nat.factorial (b x))
      = (a j + 1) * (∏ x, Nat.factorial (a x)) := by
    rw [hb]; exact prod_factorial_update a hij hi
  have hPa : 0 < ∏ x, Nat.factorial (a x) := Finset.prod_pos fun x _ => Nat.factorial_pos (a x)
  have hlt : (∏ x, Nat.factorial (b x)) < (∏ x, Nat.factorial (a x)) := by
    have h1 : (a j + 1) * (∏ x, Nat.factorial (a x)) < (a i) * (∏ x, Nat.factorial (a x)) :=
      Nat.mul_lt_mul_of_pos_right (by omega) hPa
    rw [← hprod] at h1
    exact Nat.lt_of_mul_lt_mul_left h1
  have hsum : ∑ x, b x = ∑ x, a x := by
    rw [hb]; exact sum_update_update a hij hi
  have hspec_a : (∏ x, Nat.factorial (a x)) * Nat.multinomial Finset.univ a
      = Nat.factorial (∑ x, a x) := by
    simpa using Nat.multinomial_spec Finset.univ a
  have hspec_b : (∏ x, Nat.factorial (b x)) * Nat.multinomial Finset.univ b
      = Nat.factorial (∑ x, b x) := by
    simpa using Nat.multinomial_spec Finset.univ b
  have H : (∏ x, Nat.factorial (a x)) * Nat.multinomial Finset.univ a
      = (∏ x, Nat.factorial (b x)) * Nat.multinomial Finset.univ b := by
    rw [hspec_a, hspec_b, hsum]
  have hgoal : Nat.multinomial Finset.univ a < Nat.multinomial Finset.univ b := by
    by_contra hcon
    simp only [not_lt] at hcon
    have hstep : (∏ x, Nat.factorial (b x)) * Nat.multinomial Finset.univ b
        < (∏ x, Nat.factorial (a x)) * Nat.multinomial Finset.univ a :=
      calc (∏ x, Nat.factorial (b x)) * Nat.multinomial Finset.univ b
          ≤ (∏ x, Nat.factorial (b x)) * Nat.multinomial Finset.univ a :=
            Nat.mul_le_mul_left _ hcon
        _ < (∏ x, Nat.factorial (a x)) * Nat.multinomial Finset.univ a :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.multinomial_pos Finset.univ a)
    rw [H] at hstep
    exact absurd hstep (lt_irrefl _)
  rw [hb] at hgoal
  exact hgoal

theorem le_central (m d : ℕ) (hm : 0 < m) (hmd : m ∣ d) (pv : Fin m → ℕ)
    (hsum : ∑ i, pv i = d) :
    Nat.multinomial Finset.univ pv ≤ Nat.multinomial Finset.univ (fun _ : Fin m => d / m) := by
  classical
  have hmul : m * (d / m) = d := Nat.mul_div_cancel' hmd
  have hsumbar : ∑ _ : Fin m, d / m = d := by
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hmul
  have hpv_mem : pv ∈ (Fintype.piFinset (fun _ : Fin m => Finset.range (d + 1))).filter
      (fun a => ∑ i, a i = d) := by
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, hsum⟩
    rw [Finset.mem_range]
    have hle : pv i ≤ ∑ i, pv i :=
      Finset.single_le_sum (f := pv) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨a, haS, hamax⟩ := Finset.exists_max_image
    ((Fintype.piFinset (fun _ : Fin m => Finset.range (d + 1))).filter (fun a => ∑ i, a i = d))
    (fun a => Nat.multinomial Finset.univ a) ⟨pv, hpv_mem⟩
  have ha_sum : ∑ i, a i = d := (Finset.mem_filter.mp haS).2
  have ha_bd : ∀ i, a i ≤ d := by
    intro i
    have h1 : a i ∈ Finset.range (d + 1) :=
      Fintype.mem_piFinset.mp (Finset.mem_filter.mp haS).1 i
    simp only [Finset.mem_range] at h1
    omega
  have hmax_pv : Nat.multinomial Finset.univ pv ≤ Nat.multinomial Finset.univ a :=
    hamax pv hpv_mem
  have ha_const : a = fun _ : Fin m => d / m := by
    by_contra hne
    have hex_i : ∃ i, d / m < a i := by
      by_contra h
      simp only [not_exists, not_lt] at h
      exact hne (by
        funext i
        by_contra hnei
        have hlt_i : a i < d / m := lt_of_le_of_ne (h i) hnei
        have hstr : ∑ j, a j < ∑ j, (fun _ : Fin m => d / m) j :=
          Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ i, hlt_i⟩
        rw [ha_sum, hsumbar] at hstr
        exact lt_irrefl _ hstr)
    have hex_j : ∃ j, a j < d / m := by
      by_contra h
      simp only [not_exists, not_lt] at h
      exact hne (by
        funext i
        by_contra hnei
        have hlt_i : d / m < a i := lt_of_le_of_ne (h i) (Ne.symm hnei)
        have hstr : ∑ j, (fun _ : Fin m => d / m) j < ∑ j, a j :=
          Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ i, hlt_i⟩
        rw [hsumbar, ha_sum] at hstr
        exact lt_irrefl _ hstr)
    obtain ⟨i, hi⟩ := hex_i
    obtain ⟨j, hj⟩ := hex_j
    have hij : i ≠ j := by intro h; rw [h] at hi; omega
    have hstep : a j + 2 ≤ a i := by omega
    set b : Fin m → ℕ := Function.update (Function.update a i (a i - 1)) j (a j + 1) with hb
    have hb_sum : ∑ x, b x = ∑ x, a x := by
      rw [hb]; exact sum_update_update a hij (by omega)
    have hb_mem : b ∈ (Fintype.piFinset (fun _ : Fin m => Finset.range (d + 1))).filter
        (fun a => ∑ i, a i = d) := by
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun x => ?_, ?_⟩
      · rw [Finset.mem_range]
        have hle : b x ≤ ∑ x, b x :=
          Finset.single_le_sum (f := b) (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
        omega
      · rw [hb_sum, ha_sum]
    have hgt : Nat.multinomial Finset.univ a < Nat.multinomial Finset.univ b := by
      rw [hb]; exact multinomial_lt_update a hij hstep
    have hle := hamax b hb_mem
    omega
  rw [ha_const] at hmax_pv
  exact hmax_pv

end Commons.Combinatorics.Multinomial