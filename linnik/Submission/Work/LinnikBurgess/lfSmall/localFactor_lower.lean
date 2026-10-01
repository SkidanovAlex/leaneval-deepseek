import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs

/-!
# `localFactor 2 e a b` dominates the two main menu terms (`e ≥ 13`)

For `e ≥ 13` the `p = 2`, large-`e` branch of `menuW` applies, so

```
menuW 2 e s j
  = (if j = 0 ∧ s ≤ T then 10^6 · 2^(s/2) else 0)
    + (if s = max T j then 10^6 · 2^((m+j)/2) else 0),      T = capLevel 2 e,  m = cubeLevel 2 e.
```

Consequently every menu entry `menuW 2 e s 0` with `s ≤ T` dominates the uncapped weight
`10^6 · 2^(s/2) * [DLp 2 s a b]`, and the entry at `(max T j, j)` dominates the content weight
`10^6 · 2^((m+j)/2) * [DLp 2 (max T j) a b]` (for `2^j ∣ contAB a b`).

This is the `p = 2` counterpart of `localFactor_ge_small`, needed to turn the counting bounds for
`lvlSet2`/`capSet2` into the final local bound at `e ≥ 13`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.lfSmall

/-! ### Unfolding `menuW` at `p = 2`, `e ≥ 13` -/

private lemma menuW_two (e s j : ℕ) (he : 13 ≤ e) :
    menuW 2 e s j =
      (if j = 0 ∧ s ≤ capLevel 2 e then (10:ℝ)^6 * (2:ℝ)^((s:ℝ)/2) else 0)
      + (if s = max (capLevel 2 e) j then
          (10:ℝ)^6 * (2:ℝ)^(((cubeLevel 2 e:ℝ)+(j:ℝ))/2) else 0) := by
  rw [menuW, if_neg (by norm_num : ¬ (5:ℕ) ≤ 2), if_neg (by omega : ¬ e ≤ 12)]
  simp only [Nat.cast_ofNat]

private lemma menuW_two_nonneg {e s j : ℕ} (he : 13 ≤ e) : (0:ℝ) ≤ menuW 2 e s j := by
  rw [menuW, if_neg (by norm_num : ¬ (5:ℕ) ≤ 2), if_neg (by omega : ¬ e ≤ 12)]
  split_ifs <;> positivity

private lemma menuW_two_low {e s : ℕ} (he : 13 ≤ e) (hs : s ≤ capLevel 2 e) :
    (10:ℝ)^6 * (2:ℝ)^((s:ℝ)/2) ≤ menuW 2 e s 0 := by
  rw [menuW_two e s 0 he]
  rw [if_pos ⟨rfl, hs⟩]
  have h2 : (0:ℝ) ≤ (if s = max (capLevel 2 e) 0 then
      (10:ℝ)^6 * (2:ℝ)^(((cubeLevel 2 e:ℝ)+((0:ℕ):ℝ))/2) else 0) := by split <;> positivity
  linarith

private lemma menuW_two_cont {e j : ℕ} (he : 13 ≤ e) :
    (10:ℝ)^6 * (2:ℝ)^(((cubeLevel 2 e:ℝ)+(j:ℝ))/2)
      ≤ menuW 2 e (max (capLevel 2 e) j) j := by
  rw [menuW_two e (max (capLevel 2 e) j) j he]
  rw [if_pos rfl]
  have h1 : (0:ℝ) ≤ (if j = 0 ∧ max (capLevel 2 e) j ≤ capLevel 2 e then
      (10:ℝ)^6 * (2:ℝ)^(((max (capLevel 2 e) j:ℕ):ℝ)/2) else 0) := by split <;> positivity
  linarith

private lemma menuW_two_cap {e : ℕ} (he : 13 ≤ e) :
    menuW 2 e (capLevel 2 e) 0
      = (10:ℝ)^6 * (2:ℝ)^(((capLevel 2 e:ℕ):ℝ)/2)
        + (10:ℝ)^6 * (2:ℝ)^(((cubeLevel 2 e:ℕ):ℝ)/2) := by
  rw [menuW_two e (capLevel 2 e) 0 he]
  rw [if_pos (by simp), if_pos (by simp)]
  ring_nf

private lemma menuW_two_lt {e s : ℕ} (he : 13 ≤ e) (hs : s < capLevel 2 e) :
    menuW 2 e s 0 = (10:ℝ)^6 * (2:ℝ)^((s:ℝ)/2) := by
  rw [menuW_two e s 0 he]
  rw [if_pos ⟨rfl, le_of_lt hs⟩,
    if_neg (by simp only [Nat.max_eq_left (Nat.zero_le _)]; omega)]
  ring

/-- The `j = 0` menu entry, with the divisibility `2^0 = 1` simplified away. -/
private lemma Gzero_eq (e s : ℕ) (a b : Fin 3 → ℕ) :
    menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0)
      = menuW 2 e s 0 * ind (DLp 2 s a b) := by
  congr 1
  by_cases h : DLp 2 s a b
  · rw [ind_eq_one_of _ h, if_pos ⟨h, by rw [pow_zero]; exact one_dvd _⟩]
  · rw [ind_eq_zero_of _ h, if_neg (by rintro ⟨h', _⟩; exact h h')]

private lemma G_nonneg {e s j : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) :
    (0:ℝ) ≤ menuW 2 e s j * (if DLp 2 s a b ∧ 2^j ∣ contAB a b then (1:ℝ) else 0) :=
  mul_nonneg (menuW_two_nonneg he) (by split <;> norm_num)

/-! ### The two menu terms -/

/-- The whole uncapped row `s ≤ T`, `j = 0` is dominated by `localFactor`. -/
private lemma low_sum_le (e : ℕ) (he : 13 ≤ e) (a b : Fin 3 → ℕ) :
    (10:ℝ)^6 * (∑ s ∈ Finset.range (capLevel 2 e + 1),
        ind (DLp 2 s a b) * (2:ℝ)^((s:ℝ)/2))
      ≤ ∑ s ∈ Finset.range (capLevel 2 e + 1),
          menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsT : s ≤ capLevel 2 e := by have := Finset.mem_range.mp hs; omega
  have hlow := menuW_two_low (e := e) (s := s) he hsT
  have hind : (0:ℝ) ≤ ind (DLp 2 s a b) := ind_nonneg _
  have hstep : ((10:ℝ)^6 * (2:ℝ)^((s:ℝ)/2)) * ind (DLp 2 s a b)
      ≤ menuW 2 e s 0 * ind (DLp 2 s a b) := mul_le_mul_of_nonneg_right hlow hind
  rw [← Gzero_eq e s a b] at hstep
  have htarget : (10:ℝ)^6 * (ind (DLp 2 s a b) * (2:ℝ)^((s:ℝ)/2))
      = ((10:ℝ)^6 * (2:ℝ)^((s:ℝ)/2)) * ind (DLp 2 s a b) := by ring
  rw [htarget]
  exact hstep

/-- The capped content term `(max T j, j)` is dominated by `localFactor`. -/
private lemma cont_le (e J : ℕ) (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hJ : padicValNat 2 (contAB a b) = J) :
    (10:ℝ)^6 * ((2:ℝ)^(((cubeLevel 2 e:ℝ) + ((min J e : ℕ):ℝ))/2)
        * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b))
      ≤ menuW 2 e (max (capLevel 2 e) (min J e)) (min J e)
          * (if DLp 2 (max (capLevel 2 e) (min J e)) a b
              ∧ 2^(min J e) ∣ contAB a b then (1:ℝ) else 0) := by
  classical
  have hdvd : 2^(min J e) ∣ contAB a b := by
    have h : 2^J ∣ contAB a b := by rw [← hJ]; exact pow_padicValNat_dvd
    exact dvd_trans (pow_dvd_pow 2 (Nat.min_le_left J e)) h
  have hcont := menuW_two_cont (e := e) (j := min J e) he
  have hP : ind (DLp 2 (max (capLevel 2 e) (min J e)) a b)
      ≤ (if DLp 2 (max (capLevel 2 e) (min J e)) a b ∧ 2^(min J e) ∣ contAB a b
          then (1:ℝ) else 0) := by
    by_cases h : DLp 2 (max (capLevel 2 e) (min J e)) a b
    · rw [ind_eq_one_of _ h, if_pos ⟨h, hdvd⟩]
    · rw [ind_eq_zero_of _ h]
      by_cases h2 : (DLp 2 (max (capLevel 2 e) (min J e)) a b ∧ 2^(min J e) ∣ contAB a b)
      · rw [if_pos h2]; norm_num
      · rw [if_neg h2]
  calc (10:ℝ)^6 * ((2:ℝ)^(((cubeLevel 2 e:ℝ) + ((min J e : ℕ):ℝ))/2)
        * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b))
      = ((10:ℝ)^6 * (2:ℝ)^(((cubeLevel 2 e:ℝ) + ((min J e : ℕ):ℝ))/2))
          * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b) := by ring
    _ ≤ menuW 2 e (max (capLevel 2 e) (min J e)) (min J e)
          * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b) :=
        mul_le_mul_of_nonneg_right hcont (ind_nonneg _)
    _ ≤ menuW 2 e (max (capLevel 2 e) (min J e)) (min J e)
          * (if DLp 2 (max (capLevel 2 e) (min J e)) a b
              ∧ 2^(min J e) ∣ contAB a b then (1:ℝ) else 0) :=
        mul_le_mul_of_nonneg_left hP (menuW_two_nonneg he)

/-! ### The two cases of the assembly -/

/-- If `min J e = 0` the content term is the second half of the `(T, 0)` menu entry itself. -/
private lemma case_zero (e J : ℕ) (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hj0 : min J e = 0) :
    (10:ℝ)^6 * (∑ s ∈ Finset.range (capLevel 2 e + 1),
        ind (DLp 2 s a b) * (2:ℝ)^((s:ℝ)/2))
      + (10:ℝ)^6 * ((2:ℝ)^(((cubeLevel 2 e:ℝ) + ((min J e : ℕ):ℝ))/2)
          * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b))
      ≤ ∑ s ∈ Finset.range (capLevel 2 e + 1),
          menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0) := by
  classical
  rw [hj0, Nat.cast_zero, add_zero, Nat.max_eq_left (Nat.zero_le _)]
  rw [Finset.mul_sum, Finset.sum_range_succ, Finset.sum_range_succ]
  have hrow : (∑ s ∈ Finset.range (capLevel 2 e),
        (10:ℝ)^6 * (ind (DLp 2 s a b) * (2:ℝ)^((s:ℝ)/2)))
      = ∑ s ∈ Finset.range (capLevel 2 e),
          menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Gzero_eq e s a b, menuW_two_lt (e := e) (s := s) he (Finset.mem_range.mp hs)]
    ring
  have hcap : (10:ℝ)^6 * (ind (DLp 2 (capLevel 2 e) a b) * (2:ℝ)^(((capLevel 2 e:ℕ):ℝ)/2))
      + (10:ℝ)^6 * ((2:ℝ)^(((cubeLevel 2 e:ℕ):ℝ)/2) * ind (DLp 2 (capLevel 2 e) a b))
      = menuW 2 e (capLevel 2 e) 0
          * (if DLp 2 (capLevel 2 e) a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0) := by
    rw [Gzero_eq e (capLevel 2 e) a b, menuW_two_cap he]
    ring
  rw [hrow, add_assoc, hcap]

/-- Extra menu entries (`j0 ≥ 1`) can be added to a row without double counting. -/
private lemma add_term_le (e : ℕ) (he : 13 ≤ e) (a b : Fin 3 → ℕ) {j0 : ℕ}
    (hj0 : 1 ≤ j0) (hj0e : j0 ≤ e) :
    (∑ s ∈ Finset.range (e+2),
        menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0))
      + menuW 2 e (max (capLevel 2 e) j0) j0
          * (if DLp 2 (max (capLevel 2 e) j0) a b ∧ 2^j0 ∣ contAB a b then (1:ℝ) else 0)
      ≤ ∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1),
          menuW 2 e s j * (if DLp 2 s a b ∧ 2^j ∣ contAB a b then (1:ℝ) else 0) := by
  classical
  have hs0mem : max (capLevel 2 e) j0 ∈ Finset.range (e+2) := by
    simp only [Finset.mem_range]
    have hT : capLevel 2 e ≤ e := by simp only [capLevel]; exact Nat.sub_le _ _
    omega
  have hite : (∑ s ∈ Finset.range (e+2), (if s = max (capLevel 2 e) j0 then
        menuW 2 e (max (capLevel 2 e) j0) j0
          * (if DLp 2 (max (capLevel 2 e) j0) a b ∧ 2^j0 ∣ contAB a b then (1:ℝ) else 0)
      else 0))
      = menuW 2 e (max (capLevel 2 e) j0) j0
          * (if DLp 2 (max (capLevel 2 e) j0) a b ∧ 2^j0 ∣ contAB a b
              then (1:ℝ) else 0) := by
    rw [Finset.sum_ite_eq']
    simp [hs0mem]
  rw [← hite, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun s hs => ?_)
  by_cases hss : s = max (capLevel 2 e) j0
  · rw [hss, if_pos rfl,
      ← Finset.sum_pair (f := fun j => menuW 2 e (max (capLevel 2 e) j0) j
        * (if DLp 2 (max (capLevel 2 e) j0) a b ∧ 2^j ∣ contAB a b then (1:ℝ) else 0))
        (by intro h; omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    · intro i hi _
      exact G_nonneg he a b
  · rw [if_neg hss, add_zero]
    exact Finset.single_le_sum (fun j _ => G_nonneg (s := s) (j := j) he a b)
      (a := 0) (Finset.mem_range.mpr (Nat.succ_pos e))

/-! ### The main lemma -/

theorem localFactor_lower {e J : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hJ : padicValNat 2 (contAB a b) = J) :
    (10 : ℝ) ^ 6 * ((Finset.range (capLevel 2 e + 1)).sum
        (fun s => ind (DLp 2 s a b) * (2 : ℝ) ^ ((s : ℝ) / 2)))
      + (10 : ℝ) ^ 6 * ((2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + ((min J e : ℕ) : ℝ)) / 2)
          * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b))
    ≤ localFactor 2 e a b := by
  classical
  have hrow_le : (∑ s ∈ Finset.range (capLevel 2 e + 1),
        menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0))
      ≤ ∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1),
          menuW 2 e s j * (if DLp 2 s a b ∧ 2^j ∣ contAB a b then (1:ℝ) else 0) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (Finset.sum_le_sum (fun s hs => ?_))
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      have hT : capLevel 2 e ≤ e := by simp only [capLevel]; exact Nat.sub_le _ _
      omega
    · intro i hi _
      exact G_nonneg he a b
    · exact Finset.single_le_sum (fun j _ => G_nonneg (s := s) (j := j) he a b)
        (a := 0) (Finset.mem_range.mpr (Nat.succ_pos e))
  by_cases hj0 : min J e = 0
  · have h1 := case_zero e J he a b hj0
    rw [localFactor]
    exact le_trans h1 hrow_le
  · have hj1 : 1 ≤ min J e := by omega
    have hj0e : min J e ≤ e := Nat.min_le_right J e
    rw [localFactor]
    have h1 := low_sum_le e he a b
    have h2 := cont_le e J he a b hJ
    have h3 := add_term_le e he a b (j0 := min J e) hj1 hj0e
    have h4 : (∑ s ∈ Finset.range (capLevel 2 e + 1),
          menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0))
        ≤ ∑ s ∈ Finset.range (e+2),
          menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        simp only [Finset.mem_range] at hx ⊢
        have hT : capLevel 2 e ≤ e := by simp only [capLevel]; exact Nat.sub_le _ _
        omega
      · intro i hi _
        exact G_nonneg he a b
    calc (10:ℝ)^6 * (∑ s ∈ Finset.range (capLevel 2 e + 1),
            ind (DLp 2 s a b) * (2:ℝ)^((s:ℝ)/2))
          + (10:ℝ)^6 * ((2:ℝ)^(((cubeLevel 2 e:ℝ) + ((min J e : ℕ):ℝ))/2)
              * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b))
        ≤ (∑ s ∈ Finset.range (capLevel 2 e + 1),
            menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0))
          + menuW 2 e (max (capLevel 2 e) (min J e)) (min J e)
              * (if DLp 2 (max (capLevel 2 e) (min J e)) a b ∧ 2^(min J e) ∣ contAB a b
                  then (1:ℝ) else 0) := add_le_add h1 h2
      _ ≤ (∑ s ∈ Finset.range (e+2),
            menuW 2 e s 0 * (if DLp 2 s a b ∧ 2^0 ∣ contAB a b then (1:ℝ) else 0))
          + menuW 2 e (max (capLevel 2 e) (min J e)) (min J e)
              * (if DLp 2 (max (capLevel 2 e) (min J e)) a b ∧ 2^(min J e) ∣ contAB a b
                  then (1:ℝ) else 0) := add_le_add h4 le_rfl
      _ ≤ ∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1),
          menuW 2 e s j * (if DLp 2 s a b ∧ 2^j ∣ contAB a b then (1:ℝ) else 0) := h3

end Work.LinnikBurgess.lfSmall
