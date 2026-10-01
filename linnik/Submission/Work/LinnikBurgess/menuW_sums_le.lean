import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-! ### Auxiliary real-power estimates -/

private lemma rpow_div_natCast_le_one {x : ℝ} (hx : 1 ≤ x) {a : ℝ} {n : ℕ} (h : a ≤ (n:ℝ)) :
    x ^ a / x ^ n ≤ 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [← Real.rpow_natCast x n]
  exact (div_le_one (Real.rpow_pos_of_pos hx0 _)).mpr (Real.rpow_le_rpow_of_exponent_le hx h)

private lemma mul_rpow_div_natCast_le {x : ℝ} (hx : 1 ≤ x) {a : ℝ} {n : ℕ} {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (h : a ≤ (n:ℝ)) : c * x ^ a / x ^ n ≤ d := by
  have h1 := rpow_div_natCast_le_one hx h
  have hmul : c * x ^ a / x ^ n = c * (x ^ a / x ^ n) := by rw [mul_div_assoc]
  rw [hmul]
  calc c * (x ^ a / x ^ n) ≤ c * 1 := by gcongr
    _ = c := by ring
    _ ≤ d := hcd

private lemma rpow_div_natCast_le_rpow {x : ℝ} (hx : 1 ≤ x) {a : ℝ} {n : ℕ} {c : ℝ}
    (h : a - (n:ℝ) ≤ c) : x ^ a / x ^ n ≤ x ^ c := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [← Real.rpow_natCast x n, ← Real.rpow_sub hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-! ### Unfolding lemmas for `menuW` -/

private lemma menuW_odd_zero {p e s : ℕ} (h5 : 5 ≤ p) :
    menuW p e s 0 = (if s < capLevel p e then 4 * (p:ℝ)^((s:ℝ)/2)
      else if s = capLevel p e then 7 * (p:ℝ)^((capLevel p e:ℝ)/2)
      else if s = capLevel p e + 1 then 60 * (p:ℝ)^((e:ℝ)/6) else 0) := by
  rw [menuW, if_pos h5]
  simp

private lemma menuW_odd_pos {p e s j : ℕ} (h5 : 5 ≤ p) (hj : j ≠ 0) :
    menuW p e s j = (if s = max (capLevel p e) j then
      7 * ((e:ℝ)+1) * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) else 0) := by
  rw [menuW, if_pos h5, if_neg hj]

private lemma menuW_small_le12 {p e s j : ℕ} (h5 : ¬ 5 ≤ p) (he12 : e ≤ 12) :
    menuW p e s j = (if s = 0 ∧ j = 0 then 729 else 0) := by
  rw [menuW, if_neg h5, if_pos he12]

private lemma menuW_small_gt12 {p e s j : ℕ} (h5 : ¬ 5 ≤ p) (he12 : ¬ e ≤ 12) :
    menuW p e s j =
      (if j = 0 ∧ s ≤ capLevel p e then (10:ℝ)^6 * (p:ℝ)^((s:ℝ)/2) else 0)
      + (if s = max (capLevel p e) j then
          (10:ℝ)^6 * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) else 0) := by
  rw [menuW, if_neg h5, if_neg he12]

private lemma cubeLevel_two (e : ℕ) : cubeLevel 2 e = (e+3)/3 := by simp [cubeLevel]
private lemma cubeLevel_three (e : ℕ) : cubeLevel 3 e = (e+2)/3 := by simp [cubeLevel]

/-! ### The `5 ≤ p` case: the two inner sums -/

private lemma menuW_odd_inner_succ {p e k : ℕ} (h5 : 5 ≤ p) (he : 2 ≤ e) (hk : k < e) :
    (∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(s+(k+1))) ≤ 7*((e:ℝ)+1) := by
  have hP1 : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hp2 : p ≠ 2 := by omega
  have h3m : 3*cubeLevel p e ≤ e+2 := by
    have h : cubeLevel p e = (e+2)/3 := by simp only [cubeLevel]; rw [if_neg hp2]
    omega
  have hTm : capLevel p e + 2*cubeLevel p e = e := by
    have h2m : 2*cubeLevel p e ≤ e := by
      have h : cubeLevel p e = (e+2)/3 := by simp only [cubeLevel]; rw [if_neg hp2]
      omega
    simp only [capLevel]; omega
  have hE : ((cubeLevel p e:ℝ) + ((k+1:ℕ):ℝ))/2
      ≤ (((max (capLevel p e) (k+1) + (k+1) : ℕ)) : ℝ) := by
    have hnat : cubeLevel p e + (k+1) ≤ 2 * max (capLevel p e) (k+1) + 2 * (k+1) := by omega
    have hreal : ((cubeLevel p e : ℝ) + ((k+1 : ℕ) : ℝ))
        ≤ 2 * ((max (capLevel p e) (k+1) : ℕ) : ℝ) + 2 * ((k+1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hcast : (((max (capLevel p e) (k+1) + (k+1) : ℕ)) : ℝ)
        = ((max (capLevel p e) (k+1) : ℕ) : ℝ) + ((k+1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    linarith
  have hM : max (capLevel p e) (k+1) ∈ Finset.range (e+2) := by
    simp only [Finset.mem_range]
    have h1 : capLevel p e ≤ e := by simp only [capLevel]; omega
    have h2 : k+1 ≤ e := by omega
    omega
  have hnn : (0:ℝ) ≤ 7*((e:ℝ)+1) := by positivity
  calc (∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(s+(k+1)))
      ≤ ∑ s ∈ Finset.range (e+2),
          (if s = max (capLevel p e) (k+1) then 7*((e:ℝ)+1) else 0) := by
        apply Finset.sum_le_sum
        intro s hs
        by_cases hse : s = max (capLevel p e) (k+1)
        · rw [hse, menuW_odd_pos h5 (by omega : k+1 ≠ 0)]
          simp only [if_true]
          exact mul_rpow_div_natCast_le hP1 hnn le_rfl hE
        · rw [menuW_odd_pos h5 (by omega : k+1 ≠ 0)]
          simp [hse]
    _ = 7*((e:ℝ)+1) := by
        rw [Finset.sum_ite_eq']
        simp only [hM, if_true]

private lemma menuW_odd_inner_zero {p e : ℕ} (h5 : 5 ≤ p) (he : 2 ≤ e) :
    (∑ s ∈ Finset.range (e+2), menuW p e s 0 / (p:ℝ)^(s+0)) ≤ 60*((e:ℝ)+2) := by
  have hP1 : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hp2 : p ≠ 2 := by omega
  have hTm : capLevel p e + 2*cubeLevel p e = e := by
    have h2m : 2*cubeLevel p e ≤ e := by
      have h : cubeLevel p e = (e+2)/3 := by simp only [cubeLevel]; rw [if_neg hp2]
      omega
    simp only [capLevel]; omega
  have hN4 : (e:ℝ)/6 ≤ (capLevel p e : ℝ) + 1 := by
    have h1 : 12*cubeLevel p e ≤ 5*e+6 := by
      have h : cubeLevel p e = (e+2)/3 := by simp only [cubeLevel]; rw [if_neg hp2]
      omega
    have h2 : (12:ℝ)*cubeLevel p e ≤ 5*e + 6 := by exact_mod_cast h1
    have hTe : (capLevel p e : ℝ) + 2*cubeLevel p e = e := by exact_mod_cast hTm
    linarith
  have hsT : (capLevel p e : ℝ)/2 ≤ (capLevel p e : ℝ) := by
    have h : (0:ℝ) ≤ (capLevel p e : ℝ) := by positivity
    linarith
  have hpt : ∀ s : ℕ, menuW p e s 0 / (p:ℝ)^(s+0) ≤ 60 := by
    intro s
    have hss : (s:ℝ)/2 ≤ (s:ℝ) := by
      have h : (0:ℝ) ≤ (s:ℝ) := by positivity
      linarith
    rw [menuW_odd_zero h5]
    simp only [Nat.add_zero]
    split_ifs with h1 h2 h3
    · exact mul_rpow_div_natCast_le hP1 (by norm_num) (by norm_num) hss
    · subst h2
      exact mul_rpow_div_natCast_le hP1 (by norm_num) (by norm_num) hsT
    · subst h3
      refine mul_rpow_div_natCast_le hP1 (by norm_num) (by norm_num) ?_
      simpa using hN4
    · simp
  calc (∑ s ∈ Finset.range (e+2), menuW p e s 0 / (p:ℝ)^(s+0))
      ≤ ∑ s ∈ Finset.range (e+2), (60:ℝ) := Finset.sum_le_sum (fun s _ => hpt s)
    _ = 60*((e:ℝ)+2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

private lemma menuW_odd_inner2_succ {p e k : ℕ} (h5 : 5 ≤ p) (he : 2 ≤ e) (hk : k < e) :
    (∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(k+1))
      ≤ 7*((e:ℝ)+1) * (p:ℝ)^((e:ℝ)/6) := by
  have hP1 : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hp2 : p ≠ 2 := by omega
  have h3m : 3*cubeLevel p e ≤ e+2 := by
    have h : cubeLevel p e = (e+2)/3 := by simp only [cubeLevel]; rw [if_neg hp2]
    omega
  have hM : max (capLevel p e) (k+1) ∈ Finset.range (e+2) := by
    simp only [Finset.mem_range]
    have h1 : capLevel p e ≤ e := by simp only [capLevel]; omega
    have h2 : k+1 ≤ e := by omega
    omega
  have hexp : ((cubeLevel p e:ℝ) + ((k+1:ℕ):ℝ))/2 - ((k+1:ℕ):ℝ) ≤ (e:ℝ)/6 := by
    have h3m' : (3:ℝ)*cubeLevel p e ≤ e+2 := by exact_mod_cast h3m
    have hk1 : (0:ℝ) ≤ (k:ℝ) := by positivity
    push_cast
    linarith
  have hnn : (0:ℝ) ≤ 7*((e:ℝ)+1) := by positivity
  calc (∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(k+1))
      ≤ ∑ s ∈ Finset.range (e+2),
          (if s = max (capLevel p e) (k+1) then 7*((e:ℝ)+1)*(p:ℝ)^((e:ℝ)/6) else 0) := by
        apply Finset.sum_le_sum
        intro s hs
        by_cases hse : s = max (capLevel p e) (k+1)
        · rw [hse, menuW_odd_pos h5 (by omega : k+1 ≠ 0)]
          simp only [if_true]
          have h1 : (p:ℝ)^(((cubeLevel p e:ℝ)+((k+1:ℕ):ℝ))/2) / (p:ℝ)^(k+1) ≤ (p:ℝ)^((e:ℝ)/6) :=
            rpow_div_natCast_le_rpow hP1 hexp
          calc 7*((e:ℝ)+1) * (p:ℝ)^(((cubeLevel p e:ℝ)+((k+1:ℕ):ℝ))/2) / (p:ℝ)^(k+1)
              = 7*((e:ℝ)+1) * ((p:ℝ)^(((cubeLevel p e:ℝ)+((k+1:ℕ):ℝ))/2) / (p:ℝ)^(k+1)) := by
                rw [mul_div_assoc]
            _ ≤ 7*((e:ℝ)+1) * (p:ℝ)^((e:ℝ)/6) := by
                apply mul_le_mul_of_nonneg_left h1 hnn
        · rw [menuW_odd_pos h5 (by omega : k+1 ≠ 0)]
          simp [hse]
    _ = 7*((e:ℝ)+1) * (p:ℝ)^((e:ℝ)/6) := by
        rw [Finset.sum_ite_eq']
        simp only [hM, if_true]

private lemma menuW_odd_inner2_zero {p e : ℕ} (h5 : 5 ≤ p) (he : 2 ≤ e) :
    (∑ s ∈ Finset.range (e+2), menuW p e s 0 / (p:ℝ)^0)
      ≤ 60*((e:ℝ)+2)*(p:ℝ)^((e:ℝ)/6) := by
  have hP1 : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hp2 : p ≠ 2 := by omega
  have he3m : e ≤ 3*cubeLevel p e := by
    have h : cubeLevel p e = (e+2)/3 := by simp only [cubeLevel]; rw [if_neg hp2]
    omega
  have hTm : capLevel p e + 2*cubeLevel p e = e := by
    have h2m : 2*cubeLevel p e ≤ e := by
      have h : cubeLevel p e = (e+2)/3 := by simp only [cubeLevel]; rw [if_neg hp2]
      omega
    simp only [capLevel]; omega
  have hT6 : (capLevel p e : ℝ)/2 ≤ (e:ℝ)/6 := by
    have h1 : (e:ℝ) ≤ 3*cubeLevel p e := by exact_mod_cast he3m
    have h2 : (capLevel p e : ℝ) + 2*cubeLevel p e = e := by exact_mod_cast hTm
    linarith
  have hnonneg : (0:ℝ) ≤ (p:ℝ)^((e:ℝ)/6) := Real.rpow_nonneg (by positivity) _
  have hpt : ∀ s : ℕ, menuW p e s 0 / (p:ℝ)^0 ≤ 60*(p:ℝ)^((e:ℝ)/6) := by
    intro s
    rw [menuW_odd_zero h5]
    simp only [pow_zero, div_one]
    split_ifs with h1 h2 h3
    · have hle : (p:ℝ)^((s:ℝ)/2) ≤ (p:ℝ)^((e:ℝ)/6) := by
        apply Real.rpow_le_rpow_of_exponent_le hP1
        have hs : (s:ℝ) < (capLevel p e : ℝ) := by exact_mod_cast h1
        linarith
      linarith
    · subst h2
      have hle : (p:ℝ)^((capLevel p e:ℝ)/2) ≤ (p:ℝ)^((e:ℝ)/6) :=
        Real.rpow_le_rpow_of_exponent_le hP1 hT6
      linarith
    · subst h3
      linarith
    · positivity
  calc (∑ s ∈ Finset.range (e+2), menuW p e s 0 / (p:ℝ)^0)
      ≤ ∑ _s ∈ Finset.range (e+2), 60*(p:ℝ)^((e:ℝ)/6) := Finset.sum_le_sum (fun s _ => hpt s)
    _ = 60*((e:ℝ)+2)*(p:ℝ)^((e:ℝ)/6) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-! ### The `p ≤ 3` case: pointwise bounds -/

private lemma menuW_small_le12_div1 {p e s j : ℕ} (_hp : p.Prime) (h5 : ¬ 5 ≤ p) (he12 : e ≤ 12) :
    menuW p e s j / (p:ℝ)^(s+j) ≤ 729 := by
  rw [menuW_small_le12 h5 he12]
  by_cases h : s = 0 ∧ j = 0
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    simp

private lemma menuW_small_le12_div2 {p e s j : ℕ} (_hp : p.Prime) (h5 : ¬ 5 ≤ p) (he12 : e ≤ 12) :
    menuW p e s j / (p:ℝ)^j ≤ 729 := by
  rw [menuW_small_le12 h5 he12]
  by_cases h : s = 0 ∧ j = 0
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    simp

private lemma menuW_small_gt12_div1 {p e s j : ℕ} (hp : p.Prime) (h5 : ¬ 5 ≤ p) (he : 13 ≤ e) :
    menuW p e s j / (p:ℝ)^(s+j) ≤ (10:ℝ)^6 * (1 + p) := by
  have hp23 : p = 2 ∨ p = 3 := by
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      have h2 : 2 ≤ p := hp.two_le
      omega
  have hP1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hTm : capLevel p e + 2*cubeLevel p e = e := by
    rcases hp23 with rfl | rfl
    · have h : 2*cubeLevel 2 e ≤ e := by rw [cubeLevel_two]; omega
      simp only [capLevel]; omega
    · have h : 2*cubeLevel 3 e ≤ e := by rw [cubeLevel_three]; omega
      simp only [capLevel]; omega
  have hF3 : 5*cubeLevel p e ≤ 2*e+2 := by
    rcases hp23 with rfl | rfl
    · rw [cubeLevel_two]; omega
    · rw [cubeLevel_three]; omega
  rw [menuW_small_gt12 h5 (by omega : ¬ e ≤ 12), add_div]
  have hA : (if j = 0 ∧ s ≤ capLevel p e then (10:ℝ)^6 * (p:ℝ)^((s:ℝ)/2) else 0)
      / (p:ℝ)^(s+j) ≤ (10:ℝ)^6 := by
    by_cases h : j = 0 ∧ s ≤ capLevel p e
    · rw [if_pos h]
      obtain ⟨hj0, hsT⟩ := h
      subst hj0
      have hs0 : (0:ℝ) ≤ (s:ℝ) := by positivity
      have hexp : (s:ℝ)/2 ≤ ((s+0:ℕ):ℝ) := by push_cast; linarith
      exact mul_rpow_div_natCast_le hP1 (by positivity) le_rfl hexp
    · rw [if_neg h]; simp
  have hB : (if s = max (capLevel p e) j then
        (10:ℝ)^6 * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) else 0)
      / (p:ℝ)^(s+j) ≤ (10:ℝ)^6 * p := by
    by_cases hse : s = max (capLevel p e) j
    · rw [if_pos hse]
      have hEmax : ((cubeLevel p e:ℝ)+(j:ℝ))/2 ≤ ((s:ℝ) + (j:ℝ)) + 1 := by
        rw [hse]
        push_cast
        have hmax : (capLevel p e : ℝ) ≤ max (capLevel p e : ℝ) (j:ℝ) := le_max_left _ _
        have hF3' : (5:ℝ)*cubeLevel p e ≤ 2*e + 2 := by exact_mod_cast hF3
        have hTe : (capLevel p e : ℝ) + 2*cubeLevel p e = e := by exact_mod_cast hTm
        have hj0 : (0:ℝ) ≤ (j:ℝ) := by positivity
        nlinarith
      have hexp : ((cubeLevel p e:ℝ)+(j:ℝ))/2 - ((s+j:ℕ):ℝ) ≤ 1 := by
        push_cast; linarith
      have h1 : (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) / (p:ℝ)^(s+j) ≤ (p:ℝ)^(1:ℝ) :=
        rpow_div_natCast_le_rpow hP1 hexp
      rw [Real.rpow_one] at h1
      calc (10:ℝ)^6 * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) / (p:ℝ)^(s+j)
          = (10:ℝ)^6 * ((p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) / (p:ℝ)^(s+j)) := by
            rw [mul_div_assoc]
        _ ≤ (10:ℝ)^6 * (p:ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    · rw [if_neg hse]; simp
  calc (if j = 0 ∧ s ≤ capLevel p e then (10:ℝ)^6 * (p:ℝ)^((s:ℝ)/2) else 0) / (p:ℝ)^(s+j)
        + (if s = max (capLevel p e) j then
            (10:ℝ)^6 * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) else 0) / (p:ℝ)^(s+j)
      ≤ (10:ℝ)^6 + (10:ℝ)^6 * p := add_le_add hA hB
    _ = (10:ℝ)^6 * (1 + p) := by ring

private lemma menuW_small_gt12_div2 {p e s j : ℕ} (hp : p.Prime) (h5 : ¬ 5 ≤ p) (he : 13 ≤ e) :
    menuW p e s j / (p:ℝ)^j ≤ 4 * (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) := by
  have hp23 : p = 2 ∨ p = 3 := by
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      have h2 : 2 ≤ p := hp.two_le
      omega
  have hP1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hP3 : (p:ℝ) ≤ 3 := by rcases hp23 with rfl | rfl <;> norm_num
  have hTm : capLevel p e + 2*cubeLevel p e = e := by
    rcases hp23 with rfl | rfl
    · have h : 2*cubeLevel 2 e ≤ e := by rw [cubeLevel_two]; omega
      simp only [capLevel]; omega
    · have h : 2*cubeLevel 3 e ≤ e := by rw [cubeLevel_three]; omega
      simp only [capLevel]; omega
  have he3m : e ≤ 3*cubeLevel p e := by
    rcases hp23 with rfl | rfl
    · rw [cubeLevel_two]; omega
    · rw [cubeLevel_three]; omega
  have h3m3 : 3*cubeLevel p e ≤ e+3 := by
    rcases hp23 with rfl | rfl
    · rw [cubeLevel_two]; omega
    · rw [cubeLevel_three]; omega
  have hT6 : (capLevel p e : ℝ)/2 ≤ (e:ℝ)/6 := by
    have h1 : (e:ℝ) ≤ 3*cubeLevel p e := by exact_mod_cast he3m
    have h2 : (capLevel p e : ℝ) + 2*cubeLevel p e = e := by exact_mod_cast hTm
    linarith
  rw [menuW_small_gt12 h5 (by omega : ¬ e ≤ 12), add_div]
  have hA : (if j = 0 ∧ s ≤ capLevel p e then (10:ℝ)^6 * (p:ℝ)^((s:ℝ)/2) else 0)
      / (p:ℝ)^j ≤ (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) := by
    by_cases h : j = 0 ∧ s ≤ capLevel p e
    · rw [if_pos h]
      obtain ⟨hj0, hsT⟩ := h
      subst hj0
      simp only [pow_zero, div_one]
      have hsT' : (s:ℝ) ≤ (capLevel p e : ℝ) := by exact_mod_cast hsT
      have hle1 : (p:ℝ)^((s:ℝ)/2) ≤ (p:ℝ)^((capLevel p e:ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
      have hle2 : (p:ℝ)^((capLevel p e:ℝ)/2) ≤ (p:ℝ)^((e:ℝ)/6) :=
        Real.rpow_le_rpow_of_exponent_le hP1 hT6
      calc (10:ℝ)^6 * (p:ℝ)^((s:ℝ)/2) ≤ (10:ℝ)^6 * (p:ℝ)^((capLevel p e:ℝ)/2) :=
              mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ ≤ (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) := mul_le_mul_of_nonneg_left hle2 (by positivity)
    · rw [if_neg h]; simp only [zero_div]; positivity
  have hB : (if s = max (capLevel p e) j then
        (10:ℝ)^6 * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) else 0)
      / (p:ℝ)^j ≤ 3 * (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) := by
    by_cases hse : s = max (capLevel p e) j
    · rw [if_pos hse]
      have hm2 : (cubeLevel p e : ℝ)/2 ≤ (e:ℝ)/6 + 1/2 := by
        have h3 : (3:ℝ)*cubeLevel p e ≤ e+3 := by exact_mod_cast h3m3
        linarith
      have hstep1 : (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) / (p:ℝ)^j ≤ (p:ℝ)^((cubeLevel p e:ℝ)/2) := by
        apply rpow_div_natCast_le_rpow hP1
        have hj : (0:ℝ) ≤ (j:ℝ) := by positivity
        linarith
      have hstep2 : (p:ℝ)^((cubeLevel p e:ℝ)/2) ≤ 3 * (p:ℝ)^((e:ℝ)/6) := by
        have hP0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hP1
        calc (p:ℝ)^((cubeLevel p e:ℝ)/2) ≤ (p:ℝ)^((e:ℝ)/6 + 1/2) :=
                Real.rpow_le_rpow_of_exponent_le hP1 hm2
          _ = (p:ℝ)^((e:ℝ)/6) * (p:ℝ)^(1/2) := Real.rpow_add hP0 _ _
          _ ≤ (p:ℝ)^((e:ℝ)/6) * (p:ℝ)^(1:ℝ) := by
                apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
                exact Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
          _ = (p:ℝ)^((e:ℝ)/6) * (p:ℝ) := by rw [Real.rpow_one]
          _ ≤ (p:ℝ)^((e:ℝ)/6) * 3 := by
                apply mul_le_mul_of_nonneg_left hP3 (Real.rpow_nonneg (by positivity) _)
          _ = 3 * (p:ℝ)^((e:ℝ)/6) := by ring
      calc (10:ℝ)^6 * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) / (p:ℝ)^j
          = (10:ℝ)^6 * ((p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) / (p:ℝ)^j) := by rw [mul_div_assoc]
        _ ≤ (10:ℝ)^6 * (p:ℝ)^((cubeLevel p e:ℝ)/2) := mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ ≤ (10:ℝ)^6 * (3 * (p:ℝ)^((e:ℝ)/6)) := mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ = 3 * (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) := by ring
    · rw [if_neg hse]; simp only [zero_div]; positivity
  calc (if j = 0 ∧ s ≤ capLevel p e then (10:ℝ)^6 * (p:ℝ)^((s:ℝ)/2) else 0) / (p:ℝ)^j
        + (if s = max (capLevel p e) j then
            (10:ℝ)^6 * (p:ℝ)^(((cubeLevel p e:ℝ)+(j:ℝ))/2) else 0) / (p:ℝ)^j
      ≤ (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) + 3 * (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) := add_le_add hA hB
    _ = 4 * (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) := by ring

/-! ### The main theorem -/

/-- **U12 — Lemma M: the per-prime menu sums** (`BURGESS_ROUTE_LEAD.md` §4.4).  For a prime `p` and
`e ≥ 2`, with the menu weights `Work.LinnikBurgess.menuW p e s j` of `burgess_lead_defs`,

`Σ_{s<e+2} Σ_{j<e+1} menuW p e s j / p^(s+j) ≤ 10^8 (e+1)²`  and
`Σ_{s<e+2} Σ_{j<e+1} menuW p e s j / p^j ≤ 10^8 (e+1)² p^(e/6)`.

A reviewer replicated the weights in Python for every prime `p ≤ 59` and `2 ≤ e ≤ 1999`: the
tightest ratio is `≈ 2.3·10⁴` and `≈ 3.0·10⁴` (worst at `p = 2, e = 13`), i.e. ~4000× inside the
stated `10^8`.  The lead hand-checked the exponents in §4.4 (all exponents `≤ 0` in the first sum;
in the second `p^{T/2}, p^{(m−1)/2} ≤ p^{e/6}` with `m = ⌈e/3⌉`, `T = e − 2m`; for `p ≤ 3` the extra
powers are `≤ 3^{O(1)}`, absorbed by the `10^6` constants).  Needed for the final assembly U13. -/
theorem menuW_sums_le {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
        Work.LinnikBurgess.menuW p e s j / (p : ℝ) ^ (s + j)) ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2
    ∧ (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
        Work.LinnikBurgess.menuW p e s j / (p : ℝ) ^ j)
        ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 * (p : ℝ) ^ ((e : ℝ) / 6) := by
  by_cases h5 : 5 ≤ p
  · -- Case `5 ≤ p`
    constructor
    · have hz := menuW_odd_inner_zero (p:=p) (e:=e) h5 he
      have hk : ∀ k ∈ Finset.range e,
          (∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(s+(k+1))) ≤ 7*((e:ℝ)+1) :=
        fun k hk => menuW_odd_inner_succ (p:=p) (e:=e) h5 he (Finset.mem_range.mp hk)
      calc (∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1), menuW p e s j / (p:ℝ)^(s+j))
          = ∑ j ∈ Finset.range (e+1), ∑ s ∈ Finset.range (e+2), menuW p e s j / (p:ℝ)^(s+j) :=
            Finset.sum_comm
        _ = (∑ k ∈ Finset.range e,
              ∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(s+(k+1)))
            + (∑ s ∈ Finset.range (e+2), menuW p e s 0 / (p:ℝ)^(s+0)) :=
            Finset.sum_range_succ' (fun j => ∑ s ∈ Finset.range (e+2), menuW p e s j / (p:ℝ)^(s+j)) e
        _ ≤ (e:ℝ)*(7*((e:ℝ)+1)) + 60*((e:ℝ)+2) := by
            apply add_le_add
            · calc (∑ k ∈ Finset.range e,
                    ∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(s+(k+1)))
                  ≤ ∑ _k ∈ Finset.range e, (7*((e:ℝ)+1)) := Finset.sum_le_sum hk
                _ = (e:ℝ)*(7*((e:ℝ)+1)) := by
                    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            · exact hz
        _ ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 := by
            have he2 : (2:ℝ) ≤ e := by exact_mod_cast he
            nlinarith [sq_nonneg ((e:ℝ)+1)]
    · have hz := menuW_odd_inner2_zero (p:=p) (e:=e) h5 he
      have hk : ∀ k ∈ Finset.range e,
          (∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(k+1))
            ≤ 7*((e:ℝ)+1) * (p:ℝ)^((e:ℝ)/6) :=
        fun k hk => menuW_odd_inner2_succ (p:=p) (e:=e) h5 he (Finset.mem_range.mp hk)
      calc (∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1), menuW p e s j / (p:ℝ)^j)
          = ∑ j ∈ Finset.range (e+1), ∑ s ∈ Finset.range (e+2), menuW p e s j / (p:ℝ)^j :=
            Finset.sum_comm
        _ = (∑ k ∈ Finset.range e,
              ∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(k+1))
            + (∑ s ∈ Finset.range (e+2), menuW p e s 0 / (p:ℝ)^0) :=
            Finset.sum_range_succ' (fun j => ∑ s ∈ Finset.range (e+2), menuW p e s j / (p:ℝ)^j) e
        _ ≤ (e:ℝ)*(7*((e:ℝ)+1) * (p:ℝ)^((e:ℝ)/6))
            + 60*((e:ℝ)+2)*(p:ℝ)^((e:ℝ)/6) := by
            apply add_le_add
            · calc (∑ k ∈ Finset.range e,
                    ∑ s ∈ Finset.range (e+2), menuW p e s (k+1) / (p:ℝ)^(k+1))
                  ≤ ∑ _k ∈ Finset.range e, (7*((e:ℝ)+1) * (p:ℝ)^((e:ℝ)/6)) :=
                    Finset.sum_le_sum hk
                _ = (e:ℝ)*(7*((e:ℝ)+1) * (p:ℝ)^((e:ℝ)/6)) := by
                    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            · exact hz
        _ ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 * (p : ℝ) ^ ((e : ℝ) / 6) := by
            have he2 : (2:ℝ) ≤ e := by exact_mod_cast he
            have hX : (0:ℝ) < (p:ℝ)^((e:ℝ)/6) := Real.rpow_pos_of_pos (by positivity) _
            have hbase : (e:ℝ)*(7*((e:ℝ)+1)) + 60*((e:ℝ)+2) ≤ 10^8 * ((e:ℝ)+1)^2 := by
              nlinarith [sq_nonneg ((e:ℝ)+1)]
            nlinarith [mul_le_mul_of_nonneg_right hbase (le_of_lt hX)]
  · -- Case `¬ 5 ≤ p`
    have hp23 : p = 2 ∨ p = 3 := by
      rcases hp.eq_two_or_odd with h | h
      · exact Or.inl h
      · right
        have h2 : 2 ≤ p := hp.two_le
        omega
    have hP1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hP3 : (p:ℝ) ≤ 3 := by rcases hp23 with rfl | rfl <;> norm_num
    by_cases he12 : e ≤ 12
    · -- Case `e ≤ 12`
      constructor
      · calc (∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1), menuW p e s j / (p:ℝ)^(s+j))
            ≤ ∑ _s ∈ Finset.range (e+2), ∑ _j ∈ Finset.range (e+1), (729:ℝ) := by
              apply Finset.sum_le_sum; intro s hs
              apply Finset.sum_le_sum; intro j hj
              exact menuW_small_le12_div1 hp h5 he12
          _ = 729*((e:ℝ)+2)*((e:ℝ)+1) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
          _ ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 := by
              have he2 : (2:ℝ) ≤ e := by exact_mod_cast he
              nlinarith [sq_nonneg ((e:ℝ)+1)]
      · calc (∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1), menuW p e s j / (p:ℝ)^j)
            ≤ ∑ _s ∈ Finset.range (e+2), ∑ _j ∈ Finset.range (e+1), (729:ℝ) := by
              apply Finset.sum_le_sum; intro s hs
              apply Finset.sum_le_sum; intro j hj
              exact menuW_small_le12_div2 hp h5 he12
          _ = 729*((e:ℝ)+2)*((e:ℝ)+1) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
          _ ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 * (p : ℝ) ^ ((e : ℝ) / 6) := by
              have he2 : (2:ℝ) ≤ e := by exact_mod_cast he
              have hX : (1:ℝ) ≤ (p:ℝ)^((e:ℝ)/6) := Real.one_le_rpow hP1 (by positivity)
              nlinarith [sq_nonneg ((e:ℝ)+1)]
    · -- Case `13 ≤ e`
      have he13 : 13 ≤ e := by omega
      constructor
      · calc (∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1), menuW p e s j / (p:ℝ)^(s+j))
            ≤ ∑ _s ∈ Finset.range (e+2), ∑ _j ∈ Finset.range (e+1),
                ((10:ℝ)^6 * (1 + p)) := by
              apply Finset.sum_le_sum; intro s hs
              apply Finset.sum_le_sum; intro j hj
              exact menuW_small_gt12_div1 hp h5 he13
          _ = (10:ℝ)^6 * (1 + p) * ((e:ℝ)+2) * ((e:ℝ)+1) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
          _ ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 := by
              have he2 : (2:ℝ) ≤ e := by exact_mod_cast he
              nlinarith [sq_nonneg ((e:ℝ)+1)]
      · calc (∑ s ∈ Finset.range (e+2), ∑ j ∈ Finset.range (e+1), menuW p e s j / (p:ℝ)^j)
            ≤ ∑ _s ∈ Finset.range (e+2), ∑ _j ∈ Finset.range (e+1),
                (4 * (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6)) := by
              apply Finset.sum_le_sum; intro s hs
              apply Finset.sum_le_sum; intro j hj
              exact menuW_small_gt12_div2 hp h5 he13
          _ = 4 * (10:ℝ)^6 * (p:ℝ)^((e:ℝ)/6) * ((e:ℝ)+2) * ((e:ℝ)+1) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
          _ ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 * (p : ℝ) ^ ((e : ℝ) / 6) := by
              have he2 : (2:ℝ) ≤ e := by exact_mod_cast he
              have hX : (0:ℝ) < (p:ℝ)^((e:ℝ)/6) := Real.rpow_pos_of_pos (by positivity) _
              have hbase : 4 * (10:ℝ)^6 * ((e:ℝ)+2) * ((e:ℝ)+1) ≤ 10^8 * ((e:ℝ)+1)^2 := by
                nlinarith [sq_nonneg ((e:ℝ)+1)]
              nlinarith [mul_le_mul_of_nonneg_right hbase (le_of_lt hX)]

end Work.LinnikBurgess
