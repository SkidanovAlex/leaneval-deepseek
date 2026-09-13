import Mathlib
import Submission.Commons.Combinatorics.QBinomial.gb_pair_pow_sum_lt_one
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_one_zmod_two

namespace Commons.Combinatorics.QBinomial

noncomputable section

open Finset

/-- The number of lines in `𝔽₂^r` is `2^r - 1`. -/
lemma gb_one (r : ℕ) : gb r 1 = 2 ^ r - 1 := by
  unfold gb
  have h := Commons.LinearAlgebra.Submodule.card_submodule_finrank_one_zmod_two
    (V := Fin r → ZMod 2)
  rw [Module.finrank_fintype_fun_eq_card (ZMod 2) (η := Fin r), Fintype.card_fin] at h
  exact h

/-- Term bound: for `1 ≤ i ≤ d` and `r ≤ 2d`, the `i`-th summand
`gb r i · 2^{-7di} · 2^{4i²}` is at most `(2^{2d-1})^{-i}`. -/
lemma gb_pair_a_term_le (d r i : ℕ) (hr : r ≤ 2 * d) (hd : 1 ≤ d) (_hi : 1 ≤ i)
    (hid : i ≤ d) :
    (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)
      ≤ ((2 : ℝ) ^ (i * (2 * d - 1)))⁻¹ := by
  rcases le_or_gt i r with hir | hri
  · have hkey : i * (r - i) + i + 4 * i ^ 2 + i * (2 * d - 1) ≤ 7 * d * i := by
      have ha : i * (r - i) + 4 * i ^ 2 ≤ 5 * d * i := by
        have h1 : i * (r - i) ≤ i * (2 * d - i) :=
          Nat.mul_le_mul_left i (Nat.sub_le_sub_right hr i)
        have h2' : i * (2 * d - i) = 2 * d * i - i * i := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_comm i (2 * d)]
        have h3 : i * i ≤ 2 * d * i := by
          have hile : i ≤ 2 * d := by omega
          calc i * i ≤ i * (2 * d) := Nat.mul_le_mul_left i hile
            _ = 2 * d * i := by ring
        have h4 : 3 * (i * i) ≤ 3 * (d * i) :=
          Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right i hid)
        calc i * (r - i) + 4 * i ^ 2 = i * (r - i) + 4 * (i * i) := by ring
          _ ≤ i * (2 * d - i) + 4 * (i * i) := by gcongr
          _ = (2 * d * i - i * i) + 4 * (i * i) := by rw [h2']
          _ = 2 * d * i + 3 * (i * i) := by omega
          _ ≤ 2 * d * i + 3 * (d * i) := by omega
          _ = 5 * d * i := by ring
      have hii : i ≤ 2 * d * i := Nat.le_mul_of_pos_left i (by omega)
      have h2 : i * (2 * d - 1) = 2 * d * i - i := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm i (2 * d)]
      have hre : i * (r - i) + i + 4 * i ^ 2 + i * (2 * d - 1)
          = (i * (r - i) + 4 * i ^ 2) + (i + i * (2 * d - 1)) := by ac_rfl
      rw [hre, h2, Nat.add_sub_of_le hii]
      calc (i * (r - i) + 4 * i ^ 2) + 2 * d * i ≤ 5 * d * i + 2 * d * i :=
            Nat.add_le_add_right ha _
        _ = 7 * d * i := by ring
    have hstep : (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)
        ≤ (2 : ℝ) ^ (i * (r - i) + i) * ((2 : ℝ) ^ (7 * d * i))⁻¹
          * (2 : ℝ) ^ (4 * i ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (gb_pair_le_two_pow r i) (by positivity)
    exact le_trans hstep (gb_pair_pow_mul_inv_mul_le _ _ _ _ hkey)
  · have hz : gb r i = 0 := gb_eq_zero_of_lt r i hri
    rw [hz]
    simp only [Nat.cast_zero, zero_mul]
    positivity

/-- Sum bound: for `r ≤ 2d`, `∑_{i=0}^{d} gb r i · 2^{-7di} · 2^{4i²} ≤ 11/8`. -/
lemma gb_pair_a_sum_le (d r : ℕ) (hr : r ≤ 2 * d) :
    (∑ i ∈ Finset.range (d + 1),
        (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)) ≤ 11 / 8 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · rw [hd0, Finset.sum_range_one, gb_zero]
    norm_num
  · rcases lt_or_eq_of_le (by omega : 1 ≤ d) with hd2 | hd1
    · rw [Finset.sum_range_succ']
      set q : ℝ := ((2 : ℝ) ^ (2 * d - 1))⁻¹ with hq
      have hqe : ∀ n, q ^ n = ((2 : ℝ) ^ (n * (2 * d - 1)))⁻¹ := by
        intro n
        rw [hq, inv_pow]
        congr 1
        rw [← pow_mul, Nat.mul_comm (2 * d - 1) n]
      have hqge0 : 0 ≤ q := by rw [hq]; positivity
      have hqle : q ≤ 1 / 8 := by
        rw [hq]
        have h3 : 3 ≤ 2 * d - 1 := by omega
        have hp : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (2 * d - 1) := pow_le_pow_right₀ (by norm_num) h3
        calc ((2 : ℝ) ^ (2 * d - 1))⁻¹ ≤ ((2 : ℝ) ^ 3)⁻¹ :=
              (inv_le_inv₀ (by positivity) (by positivity)).mpr hp
          _ = 1 / 8 := by norm_num
      have hq1 : q < 1 := by linarith
      have hgeom : (∑ k ∈ Finset.range d, q ^ k) ≤ (1 - q)⁻¹ := by
        have := gb_pair_geom_sum_range_le q hqge0 hq1 d
        simpa [one_div] using this
      have hqinv : (1 - q)⁻¹ ≤ 2 := by
        have hhalf : (1 : ℝ) / 2 ≤ 1 - q := by linarith
        calc (1 - q)⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ :=
              (inv_le_inv₀ (by positivity) (by positivity)).mpr hhalf
          _ = 2 := by norm_num
      have hsumq : (∑ k ∈ Finset.range d, q ^ (k + 1)) ≤ 1 / 4 := by
        have h1 : (∑ k ∈ Finset.range d, q ^ (k + 1)) = q * ∑ k ∈ Finset.range d, q ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ, mul_comm])
        rw [h1]
        calc q * ∑ k ∈ Finset.range d, q ^ k ≤ q * (1 - q)⁻¹ :=
              mul_le_mul_of_nonneg_left hgeom hqge0
          _ ≤ (1 / 8) * 2 := mul_le_mul hqle hqinv (by positivity) (by norm_num)
          _ = 1 / 4 := by norm_num
      have hf0 : (gb r 0 : ℝ) * ((2 : ℝ) ^ (7 * d * 0))⁻¹ * (2 : ℝ) ^ (4 * 0 ^ 2) = 1 := by
        rw [gb_zero]; norm_num
      rw [hf0]
      have hsum_le : (∑ k ∈ Finset.range d,
            (gb r (k + 1) : ℝ) * ((2 : ℝ) ^ (7 * d * (k + 1)))⁻¹
              * (2 : ℝ) ^ (4 * (k + 1) ^ 2)) ≤ 1 / 4 := by
        refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) hsumq
        have hk' : k < d := Finset.mem_range.mp hk
        have h1 : 1 ≤ k + 1 := by omega
        have h2 : k + 1 ≤ d := by omega
        have h := gb_pair_a_term_le d r (k + 1) hr (by omega) h1 h2
        rwa [← hqe (k + 1)] at h
      linarith
    · rw [← hd1, Finset.sum_range_succ, Finset.sum_range_one, gb_zero]
      have hgb1 : gb r 1 ≤ 3 := by
        rw [gb_one]
        have hr2 : r ≤ 2 := by omega
        have hp : 2 ^ r ≤ 4 := by
          simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hr2
        omega
      have hfirst : ((1 : ℕ) : ℝ) * ((2 : ℝ) ^ (7 * 1 * 0))⁻¹ * (2 : ℝ) ^ (4 * 0 ^ 2) = 1 := by
        norm_num
      rw [hfirst]
      have hsecond : (gb r 1 : ℝ) * ((2 : ℝ) ^ (7 * 1 * 1))⁻¹ * (2 : ℝ) ^ (4 * 1 ^ 2)
          ≤ 3 / 8 := by
        have h3 : (gb r 1 : ℝ) ≤ 3 := by exact_mod_cast hgb1
        calc (gb r 1 : ℝ) * ((2 : ℝ) ^ (7 * 1 * 1))⁻¹ * (2 : ℝ) ^ (4 * 1 ^ 2)
            ≤ 3 * ((2 : ℝ) ^ (7 * 1 * 1))⁻¹ * (2 : ℝ) ^ (4 * 1 ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = 3 / 8 := by norm_num
      linarith

/-- The double sum with the `(0,0)` term dropped is `< 1`, under `r ≤ 2d`.

Writing `a i = gb r i · 2^{-7di} · 2^{4i²}` and `T i j = a i · a j`, the double sum over
`i, j ∈ {0,…,d}` equals `(∑ a)² - a 0² = (∑ a)² - 1`.  The single sum `∑ a` is at most `11/8`,
whence the double sum is at most `(11/8)² - 1 = 57/64 < 1`. -/
theorem gb_pair_pow_sum_lt_one_of_le_two_mul (d r : ℕ) (hr : r ≤ 2 * d) :
    (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
      (if i = 0 ∧ j = 0 then 0 else (Commons.Combinatorics.QBinomial.gb r i : ℝ) * (Commons.Combinatorics.QBinomial.gb r j : ℝ) *
        ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) < 1 := by
  classical
  set s : Finset ℕ := Finset.range (d + 1) with hs
  set a : ℕ → ℝ := fun i => (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2) with ha
  set T : ℕ → ℕ → ℝ := fun i j => (gb r i : ℝ) * (gb r j : ℝ) *
    ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2) with hTdef
  have hT : ∀ i j, T i j = a i * a j := by
    intro i j
    simp only [hTdef, ha]
    rw [show 7 * d * (i + j) = 7 * d * i + 7 * d * j by ring, pow_add, pow_add, mul_inv]
    ring
  have hcond : ∀ p : ℕ × ℕ, (p.1 = 0 ∧ p.2 = 0) ↔ p = (0, 0) := by
    intro p; constructor
    · intro h; exact Prod.ext h.1 h.2
    · intro h; rw [h]; simp
  have hmem : (0, 0) ∈ s ×ˢ s := by simp [hs]
  have hprod : (∑ i ∈ s, ∑ j ∈ s, (if i = 0 ∧ j = 0 then 0 else T i j))
      = ∑ p ∈ s ×ˢ s, (if p.1 = 0 ∧ p.2 = 0 then 0 else T p.1 p.2) := by
    simpa using (Finset.sum_product s s
      (fun p : ℕ × ℕ => if p.1 = 0 ∧ p.2 = 0 then 0 else T p.1 p.2)).symm
  have hextract :
      (∑ p ∈ s ×ˢ s, (if p.1 = 0 ∧ p.2 = 0 then T p.1 p.2 else 0)) = T 0 0 := by
    have h1 : (∑ p ∈ s ×ˢ s, (if p.1 = 0 ∧ p.2 = 0 then T p.1 p.2 else 0))
        = ∑ p ∈ s ×ˢ s, (if p = (0, 0) then T p.1 p.2 else 0) :=
      Finset.sum_congr rfl (fun p _ => by
        by_cases h : p.1 = 0 ∧ p.2 = 0
        · have hp0 : p = (0, 0) := (hcond p).mp h
          rw [if_pos h, if_pos hp0]
        · have hp0 : ¬ (p = (0, 0)) := fun hh => h ((hcond p).mpr hh)
          rw [if_neg h, if_neg hp0])
    rw [h1, Finset.sum_ite_eq' (s ×ˢ s) (0, 0) (fun p => T p.1 p.2), if_pos hmem]
  have hsplit : (∑ p ∈ s ×ˢ s, (if p.1 = 0 ∧ p.2 = 0 then 0 else T p.1 p.2))
      = (∑ p ∈ s ×ˢ s, T p.1 p.2) - T 0 0 := by
    rw [← hextract, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.1 = 0 ∧ p.2 = 0 <;> simp [h]
  have htotal : (∑ p ∈ s ×ˢ s, T p.1 p.2) = (∑ i ∈ s, a i) ^ 2 := by
    have h1 : (∑ p ∈ s ×ˢ s, T p.1 p.2) = ∑ i ∈ s, ∑ j ∈ s, T i j := by
      simpa using (Finset.sum_product s s (fun p : ℕ × ℕ => T p.1 p.2))
    have h2 : (∑ i ∈ s, ∑ j ∈ s, T i j) = ∑ i ∈ s, ∑ j ∈ s, a i * a j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hT i j
    rw [h1, h2, ← Finset.sum_mul_sum, sq]
  have hT00 : T 0 0 = 1 := by simp [hTdef, gb_zero]
  have hbound : (∑ i ∈ s, a i) ≤ 11 / 8 := by
    have h := gb_pair_a_sum_le d r hr
    simpa [hs, ha] using h
  have h0 : 0 ≤ ∑ i ∈ s, a i := by
    apply Finset.sum_nonneg
    intro i _
    simp only [ha]
    positivity
  calc (∑ i ∈ s, ∑ j ∈ s, (if i = 0 ∧ j = 0 then 0 else T i j))
      = (∑ i ∈ s, a i) ^ 2 - 1 := by rw [hprod, hsplit, htotal, hT00]
    _ ≤ (11 / 8) ^ 2 - 1 := by
        have h2 : (∑ i ∈ s, a i) ^ 2 ≤ (11 / 8) ^ 2 := pow_le_pow_left₀ h0 hbound 2
        linarith
    _ < 1 := by norm_num

end

end Commons.Combinatorics.QBinomial
