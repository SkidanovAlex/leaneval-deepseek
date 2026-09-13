import Mathlib
import Submission.Commons.Combinatorics.QBinomial.exists_inclusion_exclusion_seq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow

namespace Commons.Combinatorics.QBinomial

noncomputable section

/-- The number of `i`-dimensional subspaces of `𝔽₂^r` is at most `2 ^ (i * (r - i) + i)`.
This is the specialization to `K = 𝔽₂` of
`Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow`. -/
lemma gb_pair_le_two_pow (r i : ℕ) : (gb r i : ℝ) ≤ (2 : ℝ) ^ (i * (r - i) + i) := by
  have h := Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow
    (K := ZMod 2) (V := Fin r → ZMod 2) i
  have h' : Nat.card {W : Submodule (ZMod 2) (Fin r → ZMod 2) //
      Module.finrank (ZMod 2) W = i} ≤ 2 ^ (i * (r - i) + i) := by
    simpa using h
  have hgb : gb r i = Nat.card {W : Submodule (ZMod 2) (Fin r → ZMod 2) //
      Module.finrank (ZMod 2) W = i} := rfl
  rw [hgb]
  exact_mod_cast h'

/-- Elementary bound on powers of `2`:  `2^A · 2^{-B} · 2^C ≤ 2^{-K}` as soon as
`A + C + K ≤ B`. -/
lemma gb_pair_pow_mul_inv_mul_le (A B C K : ℕ) (h : A + C + K ≤ B) :
    (2 : ℝ) ^ A * ((2 : ℝ) ^ B)⁻¹ * (2 : ℝ) ^ C ≤ ((2 : ℝ) ^ K)⁻¹ := by
  have key : (2 : ℝ) ^ A * ((2 : ℝ) ^ B)⁻¹ * (2 : ℝ) ^ C
      = (2 : ℝ) ^ (A + C) / (2 : ℝ) ^ B := by
    rw [pow_add, div_eq_mul_inv]; ring
  rw [key, div_le_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ B by positivity)]
  rw [inv_mul_eq_div, le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ K by positivity)]
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- The exponent inequality driving the estimate: for `i ≤ r ≤ d`,
`i(r-i) + i + 4i² + 2ri ≤ 7di`. -/
lemma gb_pair_exp_ineq (d r i : ℕ) (hrd : r ≤ d) (hi : i ≤ r) :
    i * (r - i) + i + 4 * i ^ 2 + 2 * (r * i) ≤ 7 * d * i := by
  have hid : i ≤ d := le_trans hi hrd
  have hsub : i * (r - i) + i * i = i * r := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hi]
  have h1 : 3 * (r * i) ≤ 3 * (d * i) :=
    Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right i hrd)
  have h2 : 3 * i ^ 2 ≤ 3 * (d * i) := by
    rw [pow_two]
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right i hid)
  have h3 : i ≤ d * i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0]; simp
    · exact Nat.le_mul_of_pos_left i (by omega)
  have h4 : i ^ 2 = i * i := pow_two i
  nlinarith [hsub]

/-- Single-term estimate: for `i ≤ r ≤ d`,
`gb r i · 2^{-7di} · 2^{4i²} ≤ ((1/4)^r)^i`. -/
lemma gb_pair_term_le (d r i : ℕ) (hrd : r ≤ d) (hi : i ≤ r) :
    (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)
      ≤ ((1 : ℝ) / 4) ^ (r * i) := by
  have hstep : (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)
      ≤ (2 : ℝ) ^ (i * (r - i) + i) * ((2 : ℝ) ^ (7 * d * i))⁻¹
        * (2 : ℝ) ^ (4 * i ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (gb_pair_le_two_pow r i) (by positivity)
  refine le_trans hstep ?_
  have hK : ((1 : ℝ) / 4) ^ (r * i) = ((2 : ℝ) ^ (2 * (r * i)))⁻¹ := by
    rw [show ((1 : ℝ) / 4) = (4 : ℝ)⁻¹ by norm_num, inv_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [hK]
  exact gb_pair_pow_mul_inv_mul_le _ _ _ _ (by have := gb_pair_exp_ineq d r i hrd hi; omega)

/-- Geometric sum bound: `∑_{i<n} c^i ≤ 1/(1-c)` for `0 ≤ c < 1`. -/
lemma gb_pair_geom_sum_range_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, c ^ i ≤ 1 / (1 - c) := by
  have hpos : 0 < 1 - c := by linarith
  have h2 : (∑ i ∈ Finset.range n, c ^ i) * (1 - c) = 1 - c ^ n := by
    calc (∑ i ∈ Finset.range n, c ^ i) * (1 - c)
        = -((∑ i ∈ Finset.range n, c ^ i) * (c - 1)) := by ring
      _ = -(c ^ n - 1) := by rw [geom_sum_mul]
      _ = 1 - c ^ n := by ring
  have h3 : (∑ i ∈ Finset.range n, c ^ i) * (1 - c) ≤ 1 := by
    rw [h2]
    have h4 : (0 : ℝ) ≤ c ^ n := by positivity
    linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- `1/(1-c) ≤ 4/3` for `c ≤ 1/4`. -/
lemma gb_pair_one_div_one_sub_le (c : ℝ) (hc : c ≤ 1 / 4) (hc1 : c < 1) :
    1 / (1 - c) ≤ 4 / 3 := by
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - c)]
  nlinarith

/-- The single-sum estimate underlying the pair estimate. -/
lemma gb_pair_sum_le_aux (d r : ℕ) (hrd : r ≤ d) :
    (∑ i ∈ Finset.range (r + 1),
        (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)) ≤ 4 / 3 := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    rw [Finset.sum_range_one, gb_zero]
    norm_num
  · have hc : ((1 : ℝ) / 4) ^ r ≤ 1 / 4 := by
      have h := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 4 by norm_num)
        (show (1 : ℝ) / 4 ≤ 1 by norm_num) hrpos
      simpa using h
    have hc0 : 0 ≤ ((1 : ℝ) / 4) ^ r := by positivity
    have hc1 : ((1 : ℝ) / 4) ^ r < 1 := by linarith
    calc (∑ i ∈ Finset.range (r + 1),
            (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2))
        ≤ ∑ i ∈ Finset.range (r + 1), (((1 : ℝ) / 4) ^ r) ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ r := by
            rw [Finset.mem_range] at hi; omega
          rw [← pow_mul]
          exact gb_pair_term_le d r i hrd hi'
      _ ≤ 1 / (1 - ((1 : ℝ) / 4) ^ r) := gb_pair_geom_sum_range_le _ hc0 hc1 _
      _ ≤ 4 / 3 := gb_pair_one_div_one_sub_le _ hc hc1

/-- The double sum with the `(0,0)` term dropped is `< 1`.

The double summand is `T i j = gb r i · gb r j · 2^{-7d(i+j)} · 2^{4i² + 4j²}`, which factors
as `T i j = a i · a j` with `a i = gb r i · 2^{-7di} · 2^{4i²}`.  Hence the full double sum is
`(∑ a)² ≤ (4/3)² = 16/9` by `gb_pair_sum_le_aux`, and the term `T 0 0 = 1` is replaced by `0`
in the target sum, leaving `< 16/9 - 1 = 7/9 < 1`. -/
theorem gb_pair_pow_sum_lt_one (d r : ℕ) (hr : r ≤ d) :
    (∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
      (if i = 0 ∧ j = 0 then 0 else (Commons.Combinatorics.QBinomial.gb r i : ℝ) *
        (Commons.Combinatorics.QBinomial.gb r j : ℝ) *
        ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) < 1 := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    norm_num
  · set s : Finset ℕ := Finset.range (r + 1) with hs
    set a : ℕ → ℝ := fun i => (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)
      with ha
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
    have hT00 : T 0 0 = 1 := by
      simp [hTdef, gb_zero]
    have hbound : (∑ i ∈ s, a i) ≤ 4 / 3 := by
      have h := gb_pair_sum_le_aux d r hr
      simpa [hs, ha] using h
    have h0 : 0 ≤ ∑ i ∈ s, a i := by
      apply Finset.sum_nonneg
      intro i _
      simp only [ha]
      positivity
    calc (∑ i ∈ s, ∑ j ∈ s, (if i = 0 ∧ j = 0 then 0 else T i j))
        = (∑ i ∈ s, a i) ^ 2 - 1 := by rw [hprod, hsplit, htotal, hT00]
      _ ≤ (4 / 3) ^ 2 - 1 := by
          have h2 : (∑ i ∈ s, a i) ^ 2 ≤ (4 / 3) ^ 2 := pow_le_pow_left₀ h0 hbound 2
          linarith
      _ < 1 := by norm_num

end

end Commons.Combinatorics.QBinomial
