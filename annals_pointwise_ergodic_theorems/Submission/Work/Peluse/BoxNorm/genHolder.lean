import Mathlib

namespace Work.Peluse.BoxNorm

/-- **AM-GM corollary.**  If `A` is a finite type of cardinality `n > 0` and `y : A → ℝ` is
nonnegative, then the product of the `y i` is bounded by the arithmetic mean of the `n`-th
powers.  This is the weighted AM-GM inequality with the uniform weights `1 / n`. -/
lemma prod_le_sum_pow {A : Type*} [Fintype A] {n : ℕ} (hcard : Fintype.card A = n) (hn : 0 < n)
    (y : A → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∏ i, y i ≤ (1 / (n : ℝ)) * ∑ i, (y i) ^ n := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    simpa using this
  have hsum : ∑ i : A, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one_div, div_self hnR]
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset A) (fun _ => 1 / (n : ℝ))
    (fun i => (y i) ^ n) (by intro i _; positivity) hsum
    (by intro i _; exact pow_nonneg (hy i) n)
  calc ∏ i, y i = ∏ i, ((y i) ^ n) ^ (1 / (n : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hy i)]
        rw [show (n : ℝ) * (1 / (n : ℝ)) = 1 by rw [mul_one_div, div_self hnR]]
        rw [Real.rpow_one]
    _ ≤ ∑ i, (1 / (n : ℝ)) * (y i) ^ n := h
    _ = (1 / (n : ℝ)) * ∑ i, (y i) ^ n := by rw [Finset.mul_sum]

/-- **Hölder with equal exponents.**  If every `y i ·` (`i : A`, `#A = n > 0`) has `n`-th power
summing to `1`, then the sum over `x` of `∏ i, y i x` is at most `1`. -/
lemma sum_prod_le_one {A ι : Type*} [Fintype A] [Fintype ι] {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 0 < n) (y : A → ι → ℝ) (hy : ∀ i x, 0 ≤ y i x)
    (h : ∀ i, ∑ x, (y i x) ^ n = 1) :
    ∑ x, ∏ i, y i x ≤ 1 := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    simpa using this
  calc ∑ x, ∏ i, y i x
      ≤ ∑ x, (1 / (n : ℝ)) * ∑ i, (y i x) ^ n :=
        Finset.sum_le_sum fun x _ => prod_le_sum_pow hcard hn (fun i => y i x) (fun i => hy i x)
    _ = (1 / (n : ℝ)) * ∑ i, ∑ x, (y i x) ^ n := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (1 / (n : ℝ)) * ∑ i, (1 : ℝ) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => h i
    _ = (1 / (n : ℝ)) * (n : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one]
    _ = 1 := div_mul_cancel₀ 1 hnR

/-- **Generalised Hölder's inequality** for `n` functions on a finite type: the sum of the
pointwise products is bounded by the product of the `L^n` norms, when the number of functions
equals the exponent. -/
lemma holder_general {A ι : Type*} [Fintype A] [Fintype ι] {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 0 < n) (f : A → ι → ℝ) (hf : ∀ i x, 0 ≤ f i x) :
    ∑ x, ∏ i, f i x ≤ ∏ i, (∑ x, (f i x) ^ n) ^ (1 / (n : ℝ)) := by
  have hnRne : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    simpa using this
  by_cases hzero : ∃ i, (∑ x, (f i x) ^ n) = 0
  · obtain ⟨i0, hi0⟩ := hzero
    have hf0 : ∀ x, f i0 x = 0 := by
      intro x
      have hle : (f i0 x) ^ n ≤ ∑ x, (f i0 x) ^ n :=
        Finset.single_le_sum (fun y _ => pow_nonneg (hf i0 y) n) (Finset.mem_univ x)
      rw [hi0] at hle
      have h0 : (f i0 x) ^ n = 0 := le_antisymm hle (pow_nonneg (hf i0 x) n)
      exact (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp hn)).mp h0
    have hL : ∑ x, ∏ i, f i x = 0 :=
      Finset.sum_eq_zero fun x _ => Finset.prod_eq_zero (Finset.mem_univ i0) (hf0 x)
    have hR : ∏ i, (∑ x, (f i x) ^ n) ^ (1 / (n : ℝ)) = 0 := by
      have hne : (1 : ℝ) / (n : ℝ) ≠ 0 := by rw [one_div]; exact inv_ne_zero hnRne
      exact Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [hi0, Real.zero_rpow hne])
    rw [hL, hR]
  · push Not at hzero
    have hSpos : ∀ i, 0 < ∑ x, (f i x) ^ n := fun i =>
      lt_of_le_of_ne (Finset.sum_nonneg fun x _ => pow_nonneg (hf i x) n) (Ne.symm (hzero i))
    have hden_pow : ∀ i, ((∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) ^ n = ∑ z, (f i z) ^ n := by
      intro i
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (hSpos i))]
      rw [show (1 / (n : ℝ)) * (n : ℝ) = 1 by rw [div_mul_cancel₀ 1 hnRne]]
      rw [Real.rpow_one]
    have hsum1 : ∀ i, ∑ x, (f i x / (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) ^ n = 1 := by
      intro i
      calc ∑ x, (f i x / (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) ^ n
          = ∑ x, (f i x) ^ n / ((∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) ^ n :=
            Finset.sum_congr rfl fun x _ => div_pow _ _ _
        _ = (∑ x, (f i x) ^ n) / ((∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) ^ n :=
            (Finset.sum_div _ _ _).symm
        _ = (∑ x, (f i x) ^ n) / (∑ x, (f i x) ^ n) := by rw [hden_pow i]
        _ = 1 := div_self (hzero i)
    have hsum_le : ∑ x, ∏ i, (f i x / (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) ≤ 1 :=
      sum_prod_le_one hcard hn _
        (fun i x => div_nonneg (hf i x) (le_of_lt (Real.rpow_pos_of_pos (hSpos i) _))) hsum1
    have hfac : ∀ x, ∏ i, f i x = (∏ i, (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ)))
        * ∏ i, (f i x / (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) := by
      intro x
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [mul_div_assoc']
      exact (mul_div_cancel_left₀ (f i x)
        (ne_of_gt (Real.rpow_pos_of_pos (hSpos i) _))).symm
    calc ∑ x, ∏ i, f i x
        = ∑ x, (∏ i, (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ)))
            * ∏ i, (f i x / (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) :=
          Finset.sum_congr rfl fun x _ => hfac x
      _ = (∏ i, (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ)))
            * ∑ x, ∏ i, (f i x / (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ (∏ i, (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hsum_le
            (Finset.prod_nonneg fun i _ => le_of_lt (Real.rpow_pos_of_pos (hSpos i) _))
      _ = ∏ i, (∑ z, (f i z) ^ n) ^ (1 / (n : ℝ)) := mul_one _

theorem genHolder {t : ℕ} {X : Type*} [Fintype X] (a : (Fin t → Bool) → X → ℝ)
    (ha : ∀ ω x, 0 ≤ a ω x) :
    ∑ x, ∏ ω : Fin t → Bool, a ω x
      ≤ ∏ ω : Fin t → Bool, (∑ x, (a ω x) ^ (2 ^ t)) ^ (1 / (2 : ℝ) ^ t) := by
  have hcard : Fintype.card (Fin t → Bool) = 2 ^ t := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hn : 0 < 2 ^ t := pow_pos (by norm_num) t
  have hm := holder_general hcard hn a ha
  simpa [Nat.cast_pow, Nat.cast_ofNat] using hm

end Work.Peluse.BoxNorm
