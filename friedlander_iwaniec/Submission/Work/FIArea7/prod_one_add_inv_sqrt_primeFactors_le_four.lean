import Mathlib

namespace Work.FIArea7

/-- For a prime `p ≠ 2` (hence `p ≥ 3`), the elementary bound `1 + 1/√p ≤ √p`. -/
private lemma one_add_inv_sqrt_le_sqrt_of_prime_ne_two {p : ℕ} (hp : Nat.Prime p)
    (h2 : p ≠ 2) : 1 + 1 / Real.sqrt (p : ℝ) ≤ Real.sqrt (p : ℝ) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    have : 3 ≤ p := by
      have h2le := hp.two_le
      omega
    exact_mod_cast this
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos_of_pos hppos
  -- `√p ≤ p - 1`, since `p ≤ (p-1)^2`
  have hsle : Real.sqrt (p : ℝ) ≤ (p : ℝ) - 1 := by
    rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)]
    nlinarith [sq_nonneg ((p : ℝ) - 2), hp3]
  have hkey : (1 : ℝ) ≤ Real.sqrt (p : ℝ) * (Real.sqrt (p : ℝ) - 1) := by
    have : Real.sqrt (p : ℝ) * (Real.sqrt (p : ℝ) - 1) = (p : ℝ) - Real.sqrt (p : ℝ) := by
      rw [mul_sub, mul_one, ← sq, Real.sq_sqrt hppos.le]
    rw [this]; linarith
  have hdiv : 1 / Real.sqrt (p : ℝ) ≤ Real.sqrt (p : ℝ) - 1 := by
    rw [div_le_iff₀ hspos]
    nlinarith [hkey]
  linarith

/-- `1 + 1/√2 ≤ 2`. -/
private lemma one_add_inv_sqrt_two_le_two : 1 + 1 / Real.sqrt (2 : ℝ) ≤ 2 := by
  have hspos : (0 : ℝ) < Real.sqrt (2 : ℝ) := Real.sqrt_pos_of_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ Real.sqrt (2 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have : 1 / Real.sqrt (2 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hspos]; linarith
  linarith

/-- The numerical core: `√(4dq) ≤ 2·d·√q` for `d ≥ 1`. -/
private lemma sqrt_four_mul_le (d q : ℕ) (hd : 1 ≤ d) :
    Real.sqrt (((4 * d * q : ℕ)) : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt (q : ℝ) := by
  have hcast : (((4 * d * q : ℕ)) : ℝ) = 4 * (d : ℝ) * (q : ℝ) := by push_cast; ring
  rw [hcast]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hy : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt (q : ℝ) := by positivity
  rw [Real.sqrt_le_left hy]
  have h3 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hprod : (0 : ℝ) ≤ 4 * (d : ℝ) * (q : ℝ) * ((d : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hdnn) hqnn) h3
  have heq : (2 * (d : ℝ) * Real.sqrt (q : ℝ)) ^ 2 = 4 * ((d : ℝ) ^ 2) * (q : ℝ) := by
    rw [show (2 * (d : ℝ) * Real.sqrt (q : ℝ)) = 2 * ((d : ℝ) * Real.sqrt (q : ℝ)) by ring]
    rw [mul_pow, mul_pow, Real.sq_sqrt hqnn]; ring
  rw [heq]; nlinarith [hprod]

/-- For `1 ≤ d`, `1 ≤ q`: `∏_{p ∣ 4dq} (1 + 1/√p) ≤ 4·d·√q`.

Proof: let `P = (4 * d * q).primeFactors` and `R = ∏ p ∈ P, p` (the radical), so
`R ∣ 4*d*q` with `4*d*q ≠ 0`, hence `R ≤ 4*d*q` (`Nat.le_of_dvd`).  Every `p ∈ P` is prime.
Case on `2 ∈ P`:
- if `2 ∉ P` then every `p ∈ P` is an odd prime, so `p ≥ 3` and `1 + 1/√p ≤ √p`
  (from `√p * √p = p`, `√p ≥ 0`, `p ≥ 3`); hence the product is `≤ ∏_{p∈P} √p = √R`
  (`Real.sqrt_prod`), and `√R ≤ √(4dq) = 2√(dq) ≤ 4 d √q`.
- if `2 ∈ P` then `P = insert 2 Q` with `Q = P.erase 2`; the factor at `2` is `≤ 2` (as `√2 ≥ 1`),
  the other factors are `≤ √p`, so the product is `≤ 2·∏_{p ∈ Q}√p ≤ 2·∏_{p∈P}√p = 2√R`
  (the extra `√2 ≥ 1` factor is harmless), and again `2√R ≤ 4 d √q`. -/
theorem prod_one_add_inv_sqrt_primeFactors_le_four (d q : ℕ) (hd : 1 ≤ d) (hq : 1 ≤ q) :
    ∏ p ∈ (4 * d * q).primeFactors, (1 + 1 / Real.sqrt (p : ℝ))
      ≤ 4 * (d : ℝ) * Real.sqrt (q : ℝ) := by
  set P : Finset ℕ := (4 * d * q).primeFactors with hPdef
  have h4dq_pos : 0 < 4 * d * q :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  -- the radical divides `4dq`, hence is `≤ 4dq`
  have hRle : (∏ p ∈ P, p) ≤ 4 * d * q := by
    rw [hPdef]
    exact Nat.le_of_dvd h4dq_pos (Nat.prod_primeFactors_dvd _)
  -- the product of the square roots is the square root of the radical
  have hsqrt_prod : ∏ p ∈ P, Real.sqrt (p : ℝ) = Real.sqrt (((∏ p ∈ P, p) : ℕ) : ℝ) := by
    rw [← Real.sqrt_prod P (fun p _ => Nat.cast_nonneg p)]
    congr 1
    exact (Finset.prod_natCast P (fun p => p)).symm
  have hRleR : Real.sqrt (((∏ p ∈ P, p) : ℕ) : ℝ) ≤ Real.sqrt (((4 * d * q : ℕ)) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hRle
  have hsq4 : Real.sqrt (((4 * d * q : ℕ)) : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt (q : ℝ) :=
    sqrt_four_mul_le d q hd
  have hdq_nonneg : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt (q : ℝ) :=
    mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _)
  -- nonnegativity of the factors
  have hnn : ∀ p ∈ P, (0 : ℝ) ≤ 1 + 1 / Real.sqrt (p : ℝ) := by
    intro p _
    have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := div_nonneg zero_le_one (Real.sqrt_nonneg _)
    linarith
  by_cases h2P : 2 ∈ P
  · -- case `2 ∈ P`
    have hsplit : ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ))
        = (1 + 1 / Real.sqrt (2 : ℝ)) * ∏ p ∈ P.erase 2, (1 + 1 / Real.sqrt (p : ℝ)) := by
      conv_lhs => rw [← Finset.insert_erase h2P]
      rw [Finset.prod_insert (by simp : (2 : ℕ) ∉ P.erase 2)]
      norm_num
    have hfac2 : ∏ p ∈ P.erase 2, (1 + 1 / Real.sqrt (p : ℝ))
        ≤ ∏ p ∈ P.erase 2, Real.sqrt (p : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := div_nonneg zero_le_one (Real.sqrt_nonneg _)
        linarith
      · intro p hp
        have hmem := Finset.mem_erase.mp hp
        have hpP : p ∈ P := hmem.2
        have hne : p ≠ 2 := hmem.1
        have hprime : Nat.Prime p := (Nat.mem_primeFactors.mp (hPdef ▸ hpP)).1
        exact one_add_inv_sqrt_le_sqrt_of_prime_ne_two hprime hne
    have hfac3 : ∏ p ∈ P.erase 2, Real.sqrt (p : ℝ) ≤ ∏ p ∈ P, Real.sqrt (p : ℝ) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.erase_subset 2 P)
      · intro p _; exact Real.sqrt_nonneg _
      · intro p hpP hpnotmem
        have hp2 : p = 2 := by
          by_contra h
          exact hpnotmem (Finset.mem_erase.mpr ⟨h, hpP⟩)
        subst hp2
        exact Real.one_le_sqrt.mpr (by norm_num)
    have hfacQ_nn : (0 : ℝ) ≤ ∏ p ∈ P.erase 2, (1 + 1 / Real.sqrt (p : ℝ)) :=
      Finset.prod_nonneg (fun p _ => by
        have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := div_nonneg zero_le_one (Real.sqrt_nonneg _)
        linarith)
    calc ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ))
        = (1 + 1 / Real.sqrt (2 : ℝ)) * ∏ p ∈ P.erase 2, (1 + 1 / Real.sqrt (p : ℝ)) :=
          hsplit
      _ ≤ 2 * ∏ p ∈ P.erase 2, Real.sqrt (p : ℝ) :=
          mul_le_mul one_add_inv_sqrt_two_le_two hfac2 hfacQ_nn (by norm_num)
      _ ≤ 2 * ∏ p ∈ P, Real.sqrt (p : ℝ) :=
          mul_le_mul_of_nonneg_left hfac3 (by norm_num)
      _ = 2 * Real.sqrt (((∏ p ∈ P, p) : ℕ) : ℝ) := by rw [hsqrt_prod]
      _ ≤ 2 * Real.sqrt (((4 * d * q : ℕ)) : ℝ) :=
          mul_le_mul_of_nonneg_left hRleR (by norm_num)
      _ ≤ 4 * (d : ℝ) * Real.sqrt (q : ℝ) := by
          nlinarith [hsq4, hdq_nonneg]
  · -- case `2 ∉ P`
    have hfac : ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ)) ≤ ∏ p ∈ P, Real.sqrt (p : ℝ) := by
      apply Finset.prod_le_prod₀ hnn
      intro p hp
      have hpP : p ∈ (4 * d * q).primeFactors := hPdef ▸ hp
      have hprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpP).1
      have hne : p ≠ 2 := fun h => h2P (h ▸ hp)
      exact one_add_inv_sqrt_le_sqrt_of_prime_ne_two hprime hne
    calc ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ))
        ≤ ∏ p ∈ P, Real.sqrt (p : ℝ) := hfac
      _ = Real.sqrt (((∏ p ∈ P, p) : ℕ) : ℝ) := hsqrt_prod
      _ ≤ Real.sqrt (((4 * d * q : ℕ)) : ℝ) := hRleR
      _ ≤ 4 * (d : ℝ) * Real.sqrt (q : ℝ) := by
          nlinarith [hsq4, hdq_nonneg]

end Work.FIArea7
