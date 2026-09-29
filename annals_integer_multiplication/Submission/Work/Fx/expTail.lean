import Mathlib

namespace Work.Fx

/-- Key factorial estimate, iterated form of `Nat.factorial_mul_pow_le_factorial`:
`m! (m+1)^m (2m)^{2m} (4m)^{4m} ≤ (8m)!`. -/
lemma factorial_eight_ge (m : ℕ) :
    m.factorial * (m+1)^m * (2*m)^(2*m) * (4*m)^(4*m) ≤ (8*m).factorial := by
  have hA : m.factorial * (m+1)^m ≤ (2*m).factorial := by
    have h := Nat.factorial_mul_pow_le_factorial (m := m) (n := m)
    simpa [two_mul] using h
  have hB : (2*m).factorial * (2*m+1)^(2*m) ≤ (4*m).factorial := by
    have h := Nat.factorial_mul_pow_le_factorial (m := 2*m) (n := 2*m)
    have e : 2*m + 2*m = 4*m := by ring
    simpa [e] using h
  have hC : (4*m).factorial * (4*m+1)^(4*m) ≤ (8*m).factorial := by
    have h := Nat.factorial_mul_pow_le_factorial (m := 4*m) (n := 4*m)
    have e : 4*m + 4*m = 8*m := by ring
    simpa [e] using h
  calc m.factorial * (m+1)^m * (2*m)^(2*m) * (4*m)^(4*m)
      ≤ (2*m).factorial * (2*m)^(2*m) * (4*m)^(4*m) := by gcongr
    _ ≤ (2*m).factorial * (2*m+1)^(2*m) * (4*m)^(4*m) := by
        gcongr
        exact Nat.le_succ _
    _ ≤ (4*m).factorial * (4*m)^(4*m) := by gcongr
    _ ≤ (4*m).factorial * (4*m+1)^(4*m) := by
        gcongr
        exact Nat.le_succ _
    _ ≤ (8*m).factorial := hC

/-- Consequence of `factorial_eight_ge`: `2^{52 m} ≤ (8m)!` for `m ≥ 64`, because
`(m+1)^m ≥ 2^{6m}`, `(2m)^{2m} ≥ 2^{14m}` and `(4m)^{4m} ≥ 2^{32m}`. -/
lemma fact_mul_pow (m : ℕ) (hm : 64 ≤ m) : (2:ℕ)^(52*m) ≤ (8*m).factorial := by
  have h1 : (2:ℕ)^(6*m) ≤ (m+1)^m := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by omega : (2:ℕ)^6 ≤ m+1) m
  have h2 : (2:ℕ)^(14*m) ≤ (2*m)^(2*m) := by
    have heq : (2:ℕ)^(14*m) = ((2:ℕ)^7)^(2*m) := by
      rw [show ((2:ℕ)^7)^(2*m) = (2:ℕ)^(7*(2*m)) from (pow_mul 2 7 (2*m)).symm]
      congr 1
      ring
    rw [heq]
    exact Nat.pow_le_pow_left (by omega : (2:ℕ)^7 ≤ 2*m) (2*m)
  have h3 : (2:ℕ)^(32*m) ≤ (4*m)^(4*m) := by
    have heq : (2:ℕ)^(32*m) = ((2:ℕ)^8)^(4*m) := by
      rw [show ((2:ℕ)^8)^(4*m) = (2:ℕ)^(8*(4*m)) from (pow_mul 2 8 (4*m)).symm]
      congr 1
      ring
    rw [heq]
    exact Nat.pow_le_pow_left (by omega : (2:ℕ)^8 ≤ 4*m) (4*m)
  have he : (2:ℕ)^(52*m) = (2:ℕ)^(6*m) * 2^(14*m) * 2^(32*m) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have hprod : (2:ℕ)^(6*m) * 2^(14*m) * 2^(32*m)
      ≤ (m+1)^m * (2*m)^(2*m) * (4*m)^(4*m) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hstep : (m+1)^m * (2*m)^(2*m) * (4*m)^(4*m) ≤ (8*m).factorial := by
    have hfac := factorial_eight_ge m
    have hmf : (m+1)^m ≤ m.factorial * (m+1)^m :=
      le_mul_of_one_le_left (Nat.zero_le _) (Nat.factorial_pos m)
    exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmf)) hfac
  exact le_trans (le_of_eq he) (le_trans hprod hstep)

/-- `2^{41 p + 66} ≤ (8(p+1)+1)!` for `p ≥ 100`. This is the numerical core of the
exponential-tail estimate: `2 * 32^{8(p+1)+1} * 2^{p+20} = 2^{41p+66}`. -/
lemma fact_bound (p : ℕ) (hp : 100 ≤ p) :
    (2:ℕ)^(41*p+66) ≤ (8*(p+1)+1).factorial := by
  have h1 : (2:ℕ)^(52*(p+1)) ≤ (8*(p+1)).factorial := fact_mul_pow (p+1) (by omega)
  have h2 : (2:ℕ)^(41*p+66) ≤ (2:ℕ)^(52*(p+1)) := by
    apply Nat.pow_le_pow_right (show (0:ℕ) < 2 by norm_num)
    omega
  have h3 : (8*(p+1)).factorial ≤ (8*(p+1)+1).factorial := Nat.factorial_le (by omega)
  exact le_trans h2 (le_trans h1 h3)

/-- The Taylor remainder of `exp` after `8(p+1)+1` terms is at most `2^{-(p+20)}`
for `‖z‖ ≤ 32` and `p ≥ 100`. -/
theorem expTail (z : ℂ) (p : ℕ) (hp : 100 ≤ p) (hz : ‖z‖ ≤ 32) :
    ‖Complex.exp z - ∑ k ∈ Finset.range (8 * (p + 1) + 1), z ^ k / (k.factorial : ℂ)‖ ≤
      1 / (2 : ℝ) ^ (p + 20) := by
  have hx : ‖z‖ / (((8 * (p + 1) + 1).succ : ℕ) : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (((8*(p+1)+1).succ : ℕ) : ℝ))]
    have h32 : (32:ℝ) ≤ (1/2) * (((8*(p+1)+1).succ : ℕ) : ℝ) := by
      have hpR : (100:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      push_cast
      linarith
    linarith
  refine (Complex.exp_bound' (x := z) (n := 8*(p+1)+1) hx).trans ?_
  have hNpos : (0:ℝ) < ((8*(p+1)+1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (8*(p+1)+1)
  have h2pos : (0:ℝ) < (2:ℝ)^(p+20) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hNpos, div_mul_eq_mul_div, one_mul, le_div_iff₀ h2pos]
  have hzpow : ‖z‖ ^ (8*(p+1)+1) ≤ (32:ℝ)^(8*(p+1)+1) :=
    pow_le_pow_left₀ (norm_nonneg z) hz _
  have hpoweq : (32:ℝ)^(8*(p+1)+1) * 2 * (2:ℝ)^(p+20) = (2:ℝ)^(41*p+66) := by
    have hL : (32:ℝ)^(8*(p+1)+1) * 2 * (2:ℝ)^(p+20)
        = (2:ℝ)^(5*(8*(p+1)+1)) * (2:ℝ)^1 * (2:ℝ)^(p+20) := by
      rw [show (32:ℝ) = (2:ℝ)^5 by norm_num,
          (pow_mul (2:ℝ) 5 (8*(p+1)+1)).symm, pow_one]
    rw [hL, ← pow_add, ← pow_add]
    congr 1
    ring
  have hfac : (2:ℝ)^(41*p+66) ≤ ((8*(p+1)+1).factorial : ℝ) := by
    exact_mod_cast fact_bound p hp
  calc ‖z‖ ^ (8*(p+1)+1) * 2 * (2:ℝ)^(p+20)
      ≤ (32:ℝ)^(8*(p+1)+1) * 2 * (2:ℝ)^(p+20) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzpow (by norm_num)) (by positivity)
    _ = (2:ℝ)^(41*p+66) := hpoweq
    _ ≤ ((8*(p+1)+1).factorial : ℝ) := hfac

end Work.Fx
