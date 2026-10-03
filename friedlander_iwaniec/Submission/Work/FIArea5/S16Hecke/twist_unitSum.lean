/-
# `Work.FIArea5.S16Hecke.twist_unitSum`

The twist `twist χ m = χ · twistChar χ m` of a character `χ` modulo `4d` by the character
`ν(z) = (primaryUnit z)^{-j}`, `j = twistExp χ m`, has **unit sum** `4`:

  `unitSum (twist χ m) m = Σ_{u ∈ μ₄} (χ·ν)(u) u^m = 4 ≠ 0`.

This is the reduction of the `unitSum χ m = 0` case of the theta transformation to the
non-degenerate case: `χ(i)^4 = 1`, and `j` is chosen so that `χ(i)·i^m = i^j`; hence for each unit
`u = i^k` (`k ≤ 3`) the summand is

  `χ(u)·u^{-j}·u^m = (χ(i)i^m i^{-j})^k = 1^k = 1`.

The only `ℤ[i]`-arithmetic input is `primaryUnit u = u` for `u ∈ μ₄` (the four units are pairwise
incongruent modulo `(1+i)³ = -2+2i`, whose norm `8` exceeds the norms `2, 4` of the differences
`u - v`), and `isOddG u`, both proved here by a norm argument.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Norm calculus for divisibility in `ℤ[i]` -/

/-- If `a ≠ 0` divides `z ≠ 0` then the norm of `a` divides the norm of `z`; in particular
`|a|² ≤ |z|²`. -/
lemma natAbs_norm_le_of_dvd {a z : GaussianInt} (h : a ∣ z) (hz : z ≠ 0) :
    a.norm.natAbs ≤ z.norm.natAbs := by
  obtain ⟨c, rfl⟩ := h
  have hc : c ≠ 0 := by rintro rfl; simp at hz
  have hcn : c.norm.natAbs ≠ 0 := by
    intro h0
    exact hc ((GaussianInt.norm_eq_zero).mp (Int.natAbs_eq_zero.mp h0))
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  calc a.norm.natAbs = a.norm.natAbs * 1 := by ring
    _ ≤ a.norm.natAbs * c.norm.natAbs := by
        exact Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hcn)

/-- A non-zero `z` whose norm is smaller than the norm of `a` is not divisible by `a`. -/
lemma not_dvd_of_natAbs_norm_lt {a z : GaussianInt} (hz : z ≠ 0)
    (h : z.norm.natAbs < a.norm.natAbs) : ¬ a ∣ z := by
  intro hd
  have := natAbs_norm_le_of_dvd hd hz
  omega

lemma c3_norm_natAbs : c3.norm.natAbs = 8 := by decide

lemma oneAddI_norm_natAbs : oneAddI.norm.natAbs = 2 := by decide

/-- `(1+i)³ = -2+2i` has norm `8`. -/
lemma not_dvd_c3 {z : GaussianInt} (hz : z ≠ 0) (h : z.norm.natAbs < 8) : ¬ c3 ∣ z :=
  not_dvd_of_natAbs_norm_lt hz (by rw [c3_norm_natAbs]; exact h)

/-- `1+i` has norm `2`, so it divides no unit. -/
lemma not_dvd_oneAddI {z : GaussianInt} (hz : z ≠ 0) (h : z.norm.natAbs < 2) :
    ¬ oneAddI ∣ z :=
  not_dvd_of_natAbs_norm_lt hz (by rw [oneAddI_norm_natAbs]; exact h)

/-! ## 2. `primaryUnit` and `isOddG` on the four units -/

lemma primaryUnit_one : primaryUnit (1 : GaussianInt) = 1 := by simp [primaryUnit]

lemma primaryUnit_neg_one : primaryUnit (-1 : GaussianInt) = -1 := by
  have h1 : ¬ c3 ∣ ((-1 : GaussianInt) - 1) := not_dvd_c3 (by decide) (by decide)
  have h2 : c3 ∣ ((-1 : GaussianInt) + 1) := by simp
  simp only [primaryUnit, if_neg h1, if_pos h2]

lemma primaryUnit_I : primaryUnit (⟨0,1⟩ : GaussianInt) = ⟨0,1⟩ := by
  have h1 : ¬ c3 ∣ ((⟨0,1⟩ : GaussianInt) - 1) := not_dvd_c3 (by decide) (by decide)
  have h2 : ¬ c3 ∣ ((⟨0,1⟩ : GaussianInt) + 1) := not_dvd_c3 (by decide) (by decide)
  have h3 : c3 ∣ ((⟨0,1⟩ : GaussianInt) - (⟨0,1⟩ : GaussianInt)) := by simp
  simp only [primaryUnit, if_neg h1, if_neg h2, if_pos h3]

lemma primaryUnit_neg_I : primaryUnit (⟨0,-1⟩ : GaussianInt) = ⟨0,-1⟩ := by
  have h1 : ¬ c3 ∣ ((⟨0,-1⟩ : GaussianInt) - 1) := not_dvd_c3 (by decide) (by decide)
  have h2 : ¬ c3 ∣ ((⟨0,-1⟩ : GaussianInt) + 1) := not_dvd_c3 (by decide) (by decide)
  have h3 : ¬ c3 ∣ ((⟨0,-1⟩ : GaussianInt) - (⟨0,1⟩ : GaussianInt)) :=
    not_dvd_c3 (by decide) (by decide)
  have h4 : c3 ∣ ((⟨0,-1⟩ : GaussianInt) + (⟨0,1⟩ : GaussianInt)) := dvd_zero c3
  simp only [primaryUnit, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  decide

lemma isOddG_one : isOddG (1 : GaussianInt) := not_dvd_oneAddI (by decide) (by decide)
lemma isOddG_neg_one : isOddG (-1 : GaussianInt) := not_dvd_oneAddI (by decide) (by decide)
lemma isOddG_I : isOddG (⟨0,1⟩ : GaussianInt) := not_dvd_oneAddI (by decide) (by decide)
lemma isOddG_neg_I : isOddG (⟨0,-1⟩ : GaussianInt) := not_dvd_oneAddI (by decide) (by decide)

lemma pow_I_two : (⟨0,1⟩ : GaussianInt) ^ 2 = -1 := by decide
lemma pow_I_three : (⟨0,1⟩ : GaussianInt) ^ 3 = (⟨0,-1⟩ : GaussianInt) := by decide

/-- **`primaryUnit` is the identity on the four units**: `μ₄ = {i^k : k < 4}` and the units are
pairwise incongruent modulo `(1+i)³`. -/
lemma primaryUnit_pow_I {k : ℕ} (hk : k < 4) :
    primaryUnit ((⟨0,1⟩ : GaussianInt) ^ k) = (⟨0,1⟩ : GaussianInt) ^ k := by
  interval_cases k
  · simp [primaryUnit]
  · simp [primaryUnit_I]
  · rw [pow_I_two, primaryUnit_neg_one]
  · rw [pow_I_three, primaryUnit_neg_I]

/-- The four units are odd. -/
lemma isOddG_pow_I {k : ℕ} (hk : k < 4) : isOddG ((⟨0,1⟩ : GaussianInt) ^ k) := by
  interval_cases k
  · simpa using isOddG_one
  · simpa using isOddG_I
  · rw [pow_I_two]; exact isOddG_neg_one
  · rw [pow_I_three]; exact isOddG_neg_I

/-! ## 3. Arithmetic of the exponent `j = twistExp χ m` -/

/-- Multiplicativity of `χ` under powers. -/
lemma chi_pow {d : ℕ} {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    (z : GaussianInt) (k : ℕ) : chi (z ^ k) = chi z ^ k := by
  induction k with
  | zero => simp [hchi.1]
  | succ k ih => rw [pow_succ', hchi.2.1, ih, pow_succ']

/-- `χ(i)` is a fourth root of unity (it lies in `μ₄`). -/
lemma chi_I_pow4 {d : ℕ} {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi) :
    chi (⟨0,1⟩ : GaussianInt) ^ 4 = 1 := by
  have h : (⟨0,1⟩ : GaussianInt) ^ 4 = 1 := by decide
  calc chi (⟨0,1⟩ : GaussianInt) ^ 4 = chi ((⟨0,1⟩ : GaussianInt) ^ 4) :=
        (chi_pow hchi _ 4).symm
    _ = chi 1 := by rw [h]
    _ = 1 := hchi.1

/-- The fourth roots of unity in `ℂ` are `1, i, -1, -i`. -/
lemma pow4_eq_one_disj (c : ℂ) (h : c ^ 4 = 1) :
    c = 1 ∨ c = Complex.I ∨ c = -1 ∨ c = -Complex.I := by
  have hfac : (c^2 - 1) * (c^2 + 1) = 0 := by linear_combination h
  have hsq : ∀ x : ℂ, (x - Complex.I) * (x + Complex.I) = x^2 + 1 := by
    intro x; ring_nf; rw [Complex.I_sq]; ring
  rcases mul_eq_zero.mp hfac with h1 | h2
  · have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · left; linear_combination h4
    · right; right; left; linear_combination h4
  · have h3 : (c - Complex.I) * (c + Complex.I) = 0 := by rw [hsq, h2]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · right; left; linear_combination h4
    · right; right; right; linear_combination h4

/-- `i` has order `4`. -/
lemma I_pow_mod4 (k : ℕ) : (Complex.I : ℂ) ^ (k % 4) = Complex.I ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

/-- **The defining property of `twistExp`**: `i^j = χ(i)·i^m`. -/
lemma I_pow_twistExp {chi : GaussianInt → ℂ} {m : ℕ} (h4 : chi (⟨0,1⟩ : GaussianInt) ^ 4 = 1) :
    (Complex.I : ℂ) ^ (twistExp chi m) = chi (⟨0,1⟩ : GaussianInt) * Complex.I ^ m := by
  have hclass := pow4_eq_one_disj _ h4
  unfold twistExp
  split_ifs with h1 h2 h3
  · rw [h1, I_pow_mod4]; ring
  · rw [h2, I_pow_mod4, pow_succ]; ring
  · rw [h3, I_pow_mod4, pow_add, Complex.I_sq]; ring
  · have hc : chi (⟨0,1⟩ : GaussianInt) = -Complex.I := by
      rcases hclass with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact h
    rw [hc, I_pow_mod4, pow_add, Complex.I_pow_three]; ring

/-- **`χ(i) = i^{j-m}`**: the equivalent form of `i^j = χ(i)i^m` used for the four summands. -/
lemma chi_I_eq_zpow {chi : GaussianInt → ℂ} {m : ℕ} (h4 : chi (⟨0,1⟩ : GaussianInt) ^ 4 = 1) :
    chi (⟨0,1⟩ : GaussianInt) = (Complex.I : ℂ) ^ ((twistExp chi m : ℤ) - (m : ℤ)) := by
  have hkey := I_pow_twistExp (chi := chi) (m := m) h4
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hz : (Complex.I : ℂ) ^ m ≠ 0 := pow_ne_zero _ hI
  rw [zpow_sub₀ hI]
  simp only [zpow_natCast]
  rw [hkey]
  exact (mul_div_cancel_right₀ _ hz).symm

/-! ## 4. The four summands -/

/-- The abstract computation underlying all four terms: with `c = i^{j-m}`,
`c^k·(i^k)^{-j}·(i^k)^m = i^{k(j-m)}·i^{-kj}·i^{km} = 1`. -/
lemma powI_aux (k j m : ℕ) :
    (Complex.I : ℂ) ^ (((j:ℤ)-(m:ℤ)) * (k:ℤ)) * ((Complex.I : ℂ) ^ (k:ℤ)) ^ ((m:ℤ)-(j:ℤ))
      = 1 := by
  rw [← zpow_mul, ← zpow_add₀ Complex.I_ne_zero]
  rw [show ((j:ℤ)-(m:ℤ)) * (k:ℤ) + (k:ℤ) * ((m:ℤ)-(j:ℤ)) = 0 from by ring, zpow_zero]

/-- **Each of the four summands of `unitSum (twist χ m) m` equals `1`**: for the unit `i^k`,
`twist χ m (i^k)·(i^k)^m = χ(i^k)·(i^k)^{-j}·(i^k)^m = (χ(i)i^m i^{-j})^k = 1`. -/
lemma term_k {d : ℕ} {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    (m k : ℕ) (hk : k < 4) :
    twist chi m ((⟨0,1⟩ : GaussianInt) ^ k) *
      (GaussianInt.toComplex ((⟨0,1⟩ : GaussianInt) ^ k)) ^ m = 1 := by
  have h4 : chi (⟨0,1⟩ : GaussianInt) ^ 4 = 1 := chi_I_pow4 hchi
  have hc := chi_I_eq_zpow (chi := chi) (m := m) h4
  have hpu := primaryUnit_pow_I hk
  have his := isOddG_pow_I hk
  have hkI : (GaussianInt.toComplex ((⟨0,1⟩ : GaussianInt) ^ k)) = (Complex.I : ℂ) ^ k := by
    rw [map_pow]; simp [GaussianInt.toComplex]
  have hchiIk : chi ((⟨0,1⟩ : GaussianInt) ^ k) = (chi ⟨0,1⟩) ^ k := chi_pow hchi _ k
  have htw : twist chi m ((⟨0,1⟩ : GaussianInt) ^ k) =
      chi ((⟨0,1⟩ : GaussianInt) ^ k) *
        (GaussianInt.toComplex ((⟨0,1⟩ : GaussianInt) ^ k)) ^ (-(twistExp chi m : ℤ)) := by
    simp only [twist, twistChar, if_pos his, hpu]
  rw [htw, hchiIk, hkI]
  have h1 : (chi ⟨0,1⟩) ^ k = (Complex.I : ℂ) ^ (((twistExp chi m : ℤ)-(m:ℤ)) * (k:ℤ)) := by
    rw [hc, ← zpow_natCast, ← zpow_mul]
  have h2 : ((Complex.I : ℂ) ^ k) ^ (-(twistExp chi m : ℤ)) * ((Complex.I : ℂ) ^ k) ^ m =
      ((Complex.I : ℂ) ^ (k:ℤ)) ^ ((m:ℤ) - (twistExp chi m : ℤ)) := by
    rw [← zpow_natCast ((Complex.I : ℂ) ^ k) m]
    rw [← zpow_add₀ (pow_ne_zero k Complex.I_ne_zero)]
    rw [show -(twistExp chi m : ℤ) + (m:ℤ) = (m:ℤ) - (twistExp chi m : ℤ) from by ring,
      zpow_natCast]
  rw [mul_assoc, h2, h1]
  exact powI_aux k (twistExp chi m) m

/-! ## 5. The unit sum -/

/-- **The twisted unit sum is `4`.**  `μ₄ = {i^k : k < 4}`, each summand of
`unitSum (twist χ m) m = Σ_{u ∈ μ₄} twist χ m u · u^m` is `1` (`term_k`), whence the sum is `4`. -/
theorem twist_unitSum (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : Work.FITop3.IsCharMod4d d chi) : unitSum (twist chi m) m = 4 := by
  have _ : 1 ≤ d := hd
  have hset : units4 =
      ({(⟨0,1⟩:GaussianInt)^0, (⟨0,1⟩:GaussianInt)^2, (⟨0,1⟩:GaussianInt)^1,
        (⟨0,1⟩:GaussianInt)^3} : Finset GaussianInt) := by
    simp only [pow_zero, one_mul, pow_I_two, pow_I_three]
    decide
  rw [unitSum, hset]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [term_k hchi m 0 (by norm_num), term_k hchi m 2 (by norm_num),
      term_k hchi m 1 (by norm_num), term_k hchi m 3 (by norm_num)]
  norm_num

end

end Work.FIArea5.S16Hecke
